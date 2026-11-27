#!/usr/bin/env bash
# Check that LeanGeodesy, LeanGeospatial and LeanComputationalGeometry can be
# imported together and still share one plane.
#
#   scripts/joint_check.sh PATH/TO/LeanGeodesy PATH/TO/LeanGeospatial \
#     PATH/TO/LeanComputationalGeometry [WORKDIR]
#
# It fails if the three pin different Lean toolchains or Mathlib revisions, if
# the joint project does not build, or if a deliberately false line is not
# rejected (which would mean the check itself is not running).
set -euo pipefail

geodesy=$(cd "$1" && pwd)
geospatial=$(cd "$2" && pwd)
compgeom=$(cd "$3" && pwd)
work=${4:-$(mktemp -d)}
mkdir -p "$work"
work=$(cd "$work" && pwd)

mathlib_rev() {
  python3 -c 'import json,sys; m=json.load(open(sys.argv[1])); print(next(p["rev"] for p in m["packages"] if p["name"]=="mathlib"))' "$1/lake-manifest.json"
}

toolchain=$(cat "$geospatial/lean-toolchain")
rev=$(mathlib_rev "$geospatial")
for lib in "$geodesy" "$compgeom"; do
  if [ "$toolchain" != "$(cat "$lib/lean-toolchain")" ]; then
    echo "lean-toolchain differs: $geospatial has $toolchain, $lib has $(cat "$lib/lean-toolchain")" >&2
    exit 1
  fi
  if [ "$rev" != "$(mathlib_rev "$lib")" ]; then
    echo "Mathlib revision differs: $geospatial has $rev, $lib has $(mathlib_rev "$lib")" >&2
    exit 1
  fi
done
echo "All three pin $toolchain and Mathlib $rev"

cd "$work"
echo "$toolchain" > lean-toolchain
cat > lakefile.toml <<TOML
name = "joint"
defaultTargets = ["Joint"]

[[lean_lib]]
name = "Joint"

[[require]]
name = "lean-geodesy"
path = "$geodesy"

[[require]]
name = "lean-geospatial"
path = "$geospatial"

[[require]]
name = "lean-computational-geometry"
path = "$compgeom"
TOML

cat > Joint.lean <<'LEAN'
import LeanGeodesy
import LeanGeospatial
import LeanComputationalGeometry

/-! The three libraries' planes are one type, Mathlib's Euclidean plane. -/

example : Geospatial.Point2D = Geodesy.E2 := rfl
example : Geospatial.Point2D = ComputationalGeometry.Point2D := rfl
example : Geodesy.E2 = ComputationalGeometry.Point2D := rfl

/-- A point a LeanGeodesy projection draws is a point of a LeanGeospatial
region, with no conversion. -/
example (R φ lam : ℝ) (A : Geospatial.Region) : Prop :=
  Geodesy.Projection.mercator R φ lam ∈ A

/-- LeanGeospatial's distance is Mathlib's distance on that plane. -/
example (p q : Geodesy.E2) : Geospatial.distance p q = dist p q := rfl

/-- Points that LeanGeodesy's Mercator projection draws feed
LeanComputationalGeometry's orientation test directly. -/
example (R φ₁ l₁ φ₂ l₂ φ₃ l₃ : ℝ) :
    ComputationalGeometry.orient (Geodesy.Projection.mercator R φ₂ l₂)
        (Geodesy.Projection.mercator R φ₁ l₁) (Geodesy.Projection.mercator R φ₃ l₃) =
      -ComputationalGeometry.orient (Geodesy.Projection.mercator R φ₁ l₁)
        (Geodesy.Projection.mercator R φ₂ l₂) (Geodesy.Projection.mercator R φ₃ l₃) :=
  ComputationalGeometry.orient_swap₁₂ _ _ _

/-- A segment of LeanComputationalGeometry is a LeanGeospatial region. -/
example (s : ComputationalGeometry.Segment) : Geospatial.Region := s.toSet

/-- Two Mercator maps of one globe at different scales differ by a
homeomorphism of the plane, so they agree on every RCC8 relation between the
areas drawn on them. -/
example (R₁ R₂ : ℝ) (h₁ : R₁ ≠ 0) (h₂ : R₂ ≠ 0)
    (A B : Geospatial.RegularClosedRegion Geospatial.Point2D)
    (r : Geospatial.RCC8.Relation) :
    let e := (Geodesy.Projection.mercatorHomeomorph R₁ h₁).symm.trans
      (Geodesy.Projection.mercatorHomeomorph R₂ h₂)
    r.holds (A.map e) (B.map e) ↔ r.holds A B :=
  Geospatial.RCC8.Relation.holds_map_iff _ A B r

/-- On the globe itself: the RCC8 relation between two areas of the Web
Mercator chart (latitude and longitude, cut along the antimeridian) is the
relation between their images on the map. -/
example (A B : Geospatial.RegularClosedRegion Geodesy.Projection.webMercatorChart)
    (r : Geospatial.RCC8.Relation) :
    r.holds (A.map Geodesy.Projection.webMercatorHomeomorph)
      (B.map Geodesy.Projection.webMercatorHomeomorph) ↔ r.holds A B :=
  Geospatial.RCC8.Relation.holds_map_iff _ A B r
LEAN

cat > False.lean <<'LEAN'
import LeanGeodesy
import LeanGeospatial
import LeanComputationalGeometry

example : (1 : ℕ) = 2 := rfl
LEAN

lake update
lake exe cache get
lake build

if lake env lean False.lean > /dev/null 2>&1; then
  echo "A false statement was accepted: the joint check is not running" >&2
  exit 1
fi
echo "LeanGeodesy, LeanGeospatial and LeanComputationalGeometry share one plane"
