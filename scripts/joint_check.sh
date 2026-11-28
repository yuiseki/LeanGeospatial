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
#
# The joint project is the library in LeanGeodesy's `joint/` directory
# (`Joint.lean` and `Joint/*.lean`): the theorems that join the three
# libraries (one plane, one space, one unit sphere, the projections, the
# metric and topological correspondences, and a worked cross-library proof),
# with its own axiom audit (`Joint/Axioms.lean`). None of the three libraries
# imports another; only this throwaway project imports all three.
#
# This script is identical in the three repositories.
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

toolchain=$(cat "$geodesy/lean-toolchain")
rev=$(mathlib_rev "$geodesy")
for lib in "$geospatial" "$compgeom"; do
  if [ "$toolchain" != "$(cat "$lib/lean-toolchain")" ]; then
    echo "lean-toolchain differs: $geodesy has $toolchain, $lib has $(cat "$lib/lean-toolchain")" >&2
    exit 1
  fi
  if [ "$rev" != "$(mathlib_rev "$lib")" ]; then
    echo "Mathlib revision differs: $geodesy has $rev, $lib has $(mathlib_rev "$lib")" >&2
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
globs = ["Joint", "Joint.*"]

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

rm -rf Joint Joint.lean
cp -R "$geodesy/joint/Joint" Joint
cp "$geodesy/joint/Joint.lean" Joint.lean

cat > False.lean <<'LEAN'
import LeanGeodesy
import LeanGeospatial
import LeanComputationalGeometry

example : (1 : ℕ) = 2 := rfl
LEAN

lake update
lake exe cache get
lake build ${LAKE_BUILD_ARGS:-}

if lake env lean False.lean > /dev/null 2>&1; then
  echo "A false statement was accepted: the joint check is not running" >&2
  exit 1
fi
echo "LeanGeodesy, LeanGeospatial and LeanComputationalGeometry share one plane, one space and one sphere"
