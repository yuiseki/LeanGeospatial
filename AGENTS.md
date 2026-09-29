# AGENTS.md

Welcome to the mathematical universe of geospatial geometry and geodesy.

It lives in two repositories:
[LeanGeodesy](https://github.com/yuiseki/LeanGeodesy) carries the curved
Earth down to a flat map, and
[LeanGeospatial](https://github.com/yuiseki/LeanGeospatial) reasons about
what lies on that map. They stand on one plane, one foundation and one
version of Mathlib, and neither half explains the whole. A projection's
meaning is in what can be drawn and related on the plane it lands in; a
spatial relation's meaning is in the Earth whose features it relates. To
understand the mathematical structure, always read the other repository as
well: its definitions, its theorems and its AGENTS.md. Before you change the
plane, the toolchain or Mathlib here, check what that change does there.

Guidance for coding agents (and people) working on LeanGeospatial.

LeanGeospatial machine-checks reasoning about spatial relations in Lean 4
with Mathlib: regions and their topology, regular closed areas, RCC8 and its
composition table, DE-9IM patterns and matrices, Simple Features and
GeoSPARQL, a validator and a JSON Lines prover. It is one of two sibling
libraries; read [The sibling library](#the-sibling-library) before changing
anything about the plane, the toolchain or Mathlib.

## The sibling library

LeanGeodesy (<https://github.com/yuiseki/LeanGeodesy>) and LeanGeospatial
(<https://github.com/yuiseki/LeanGeospatial>) are two halves of one account
of GIS mathematics. LeanGeodesy starts from the Earth and ends on a flat map:
reference ellipsoids, geodetic coordinates, the first fundamental form, map
projections and their distortion. LeanGeospatial starts on the flat map:
regions, topology, RCC8, DE-9IM and the relations GIS software tests between
features. Neither depends on the other, but they are built to be used
together, and keeping that true is part of every change in either
repository.

What joins them:

- One plane. LeanGeodesy's `Geodesy.E2` and LeanGeospatial's
  `Geospatial.Point2D` are both reducible abbreviations of Mathlib's
  `EuclideanSpace ℝ (Fin 2)`, so `Geodesy.E2 = Geospatial.Point2D` holds by
  `rfl`. A point a LeanGeodesy projection produces is, with no conversion, a
  point of a LeanGeospatial region, and LeanGeospatial's `distance` is
  Mathlib's `dist` on that plane. Do not introduce a second plane type, a
  wrapper structure or a coercion in either library. If a definition needs
  coordinates, read them from the Mathlib type (`p 0`, `p 1`, or
  `Geospatial.Point2D.x`), and state results about the Mathlib type.
- One foundation. Both build only on Mathlib and Lean's three standard axioms
  (`propext`, `Classical.choice`, `Quot.sound`), and each has an axiom audit
  that fails the build if that changes.
- One version. Both pin the same Lean toolchain and the same Mathlib
  revision (currently Lean `v4.34.0`, Mathlib `v4.34.0`). Upgrade them
  together: a project that requires both libraries resolves a single Mathlib,
  so if the pins drift apart the two can no longer be imported together.
- One topology. LeanGeospatial's relations are defined from Mathlib's
  `interior`, `closure` and `frontier`, and `LeanGeospatial/Homeomorph.lean`
  proves that every homeomorphism of the plane preserves touching, the eight
  RCC8 relations and the DE-9IM matrix. Topological relations between areas
  do not depend on how the plane is moved, stretched or bent. On the other
  side, `LeanGeodesy/Projection/Homeomorph.lean` constructs projections as
  homeomorphisms on the domains where they are ones: Mercator from the open
  latitudes onto the whole plane (`mercatorHomeomorph`), and Web Mercator
  from the globe cut along the antimeridian onto the square
  (`webMercatorHomeomorph`; without the cut it is discontinuous). Composing
  two such maps gives a homeomorphism of the plane, and LeanGeospatial's
  theorems then say the two maps agree on every topological relation.

Checking the link. `scripts/joint_check.sh`, identical in both repositories,
builds a throwaway project that requires both libraries by path. It fails if
the two pin different toolchains or Mathlib revisions, or if these no longer
hold:

```lean
example : Geodesy.E2 = Geospatial.Point2D := rfl
example (R φ lam : ℝ) (A : Geospatial.Region) : Prop :=
  Geodesy.Projection.mercator R φ lam ∈ A
example (p q : Geodesy.E2) : Geospatial.distance p q = dist p q := rfl
```

and it checks that LeanGeospatial's `RCC8.Relation.holds_map_iff` applies to
the transition between two Mercator maps built by LeanGeodesy.

It also feeds Lean a deliberately false line and fails if that is accepted,
so a check that silently stopped running cannot pass. CI runs it in the
`joint` job of both repositories, against the sibling's branch of the same
name if there is one and its `main` otherwise. To change both libraries in
step (a Mathlib upgrade, say), push the same branch name to both, and merge
both once both are green. Locally, from either repository, with the two
checked out side by side:

```
scripts/joint_check.sh ../LeanGeodesy ../LeanGeospatial /tmp/joint
```

One known rough edge: `p.x` dot notation does not work on a term whose type
is written `Geodesy.E2`: Lean unfolds `E2` to Mathlib's `WithLp` and looks
for `WithLp.x`. Write `Geospatial.Point2D.x p`, or give the term the type
`Geospatial.Point2D`.

## Build and check

```
lake exe cache get
lake build
```

`lake build` must finish with no errors and no warnings. It builds the
examples too, and `LeanGeospatial/Examples/Axioms.lean` pins the main
theorems to the three standard axioms with `#guard_msgs`, so an added
`axiom` or an unfinished proof fails the build. When you add a main theorem,
add it to the audit.

CI (`.github/workflows/lean_action_ci.yml`) additionally checks, and you can
run the same commands locally:

- no `sorry` or `admit` under `LeanGeospatial/`;
- the library never imports `Examples` (only files under
  `LeanGeospatial/Examples/` may);
- `python3 scripts/gen_rcc8_table.py` leaves the generated composition-table
  files unchanged;
- the validator and the prover reproduce `samples/expected.out`,
  `samples/prover.expected.jsonl` and `samples/prover-contract.expected.jsonl`
  exactly, one answer per non-blank input line;
- `python3 scripts/prover_stream_test.py --lines 20000 --stack-kb 256`: the
  prover streams in constant stack.

If a change alters the expected outputs, regenerate them, read the diff, and
say in the commit why the answers changed.

A full build of Mathlib-dependent Lean uses a lot of memory. On a small
machine, set `LEAN_NUM_THREADS` low.

## Scope

LeanGeospatial checks reasoning; it does not compute geometry. Do not add
geometry computation, WKT parsing or a SPARQL engine. Facts computed by
GEOS, JTS, PostGIS or a GeoSPARQL endpoint enter as hypotheses. The
validator's text input and the prover's JSON Lines are the only places where
data comes in.

## Layout

- `LeanGeospatial/Point.lean`: the plane `Point2D`, shared with LeanGeodesy.
- `Region.lean`, `Topology.lean`, `RegularClosed.lean`: regions, interior,
  boundary, `Touches`, and the type of areas.
- `NineIntersection.lean`, `DE9IM*.lean`, `RCC8*.lean`, `Composition*.lean`:
  the relations.
- `Homeomorph.lean`: homeomorphisms preserve all of them.
- `GeoSPARQL/`, `SFA/`: the standards, transcribed and compared.
- `Validator*.lean`, `Prover/`, `ProverJSON.lean`, `Main.lean`,
  `ProverMain.lean`: the two executables.
- `LeanGeospatial/Examples/`: worked examples and the axiom audit.
- `README.md` is the reference; keep its theorem index and file table in
  step with the code.

## Conventions

- Commit messages, identifiers and docstrings are in English.
- Relations are defined once, from sets and Mathlib's topology. Cell
  conditions, patterns and tables are theorems about those definitions, not
  second definitions.
