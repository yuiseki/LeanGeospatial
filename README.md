# LeanGeospatial

LeanGeospatial is a small formal system in Lean 4 for machine-checking claims
about spatial relations. Machine-checked means that every conclusion it
reports rests on a proof the Lean compiler has verified, not on tests alone.

It is not a GIS engine written in Lean. It does not read geometry or compute
intersections. A GIS computes geometry; LeanGeospatial checks the reasoning
from the result. Given spatial facts or a DE-9IM matrix computed by GEOS,
JTS, PostGIS, a GeoSPARQL endpoint or any other tool, it verifies that a
conclusion follows logically from those premises.

The main entry point is `lean-geospatial-prover`, a command that reads
requests as JSON Lines on stdin and writes one JSON answer per line on
stdout.

## What can I do with it?

### 1. Check a Simple Features claim from DE-9IM

Give the prover a DE-9IM matrix, as GEOS or JTS print it, and one of the
eight Simple Features relations: `equals`, `disjoint`, `intersects`,
`touches`, `within`, `contains`, `overlaps`, `crosses`.

```json
{"id":"wards","matrix":"FF2F11212","claim":"touches"}
{"status":"entailed","id":"wards","claim":"touches"}
```

`entailed` means the relation holds for any geometries with that matrix;
`refuted` means it holds for none. `overlaps` and `crosses` depend on the
dimensions of the geometries, so they also need `a_kind` and `b_kind`
(`point`, `line` or `area`):

```json
{"id":"lines","matrix":"0F1FF0102","claim":"crosses","a_kind":"line","b_kind":"line"}
{"status":"entailed","id":"lines","claim":"crosses"}
```

### 2. Infer RCC8 relations from known facts

Give the prover facts between named features, in the eight RCC8 relations
(`DC EC PO EQ TPP NTPP TPPi NTPPi`), and ask about a pair. A district strictly
inside a city, and the city strictly inside a province:

```json
{"id":"nested","facts":[{"a":"DistrictA","relation":"NTPP","b":"CityB"},{"a":"CityB","relation":"NTPP","b":"ProvinceC"}],"query":{"a":"DistrictA","b":"ProvinceC"}}
{"status":"entailed","relation":"NTPP","id":"nested"}
```

The answer is one of:

- `entailed`: the facts force this one relation;
- `possible`: the facts leave several relations, listed in `relations`;
- `contradictory`: the facts cannot all be true.

## Quick start

You need [elan](https://github.com/leanprover/elan), the Lean toolchain
manager; it installs the Lean version in `lean-toolchain`.

```bash
git clone https://github.com/yuiseki/LeanGeospatial.git
cd LeanGeospatial
lake exe cache get      # download prebuilt Mathlib
lake build              # checks every proof, builds the commands
lake exe lean-geospatial-prover < samples/prover.jsonl
```

To try your own request:

```bash
echo '{"id":"x","matrix":"FF2F11212","claim":"within"}' | lake exe lean-geospatial-prover
```

```json
{"status":"refuted","id":"x","claim":"within"}
```

The full input and output format is in
[Prover JSON Lines contract](#13-prover-json-lines-contract).

## What is actually proved?

Everything below is a theorem checked by `lake build`. The repository has no
unfinished proofs (`sorry`, `admit`) and no axioms of its own.

### DE-9IM / Simple Features

The eight relations are defined from point sets: the geometries' points,
their interiors, boundaries and exteriors as Simple Features defines them,
and the dimensions of intersections. They are not defined by DE-9IM
patterns.

The prover's answer comes from `Claim.decide`, and `Claim.decide_iff` proves
it exact: for any points, lines or areas whose DE-9IM matrix is the given
one (and whose kinds are the given ones, for `overlaps` and `crosses`),
`decide` says `entailed` exactly when the relation holds between them.

### RCC8

The eight RCC8 relations are defined for areas from sets and topology, and
Lean proves that exactly one of them holds between any two nonempty areas.

The RCC8 composition table, which says what `A r B` and `B s C` allow
between `A` and `C`, is derived in Lean from those definitions. No published
table is assumed; the derived table is compared with the published one
afterwards, and agrees on all 64 cells.

The verdicts have soundness theorems. Call an assignment of nonempty areas
to the features that makes every fact true a model. Then:

- `entailed r`: every model has `r` between the queried features;
- `possible S`: every model has one of `S`;
- `contradictory`: there is no model.

## Trust boundary

LeanGeospatial does not compute or check geometry.

```text
geometry
  ↓  GEOS / JTS / PostGIS / GeoSPARQL endpoint     (not checked by Lean)
spatial facts / DE-9IM matrix
  ↓  LeanGeospatial                                (checked by Lean)
conclusion that follows from those facts
```

- Whether a DE-9IM matrix is correct for real geometries is outside what
  LeanGeospatial proves.
- Whether RCC8 facts describe real features correctly is outside what it
  proves.
- JSON parsing and serialisation (`LeanGeospatial/ProverJSON.lean`) are
  unproved glue code. They only turn a request into the `Graph` of facts or
  the `Matrix9` handed to the proved functions, and the answer back into
  JSON.
- What Lean guarantees is that the verdict follows logically from the
  premises as given. If a premise is false, the conclusion is unsupported,
  and Lean cannot notice.

## Why this repository exists

- To state the semantics of spatial standards precisely enough to be
  machine-checked: relations defined from point sets and topology, with the
  standards' DE-9IM patterns proved equivalent to them, or shown not to be.
- To check specifications against themselves. Doing so found places where
  OGC Simple Feature Access and GeoSPARQL 1.1 disagree with their own
  point-set definitions or with each other
  ([GeoSPARQL](#10-geosparql-11-verification), [SFA](#11-ogc-simple-feature-access-121-comparison)).
- To put a proof layer after a GIS engine: the engine computes, and the
  prover checks what the output entails.

## Details

The sections below are for readers who want the mathematics, the standards
comparison, and the implementation.

1. [Mathematical model](#1-mathematical-model)
2. [Regions and topology](#2-regions-and-topology)
3. [Regular closed areas](#3-regular-closed-areas)
4. [Nine intersections and DE-9IM patterns](#4-nine-intersections-and-de-9im-patterns)
5. [Points, lines and areas](#5-points-lines-and-areas)
6. [Simple Features](#6-simple-features)
7. [RCC8](#7-rcc8)
8. [Weak composition](#8-weak-composition)
9. [RCC8 composition table](#9-rcc8-composition-table)
10. [GeoSPARQL 1.1 verification](#10-geosparql-11-verification)
11. [OGC Simple Feature Access 1.2.1 comparison](#11-ogc-simple-feature-access-121-comparison)
12. [Validator](#12-validator)
13. [Prover JSON Lines contract](#13-prover-json-lines-contract)
14. [Known limitations](#14-known-limitations)
15. [What Lean proves](#15-what-lean-proves)
16. [Axiom and proof audit](#16-axiom-and-proof-audit)
17. [Repository layout](#17-repository-layout)
18. [Build and development](#18-build-and-development)

### 1. Mathematical model

Points are pairs of real numbers in a flat plane. A `Region` is a set of
points, `Set Point2D`. A `Polygon` is only data, a list of vertices, and is
kept separate from `Region`; the one shape with a defined region is `Rect`,
an axis-aligned rectangle. The basic relations are defined by set
operations, not postulated:

| Relation | Definition |
| --- | --- |
| `Within A B` | `A ⊆ B` |
| `Contains A B` | `B ⊆ A` |
| `Intersects A B` | `(A ∩ B).Nonempty` |
| `Disjoint A B` | `A ∩ B = ∅` |

These four relations ignore boundaries. Two regions that only share an edge
`Intersect`, and are not `Disjoint`. (The Simple Features `Within` of
section 6 is stricter.)

External facts enter as hypotheses. Lean does not know where District A is.
In `Examples/Administrative.lean` the facts

```lean
(hDistrictCity : Within DistrictA CityB)
(hCityProvince : Within CityB ProvinceC)
```

are hypotheses. They stand for claims from outside Lean: a boundary file, a
gazetteer, an official statement. Lean checks only that
`Within DistrictA ProvinceC` follows from them, which it does by the general
`within_trans`. If a hypothesis is false in the real world, the conclusion is
unsupported, and Lean cannot notice that.

With concrete coordinates Lean also proves numeric facts, for example that the
distance from `(0,0)` to `(10,10)` is `10 * √2` and that the 10 × 10 square has
shoelace area `100`.

### 2. Regions and topology

`Point2D` carries the topology it inherits from `ℝ × ℝ` through its
coordinates, which is the usual Euclidean topology of the plane.
`Point2D.homeomorphProd : Point2D ≃ₜ ℝ × ℝ` records this, so Mathlib's lemmas
about products and intervals apply directly. The topological vocabulary is
Mathlib's, not new definitions:

| Name | Meaning |
| --- | --- |
| `interior A` | Mathlib's `interior` |
| `closure A` | Mathlib's `closure` |
| `boundary A` | Mathlib's `frontier`, which is `closure A \ interior A` |
| `Touches A B` | `Intersects A B ∧ Disjoint (interior A) (interior B)` |

`Touches` is the point-set definition: the regions share a point but no
interior point. It separates "shares an edge" from "overlaps", which
`Intersects` alone cannot. The plane is connected (`Connected.lean`), so an
area other than the whole plane has a nonempty boundary and exterior.

### 3. Regular closed areas

`Region` is any set of points, including a single point, a line, or a square
with a stray line attached. A geographic area (a district, a parcel, a lake)
should be none of those. The type

```lean
structure RegularClosedRegion where
  carrier : Region
  closure_interior_eq' : closure (interior carrier) = carrier
```

holds exactly the regions that are the closure of their own interior. Every
value carries that proof, so theorems about areas do not ask for it again.
`RegularClosedRegion` is a `SetLike`, so an area can be used wherever a
`Region` is expected, but not the other way round. Areas may have several
parts and holes, and may be unbounded; the whole plane is one.

### 4. Nine intersections and DE-9IM patterns

`exterior A` is `interior Aᶜ`, which equals `(closure A)ᶜ`. Interior, boundary
and exterior split the plane: every point is in exactly one of them
(`existsUnique_stratum`). For two regions this gives nine cells,

```lean
cell s t A B = s.set A ∩ t.set B      -- s, t ∈ {I, B, E}
```

abbreviated `II`, `IB`, `IE`, `BI`, `BB`, `BE`, `EI`, `EB`, `EE`, with the
first letter for `A`.

The relations are still defined by the set operations above. The cell
conditions are theorems derived from those definitions, not a second set of
definitions. For areas `A`, `B`:

| Relation | Cell condition | Theorem |
| --- | --- | --- |
| `Disjoint A B` | `II`, `IB`, `BI`, `BB` all empty | `RegularClosedRegion.disjoint_iff_cells` |
| `Intersects A B` | one of `II`, `IB`, `BI`, `BB` nonempty | `RegularClosedRegion.intersects_iff_cells` |
| `Touches A B` | `II` empty, one of `IB`, `BI`, `BB` nonempty | `RegularClosedRegion.touches_iff_cells` |
| `Within A B`, `A` nonempty | `II` nonempty, `IE` and `BE` empty | `RegularClosedRegion.within_iff_cells` |
| `Contains A B`, `B` nonempty | `II` nonempty, `EI` and `EB` empty | `RegularClosedRegion.contains_iff_cells` |

The first three already hold for any closed regions (`..._of_isClosed`). The
`Within` row needs more, and `Examples/NineIntersection.lean` proves each
hypothesis is needed:

- The empty area lies within every area, but `II` is empty.
- A segment on the edge of a square is closed, nonempty and within the
  square, but its interior is empty, so `II` is empty. It is not an area.

Without the `II` condition, `Within` on closed regions is exactly
`IE` and `BE` empty (`within_iff_cells_of_isClosed`).

`DE9IM.lean` gives patterns a meaning from the nine cells: `T` nonempty, `F`
empty, `*` anything. A pattern is a record with one field per cell;
`Pattern.ofString?` reads the 9-character notation and rejects anything
else. Patterns with dimensions (`0`, `1`, `2`) are in section 5.

### 5. Points, lines and areas

Mathlib's `interior` and `frontier` are right for areas but not for points
and lines: in the plane a point has empty interior and is its own frontier
(`point_frontier`). `Geometry.lean` gives each geometry the strata Simple
Features uses:

| Geometry | Interior | Boundary | Exterior |
| --- | --- | --- | --- |
| Point `p` | `{p}` | `∅` | everything else |
| LineString | the line minus its boundary | its two end points, `∅` if closed | everything off the line |
| Area | topological interior | topological boundary | topological exterior |

`Geometry.existsUnique_stratum`: for every geometry, each point of the plane
is in exactly one stratum. For areas the strata are the ones of sections 2
to 4, so the Area/Area results carry over (`Geometry.cell_area_area`,
`Pattern.toDim_matches_area`). Multi geometries are not covered.

`DE9IM/Dimension.lean` gives a cell one of the values `F`, `0`, `1`, `2`,
without a dimension theory for arbitrary sets: `2` if the cell contains an
open set, `1` if it contains an arc but no open set, `0` if it is nonempty
with neither, `F` if it is empty. For the finite unions of points, arcs and
regions that occur as cells of these geometries, that is their dimension.
Every cell has exactly one value (`existsUnique_describes`). Patterns may use
`T F * 0 1 2`. `Examples/DimensionalCells.lean` shows one `II` cell of each
value, including two segments crossing in a point (`0`) and two collinear
segments overlapping in a segment (`1`).

`DE9IM/Values.lean` checks the cell values are sensible: a cell through a
point's interior or boundary is `F` or `0`; through a line's interior or
boundary it is never `2`; two areas' interiors meet in `F` or `2`; and two
lines' interiors meet in `1` exactly when the intersection contains an arc,
in `0` when it is nonempty without one.

### 6. Simple Features

`SimpleFeatures.lean` defines the eight relations from point sets, strata
and interior dimensions, following the Simple Features point-set
definitions, with no DE-9IM pattern.

The prover reads a claim off a stated matrix (`Prover/DE9IMClaim.lean`):

- disjoint, intersects, touches, within, contains are read from the pattern
  rows that the Table 2 theorems of section 10 prove equivalent to them;
- equals is read from `T*F**FFF*`, or `FFFFFFFF*` when both geometries are
  empty, not from Table 2's `TFFFTFFFT` (see section 11). Whether a geometry
  is empty can be read off the matrix: its points are the six cells of its
  interior and boundary rows;
- overlaps and crosses follow the SFA definitions. They need the kinds,
  which give each interior's dimension. The other claims ignore the kinds
  (`Claim.decide_kinds_irrel`).

`Claim.decide_iff` proves the answer exact for all eight, and
`Examples/Prover.lean` spells out what particular answers mean, for example
that any two geometries with the matrix `FF2F11212` touch and are not
within one another.

### 7. RCC8

The eight base relations of the Region Connection Calculus, for areas, are
defined from the relations above (`a`, `b` are the point sets of `A`, `B`):

| Relation | Definition |
| --- | --- |
| `DC A B` | `Disjoint a b` |
| `EC A B` | `Touches a b` |
| `PO A B` | the interiors intersect, `¬ Within a b`, `¬ Within b a` |
| `EQ A B` | `a = b` |
| `TPP A B` | `Within a b`, `a ≠ b`, `¬ Within a (interior b)` |
| `NTPP A B` | `Within a (interior b)`, `a ≠ b` |
| `TPPi A B`, `NTPPi A B` | `TPP B A`, `NTPP B A` |

`NTPP` includes `a ≠ b` because the whole plane is an area that lies within
its own interior; without it the plane would be both `EQ` and `NTPP` with
itself.

### 8. Weak composition

```lean
r ⋄ s = {t | ∃ A B C nonempty areas, r A B ∧ s B C ∧ t A C}
```

This is the meaning of an entry in the RCC8 composition table. No table is
assumed: each entry has to be proved from the definitions, in both
directions. Showing `t ∈ r ⋄ s` needs three concrete areas; showing
`t ∉ r ⋄ s` needs an argument that works for all areas.

### 9. RCC8 composition table

All 64 cells are theorems, `compose_dc_dc` through `compose_ntppi_ntppi` in
`CompositionTable/Cells.lean`, for example

```lean
theorem compose_ec_ntpp : Relation.ec ⋄ Relation.ntpp = ↑({.po, .tpp, .ntpp} : Finset Relation)
```

They all come from `compose_eq_table : r ⋄ s = ↑(table r s)`, proved in two
halves.

- Exclusion, `r ⋄ s ⊆ table r s`, is one argument for every cell. Each
  relation fixes six facts about a pair of areas (meet, interiors meet, within
  either way, within the other's interior either way). Nine laws connect the
  facts of the three pairs of a triangle, for example "X ⊆ Y ⊆ int Z gives
  X ⊆ int Z", each proved from the set and topology definitions. `table r s`
  keeps the `t` that some choice of facts allows under all nine laws in every
  orientation, and is computed by `decide`. Two of the laws use that areas are
  the closure of their interior; without them five cells would be looser
  (`EC ⋄ EC` would admit `NTPP` and `NTPPi`, and `EC ⋄ NTPP`, `EC ⋄ NTPPi`,
  `NTPP ⋄ EC`, `NTPPi ⋄ EC` would admit `EC`).
- Realisation, `table r s ⊆ r ⋄ s`, uses three rectangles per entry. Of the
  193 entries, the 15 in the `EQ` row and column follow from the identity
  laws, and the converse law pairs the rest, so 112 witnesses cover all
  entries. `rect_rcc8` checks each relation between rectangles by reducing it
  to coordinate inequalities.

`scripts/gen_rcc8_table.py` searches for the rectangles and writes the
generated files; `data/rcc8_witnesses.tsv` lists them one per line. The script
is not trusted: Lean checks every witness, and CI checks that the generated
files are up to date.

`Examples/PublishedTable.lean` compares the derived table with the one
published on Wikipedia (`data/rcc8_known_table.tsv`, revision 1366466711) and
proves they agree on all 64 cells. The published table is not used by any
proof in the library.

### 10. GeoSPARQL 1.1 verification

`GeoSPARQL/Spec.lean` and `GeoSPARQL/Table2/Spec.lean` transcribe Tables 2,
4, 5, 6 and 8 of OGC 22-047r1. They are data for comparison only; nothing in
LeanGeospatial is defined from them.

Table 8 (and Table 4), RCC8 patterns, for nonempty areas:

| Table 8 pattern | Pattern ⇒ relation | Relation ⇒ pattern |
| --- | --- | --- |
| `EQ` `TFFFTFFFT` | yes | yes, unless the area is the whole plane |
| `DC` `FFTFFTTTT` | yes | yes |
| `EC` `FFTFTTTTT` | yes | no: a square and a frame around it |
| `PO` `TTTTTTTTT` | yes | no: two two-part areas sharing a part |
| `TPP` `TFFTTFTTT` | yes | no: a square and the square plus another |
| `NTPP` `TFFTFFTTT` | yes | yes, unless the larger area is the whole plane |
| `TPPi` `TTTFTTFFT` | yes | no: as `TPP` |
| `NTPPi` `TTTFFTFFT` | yes | yes, unless the larger area is the whole plane |

The fully specified patterns fit bounded areas with a connected interior and
no holes; polygons with holes and multi-polygons break four of them. GEOS
gives the same matrices for the bounded counterexamples.

Table 5, Simple Features against RCC8, for nonempty areas:

| Table 5 row | Holds for nonempty areas |
| --- | --- |
| equals ↔ `EQ` | yes |
| disjoint ↔ `DC` | yes |
| intersects ↔ ¬`DC` | yes |
| touches ↔ `EC` | yes |
| within ↔ `TPP` ∨ `NTPP` | no, `EQ` is missing: `Within ↔ TPP ∨ NTPP ∨ EQ` |
| contains ↔ `TPPi` ∨ `NTPPi` | no, `EQ` is missing |
| overlaps ↔ `PO` | yes |

Table 2, Simple Features patterns, against the definitions of section 6, for
every combination of kinds Table 2 lists:

| Relation | Kinds | Table 2 pattern ⇔ definition |
| --- | --- | --- |
| equals | all | pattern ⇒ `Equals` always; converse fails for P/P (points have no boundary, so the pattern never matches), for closed rings, for lines that double back, and for the whole plane; holds across kinds and for areas other than the plane |
| disjoint | all | Table 2's entry `FF**FF****` is malformed; `FF*FF****` (Tables 3, 6) matches |
| intersects | all | matches |
| touches | all but P/P | matches |
| within | all | matches |
| contains | all | matches |
| overlaps | A/A, L/L | matches; L/L is `II = 1` |
| overlaps | P/P | neither can hold for single points |
| crosses | L/L | matches; `II = 0`. Table 6's `0*T***T**` also matches |
| crosses | L/A | matches |
| crosses | P/L, P/A | neither can hold for single points |

GEOS agrees on the equals counterexamples: it reports point-set equality for
them while the `TFFFTFFFT` pattern fails. Patterns that single geometries
cannot realise: `overlaps` P/P, `crosses` P/L and P/A (all need a
MultiPoint), and `equals` P/P.

Disagreements between the tables themselves, kept as printed:

- Table 2 prints `disjoint` as `(FF**FF****)`, ten characters; Tables 3 and 6
  have `FF*FF****`.
- Table 6 gives `geof:sfIntersects` the `sfTouches` rows; Table 2 gives
  `sfIntersects` `(T******** *T******* ***T***** ****T****)`. The Table 6 rows
  describe `EC`, not ¬`DC`.
- Table 5 has within = `NTPP` + `TPP`, but Table 2's `sfWithin` pattern
  `T*F**F***` also matches equal areas. The same holds for contains.

Tables 4 and 8 agree, and their `TPPi` and `NTPPi` patterns are the
transposes of `TPP` and `NTPP`. The Egenhofer column of Table 5 is not
checked.

### 11. OGC Simple Feature Access 1.2.1 comparison

`SFA/Spec.lean` transcribes clause 6.1.15 of OGC 06-103r4 (version 1.2.1).
For each named predicate SFA gives a statement about point sets and a DE-9IM
pattern, and claims they are equivalent. Both are transcribed separately.

The strata of `Geometry.lean` are SFA's (6.1.15.1): a point has no boundary,
a non-closed curve's boundary is its end points, a closed curve has none,
the interior is the geometry minus its boundary, the exterior is the rest.

LeanGeospatial's definitions against SFA's point-set statements, and SFA's
statements against SFA's own patterns:

| Relation | LeanGeospatial vs SFA statement | SFA statement vs SFA pattern |
| --- | --- | --- |
| Equals | same | disagree: a point equals itself, `TFFFTFFFT` fails (points have no boundary) |
| Disjoint | same | agree |
| Intersects | same | (no pattern) |
| Touches | same | agree |
| Within | LeanGeospatial also asks `I(a) ∩ I(b) ≠ ∅` | disagree: a point on a square's edge satisfies the statement, not `T*F**F***` |
| Contains | as Within | as Within |
| Overlaps | same | agree |
| Crosses | LeanGeospatial keeps the dimension condition SFA 1.2.1 dropped | disagree for L/L: collinear overlapping segments satisfy the statement, not `0********` |

So where LeanGeospatial differs from SFA's statements, it sides with SFA's
patterns, and SFA's statements and patterns contradict each other. GEOS sides
with the patterns in all three cases. SFA's `II ≠ ∅` in Crosses is needed:
without it, disjoint geometries would cross.

SFA's patterns against GeoSPARQL Table 2: the same strings for equals,
touches, within, overlaps and L/L crosses. GeoSPARQL differs in two places:
`disjoint` (ten characters instead of `FF*FF****`), and P/L, P/A, L/A crosses
(`T*T***T**` instead of `T*T******`, which agree for single geometries).

Equals: `T*F**FFF*`, the pattern JTS uses, is `a ⊆ b ∧ b ⊆ a ∧ II ≠ ∅` and
exactly `Equals` for nonempty geometries (`equals_iff_jtsEquals`).
`TFFFTFFFT` adds `IB = ∅`, `BI = ∅`, `BB ≠ ∅`, `EE ≠ ∅`
(`sfaEquals_iff_jtsEquals_and`); these fail for points, closed rings, lines
that double back and the whole plane.

### 12. Validator

`lean-geospatial` is an earlier, plain-text front end to the same RCC8
checker the prover uses (`Graph.check`).

```
$ lake exe lean-geospatial samples/*.txt
samples/inconsistent.txt: BuildingA → BlockC: contradictory
samples/nested.txt: DistrictA → ProvinceC: entailed NTPP
samples/touching.txt: ParcelA → ParcelC: possible {DC, EC, PO, EQ, TPP, TPPi}
```

An input file has one fact per line (`DistrictA NTPP CityB`), queries
(`? DistrictA ProvinceC`) and `#` comments.

For a pair `A`, `C`, the checker intersects two sets of relations: `table r s`
over every feature `B` with known `A r B` and `B s C` (using converses for
facts stated the other way), and the relations the facts stated between `A`
and `C` themselves allow. It then answers:

- entailed `t`: only `t` is left, so every model has `A t C`
  (`Graph.check_entailed`).
- possible `S`: several relations are left; every model has one of them
  (`Graph.check_possible`). For a single triangle each of them also occurs
  (`triangle_realizes`); with more features, other facts may rule out more.
- contradictory: nothing is left, or two different relations are stated for
  one pair anywhere in the graph, so no model exists
  (`Graph.check_contradictory`).

A model gives every feature a nonempty area making every fact true. The
three verdict theorems rest on the soundness half of the composition table
and on "exactly one relation holds". `Examples/Validator.lean` proves the
sample cases as theorems; CI also runs the command on `samples/` and
compares with `samples/expected.out`.

### 13. Prover JSON Lines contract

`lean-geospatial-prover` reads one JSON object per line on stdin, UTF-8, and
writes one JSON object per non-blank input line on stdout, in input order.
Blank lines are skipped. A line with a `matrix` key is a DE-9IM request, any
other line an RCC8 request. Unknown keys are ignored.

| Request | Fields |
| --- | --- |
| RCC8 | `id` (any JSON, optional), `facts` (array of `{"a": string, "relation": string, "b": string}`), `query` (`{"a": string, "b": string}`) |
| DE-9IM | `id` (optional), `matrix` (exactly 9 characters of `F 0 1 2`, as GEOS prints), `claim` (string), `a_kind` and `b_kind` (`point`, `line`, `area`; required for overlaps and crosses) |

RCC8 relation names: `DC EC PO EQ TPP NTPP TPPi NTPPi`, any letter case. DE-9IM
claims: `equals disjoint intersects touches within contains overlaps
crosses`, any letter case, with or without an `sf` prefix. Kinds also accept
`P L A`, `linestring` and `polygon`.

In the output, `id` is the request's `id`, or `null` if absent or if the line
is not valid JSON. Key order carries no meaning.

| `status` | Extra field | Meaning |
| --- | --- | --- |
| `entailed` | `relation` (RCC8) or `claim` (DE-9IM) | RCC8: every model of the facts has this relation between `a` and `b`. DE-9IM: every geometry pair with this matrix (and kinds) satisfies the claim |
| `possible` | `relations` (fixed order `DC EC PO EQ TPP NTPP TPPi NTPPi`) | every model has one of these; not a claim that each occurs |
| `contradictory` | | the facts have no model (found through one intermediate feature or between facts for one pair) |
| `refuted` | `claim` | DE-9IM: no geometry pair with this matrix (and kinds) satisfies the claim |
| `error` | `error` (message) | the line was not processed; nothing is claimed |

If the facts have no model, `entailed` and `possible` answers are vacuously
true; the checker does not always detect such facts (see section 14).

Every fact constrains its pair: facts stated between the queried pair
narrow the answer (a stated `A NTPP B` queried as `A`, `B` is `entailed
NTPP`), a fact stated the other way round counts as its converse, and two
different relations stated for one pair anywhere in the graph make every
query `contradictory`.

Malformed JSON, missing fields, unknown relations, matrices that are not 9
characters of `F 0 1 2`, unknown claims or kinds, overlaps or crosses without
kinds, and lines with both `facts` and `matrix` give `"status":"error"`.

Each line is answered on its own: a bad line gives an `error` line and the
next line is processed normally. The exit code is 0 whenever input was read
to the end, even if every line was an error; errors are only reported in the
output. Callers should match answers by `id` or by position among non-blank
lines.

The prover reads its input as a stream in constant stack, so one process can
take any number of lines.

Reproducibility: responses carry no version. To reproduce, pin the
LeanGeospatial commit, which fixes `lean-toolchain` (Lean) and
`lake-manifest.json` (Mathlib). `lakefile.toml`'s `version` is not updated
per change.

`samples/prover.jsonl` and `samples/prover-contract.jsonl` exercise this
contract in CI (section 18).

### 14. Known limitations

The RCC8 checker:

- It is not an RCC8 satisfiability solver. It finds contradictions only
  through the composition table along one intermediate feature and between
  facts stated for the same pair, so a graph with no model can still get
  `entailed` or `possible` (then vacuously true).
- `possible` is not always the tightest set: constraints over longer paths
  are not propagated.

The prover:

- Some error messages come from the JSON library and are terse
  (`String expected` for a missing `claim`).

Not verified, because it needs multi geometries:

- `overlaps` P/P and `crosses` P/L, P/A with MultiPoints;
- the mod-2 boundary rule of MultiLineStrings, which changes boundaries and
  so `equals`, `touches`, `within`, `overlaps`, `crosses` for lines;
- MultiPolygon validity rules (areas here may already have several parts,
  but are not checked against them);
- geometry collections of mixed dimension.

Not modelled:

- Which set of points a general polygon encloses. Only `Rect` has a region,
  and so only `Rect` has a computed interior and boundary.
- Whether a real place is an area. Building a `RegularClosedRegion` needs a
  proof of `closure (interior A) = A`, which Lean can give for a `Rect` but not
  for a boundary loaded from outside. For such data it is an assumption, made
  once when the value is built.
- Coordinate reference systems. Coordinates are plain real numbers in a flat
  plane, and `distance` is Euclidean, not a distance on the Earth.
- Reading real data, and GIS input and output.
- The Egenhofer relations.

### 15. What Lean proves

A theorem index, by topic. These hold for every region, whatever its shape or
source:

- `within_refl`, `within_trans`, `within_antisymm`
- `contains_iff_within : Contains A B ↔ Within B A`
- `intersects_symm`, `disjoint_symm`
- `Disjoint.not_intersects`, and in fact `Disjoint A B ↔ ¬ Intersects A B`
- `Intersects.mono_left`, `Intersects.mono_right`, `Disjoint.mono_left`
- `intersects_not_transitive`: `Intersects A B` and `Intersects B C` do not
  imply `Intersects A C`. The proof is a counterexample with `A = {a}`,
  `B = {a, c}`, `C = {c}`. `Examples/Intersects.lean` gives the same failure
  with three side-by-side rectangles.

For the topology:

- `Rect.interior_toRegion`: the interior of a closed rectangle is the open
  rectangle, and `Rect.boundary_toRegion` computes its boundary.
- `touches_symm`, `Touches.intersects`, and
  `touches_iff_of_intersects`: among intersecting regions, touching means the
  interiors do not meet.
- `Touches.inter_subset_boundary`: for regions equal to the closure of their
  interior, every shared point of touching regions lies on both boundaries.
- `Examples/Touches.lean`: `[0,2]×[0,2]` and `[2,4]×[0,2]` touch, while
  `[0,2]×[0,2]` and `[1,3]×[0,2]` intersect without touching. Hence
  `intersects_not_imp_touches`.

For areas:

- `Rect.toRegularClosed`: a rectangle with positive width and height is an
  area (`Rect.closure_interior_toRegion`). `Rect.segment_not_regularClosed`
  shows the positivity is needed: a width-zero rectangle is a segment, not an
  area.
- `RegularClosedRegion.inter_subset_boundary_of_touches`: when two areas
  touch, every shared point lies on both boundaries. The only hypothesis is
  `Touches`.
- `Touches.not_exists_regularClosed_inter`: what two touching regions share
  is never an area. In `Examples/Touches.lean`, the shared edge of the two
  squares is a `Region` but not a `RegularClosedRegion`.
- `RegularClosedRegion.union`: the union of two areas is an area. The
  intersection is not, by the previous point.

For RCC8, with `A` and `B` nonempty areas:

- `existsUnique_relation`: exactly one of the eight relations holds. It is
  split into `jointly_exhaustive` and `pairwise_disjoint`.
- `dc_iff_disjoint` and `ec_iff_touches`: `DC` is `Disjoint`, `EC` is
  `Touches`. `tppi_iff_tpp` and `ntppi_iff_ntpp`: the inverses are the
  converses, and `Relation.holds_converse` states this for all eight.
- `po_iff_cells`: `PO` means `II`, `IE` and `EI` are all nonempty. It rests on
  `not_within_iff_IE_nonempty`: an area fails to lie within `B` exactly when
  some interior point of it is exterior to `B`.
- `Examples/RCC8.lean` proves one relation for each of the eight on squares,
  for example that a corner square is `TPP` of the big square and nothing else.

The proof of uniqueness goes through `classify`, a decision tree over
"connected, interiors meet, equal, within, within the interior". It is a
proof device only; the relations are the definitions in the table of
section 7.

For weak composition:

- `mem_compose_converse` and `compose_converse`: the converse of `r ⋄ s` is
  `s˘ ⋄ r˘`.
- `eq_compose` and `compose_eq`: `EQ ⋄ r = {r} = r ⋄ EQ`. This needs every
  relation to occur between some pair of nonempty areas
  (`Relation.realizable`, witnessed by the squares of `RCC8Witnesses.lean`).
- `ntpp_compose_ntpp`: `NTPP ⋄ NTPP = {NTPP}`. One direction is
  `ntpp_trans`, the other is three nested squares. `ntppi_compose_ntppi`
  follows from the converse law.
- `compose_eq_table` and the 64 cells: section 9.

For the checker and the prover:

- `Graph.check_entailed`, `Graph.check_possible`, `Graph.check_contradictory`:
  the verdicts of sections 12 and 13. They rest on `Graph.mem_derived`,
  `Graph.mem_stated` and `Graph.no_model_of_conflict`.
- `Claim.decide_iff`: the DE-9IM answers of section 6.

### 16. Axiom and proof audit

`lake build` checks every theorem, including the examples. The repository
contains no `sorry`, no `admit` and no `axiom` of its own.
`Examples/Axioms.lean` pins the main theorems to Lean's three standard axioms
(`propext`, `Classical.choice`, `Quot.sound`, which come with Mathlib's real
numbers), or a subset of them, so adding an axiom or an unfinished proof
makes the build fail. CI also greps for `sorry` and `admit`.

### 17. Repository layout

| File | Contents |
| --- | --- |
| `LeanGeospatial/Point.lean` | `Point2D`, Euclidean `distance`, `midpoint` |
| `LeanGeospatial/Region.lean` | `Region`, the four relations and their laws |
| `LeanGeospatial/Polygon.lean` | `Polygon` (vertex data, shoelace area), `Rect` (a shape with a defined region) |
| `LeanGeospatial/Topology.lean` | The plane's topology, `boundary`, `Touches`, interior and boundary of a `Rect` |
| `LeanGeospatial/RegularClosed.lean` | `RegularClosedRegion`, the type of areas |
| `LeanGeospatial/NineIntersection.lean` | `exterior`, the three-part split, the nine cells, relations as cell conditions |
| `LeanGeospatial/RCC8.lean` | The eight RCC8 base relations and the proof that exactly one holds |
| `LeanGeospatial/RCC8Witnesses.lean` | Squares realising each RCC8 relation, used by weak composition |
| `LeanGeospatial/Composition.lean` | Weak composition of RCC8 relations, defined and proved from the relations |
| `LeanGeospatial/CompositionTable/Abstract.lean` | Signatures, nine laws, the computed `table`, and `r ⋄ s ⊆ table r s` |
| `LeanGeospatial/RCC8Witnesses/Triples.lean` | Generated: 112 rectangle witnesses |
| `LeanGeospatial/CompositionTable/Complete.lean` | Generated: every entry of `table` realised |
| `LeanGeospatial/CompositionTable.lean` | `compose_eq_table : r ⋄ s = table r s` |
| `LeanGeospatial/CompositionTable/Cells.lean` | Generated: the 64 cells, one theorem each |
| `LeanGeospatial/Connected.lean` | The plane is connected; boundaries and exteriors are nonempty where expected |
| `LeanGeospatial/DE9IM.lean` | DE-9IM patterns with `T`, `F`, `*`, read from 9-character strings |
| `LeanGeospatial/Geometry.lean` | Points, line strings and areas with Simple Features interior, boundary, exterior |
| `LeanGeospatial/DE9IM/Dimension.lean` | DE-9IM cell values `F`, `0`, `1`, `2` and dimensioned patterns |
| `LeanGeospatial/GeometryFacts.lean` | Lines are closed with empty interior; arcs survive removing points; `g ⊄ h` iff `IE ≠ ∅` |
| `LeanGeospatial/DE9IM/Values.lean` | Which cell values points, lines and areas allow |
| `LeanGeospatial/SimpleFeatures.lean` | The eight Simple Features relations, defined from point sets |
| `LeanGeospatial/GeoSPARQL/Table2/*.lean` | GeoSPARQL 1.1 Table 2 against those definitions |
| `LeanGeospatial/SFA/Spec.lean` | OGC SFA 1.2.1 clause 6.1.15, transcribed for comparison |
| `LeanGeospatial/SFA/Compare.lean` | SFA against LeanGeospatial, against itself, and against GeoSPARQL |
| `LeanGeospatial/GeoSPARQL/Spec.lean` | GeoSPARQL 1.1 Tables 2, 4, 5, 6, 8, transcribed for comparison |
| `LeanGeospatial/GeoSPARQL/AreaArea.lean` | The tables compared with the semantics, for areas |
| `LeanGeospatial/GeoSPARQL/Counterexamples.lean` | Areas where the Table 8 patterns fail |
| `LeanGeospatial/Validator.lean` | The RCC8 checker (`Graph.check`), with its soundness theorems |
| `LeanGeospatial/ValidatorText.lean` | The validator's plain-text input format |
| `LeanGeospatial/Prover/DE9IMClaim.lean` | Simple Features claims read off a stated DE-9IM matrix, proved exact |
| `LeanGeospatial/ProverJSON.lean` | JSON Lines front end for `lean-geospatial-prover` (unproved glue) |
| `LeanGeospatial/Examples/Administrative.lean` | District A / City B / Province C |
| `LeanGeospatial/Examples/Intersects.lean` | Three rectangles showing `Intersects` is not transitive |
| `LeanGeospatial/Examples/Measurement.lean` | Distance and area on concrete coordinates |
| `LeanGeospatial/Examples/Touches.lean` | Two squares that touch, and two that overlap; their shared edge is not an area |
| `LeanGeospatial/Examples/NineIntersection.lean` | Cells of touching, separated and nested squares; two counterexamples |
| `LeanGeospatial/Examples/RCC8.lean` | All eight relations on squares |
| `LeanGeospatial/Examples/PublishedTable.lean` | Generated: comparison with the published RCC8 table |
| `LeanGeospatial/Examples/DimensionalCells.lean` | One `II` cell of each value |
| `LeanGeospatial/Examples/Prover.lean` | What the prover's DE-9IM answers mean, as theorems |
| `LeanGeospatial/Examples/Validator.lean` | The checker's cases, with what each verdict proves |
| `LeanGeospatial/Examples/Axioms.lean` | Axiom audit of the main theorems |
| `Main.lean` | The `lean-geospatial` command (validator) |
| `ProverMain.lean` | The `lean-geospatial-prover` command |

The library under `LeanGeospatial/` never imports `LeanGeospatial/Examples/`;
the examples only use the library. CI checks this.

### 18. Build and development

```bash
lake exe cache get   # prebuilt Mathlib
lake build           # every theorem, the library and both commands
```

CI runs `lake build` and, in addition:

- a grep for `sorry` and `admit`;
- a check that the library does not import `Examples`;
- `python3 scripts/gen_rcc8_table.py`, then a check that the generated
  composition-table files are unchanged;
- the validator on `samples/*.txt`, compared with `samples/expected.out`;
- the prover on `samples/prover.jsonl`, compared with
  `samples/prover.expected.jsonl`;
- the prover on `samples/prover-contract.jsonl`, compared with
  `samples/prover-contract.expected.jsonl`, with one answer per non-blank
  line;
- `scripts/prover_stream_test.py --lines 20000 --stack-kb 256`, which
  generates an input at run time and checks the answers, their count and
  their order; the small stack catches a stack that grows per line.

For a full stress run of the prover:

```
python3 scripts/prover_stream_test.py --lines 720000
```
