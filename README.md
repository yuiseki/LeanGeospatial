# LeanGeospatial

A small formal system in Lean 4 for machine-checking claims about space.

This is not a GIS engine written in Lean. The goal is narrower: when someone
says "District A is in City B and City B is in Province C, so District A is in
Province C", Lean should be able to check that the step from the premises to
the conclusion is valid, with no trust in any geometry code.

## Build

```bash
lake exe cache get   # prebuilt Mathlib
lake build
```

`lake build` checks every theorem, including the examples. The repository
contains no `sorry`, no `admit` and no `axiom` of its own.
`Examples/Axioms.lean` pins the main theorems to Lean's three standard axioms
(`propext`, `Classical.choice`, `Quot.sound`, which come with Mathlib's real
numbers), so adding an axiom or an unfinished proof makes the build fail. CI
also greps for `sorry` and `admit`.

## Layout

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
| `LeanGeospatial/Validator.lean` | An RCC8 validator whose verdicts are backed by theorems |
| `LeanGeospatial/ValidatorText.lean` | The validator's plain-text input format |
| `LeanGeospatial/Examples/Administrative.lean` | District A / City B / Province C |
| `LeanGeospatial/Examples/Intersects.lean` | Three rectangles showing `Intersects` is not transitive |
| `LeanGeospatial/Examples/Measurement.lean` | Distance and area on concrete coordinates |
| `LeanGeospatial/Examples/Touches.lean` | Two squares that touch, and two that overlap; their shared edge is not an area |
| `LeanGeospatial/Examples/NineIntersection.lean` | Cells of touching, separated and nested squares; two counterexamples |
| `LeanGeospatial/Examples/RCC8.lean` | All eight relations on squares |
| `LeanGeospatial/Examples/PublishedTable.lean` | Generated: comparison with the published RCC8 table |
| `LeanGeospatial/Examples/DimensionalCells.lean` | One `II` cell of each value |
| `LeanGeospatial/Examples/Validator.lean` | The validator's three cases, with what each verdict proves |
| `LeanGeospatial/Examples/Axioms.lean` | Axiom audit of the main theorems |

The library under `LeanGeospatial/` never imports `LeanGeospatial/Examples/`;
the examples only use the library. CI checks this.

## The model

A `Region` is a set of points, `Set Point2D`. A `Polygon` is only data, a list
of vertices, and is kept separate from `Region`. The relations are defined by
set operations, not postulated:

| Relation | Definition |
| --- | --- |
| `Within A B` | `A ⊆ B` |
| `Contains A B` | `B ⊆ A` |
| `Intersects A B` | `(A ∩ B).Nonempty` |
| `Disjoint A B` | `A ∩ B = ∅` |

These four relations ignore boundaries. Two regions that only share an edge
`Intersect`, and are not `Disjoint`.

## Topology

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
`Intersects` alone cannot.

## Areas: regular closed regions

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
`Region` is expected, but not the other way round.

## Nine intersections

`exterior A` is `interior Aᶜ`, which equals `(closure A)ᶜ`. Interior, boundary
and exterior split the plane: every point is in exactly one of them
(`existsUnique_stratum`). For two regions this gives nine cells,

```lean
cell s t A B = s.set A ∩ t.set B      -- s, t ∈ {I, B, E}
```

abbreviated `II`, `IB`, `IE`, `BI`, `BB`, `BE`, `EI`, `EB`, `EE`, with the
first letter for `A`. Only whether a cell is empty is used. There are no
dimensions, no matrix type and no pattern strings yet.

The relations are still defined by the set operations above. The cell
conditions are theorems derived from those definitions, not a second set of
definitions.

## RCC8

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

## Weak composition

```lean
r ⋄ s = {t | ∃ A B C nonempty areas, r A B ∧ s B C ∧ t A C}
```

This is the meaning of an entry in the RCC8 composition table. No table is
assumed: each entry has to be proved from the definitions, in both
directions. Showing `t ∈ r ⋄ s` needs three concrete areas; showing
`t ∉ r ⋄ s` needs an argument that works for all areas.

## GeoSPARQL 1.1, areas only

`DE9IM.lean` gives patterns a meaning from the nine cells: `T` nonempty, `F`
empty, `*` anything (dimensions `0`, `1`, `2` are not supported yet). A
pattern is a record with one field per cell; `Pattern.ofString?` reads the
9-character notation and rejects anything else.

`GeoSPARQL/Spec.lean` transcribes Tables 2, 4, 5, 6 and 8 of OGC 22-047r1.
They are data for comparison only. For nonempty areas, LeanGeospatial proves:

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

| Table 5 row | Holds for nonempty areas |
| --- | --- |
| equals ↔ `EQ` | yes |
| disjoint ↔ `DC` | yes |
| intersects ↔ ¬`DC` | yes |
| touches ↔ `EC` | yes |
| within ↔ `TPP` ∨ `NTPP` | no, `EQ` is missing: `Within ↔ TPP ∨ NTPP ∨ EQ` |
| contains ↔ `TPPi` ∨ `NTPPi` | no, `EQ` is missing |
| overlaps ↔ `PO` | yes |

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

## Points, lines and areas

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
is in exactly one stratum. For areas the strata are the ones used above, so
the Area/Area results are unchanged (`Geometry.cell_area_area`,
`Pattern.toDim_matches_area`). Multi geometries are not covered yet.

`DE9IM/Dimension.lean` gives a cell one of the values `F`, `0`, `1`, `2`,
without a dimension theory for arbitrary sets: `2` if the cell contains an
open set, `1` if it contains an arc but no open set, `0` if it is nonempty
with neither, `F` if it is empty. For the finite unions of points, arcs and
regions that occur as cells of these geometries, that is their dimension.
Every cell has exactly one value (`existsUnique_describes`). Patterns may use
`T F * 0 1 2`. `Examples/DimensionalCells.lean` shows one `II` cell of each
value, including two segments crossing in a point (`0`) and two collinear
segments overlapping in a segment (`1`).

## GeoSPARQL 1.1 Table 2, points, lines and areas

`DE9IM/Values.lean` checks the cell values are sensible: a cell through a
point's interior or boundary is `F` or `0`; through a line's interior or
boundary it is never `2`; two areas' interiors meet in `F` or `2`; and two
lines' interiors meet in `1` exactly when the intersection contains an arc,
in `0` when it is nonempty without one.

`SimpleFeatures.lean` defines the eight relations from point sets, strata
and interior dimensions, following the Simple Features point-set definitions,
with no DE-9IM pattern. `GeoSPARQL/Table2/` then compares Table 2's patterns
with them, for every combination of kinds Table 2 lists:

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
them while the `TFFFTFFFT` pattern fails.

Patterns that single geometries cannot realise: `overlaps` P/P, `crosses`
P/L and P/A (all need a MultiPoint), and `equals` P/P.

Not yet verified, because they need multi geometries:

- `overlaps` P/P and `crosses` P/L, P/A with MultiPoints;
- the mod-2 boundary rule of MultiLineStrings, which changes boundaries and
  so `equals`, `touches`, `within`, `overlaps`, `crosses` for lines;
- MultiPolygon validity rules (areas here may already have several parts,
  but are not checked against them);
- geometry collections of mixed dimension.

## Against OGC Simple Feature Access 1.2.1

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

## Validator

A proof of concept: given stated RCC8 relations between features, check a
pair of features against the composition table.

```
$ lake exe lean-geospatial samples/*.txt
samples/inconsistent.txt: BuildingA → BlockC: contradictory
samples/nested.txt: DistrictA → ProvinceC: entailed NTPP
samples/touching.txt: ParcelA → ParcelC: possible {DC, EC, PO, EQ, TPP, TPPi}
```

An input file has one fact per line (`DistrictA NTPP CityB`), queries
(`? DistrictA ProvinceC`) and `#` comments. For a pair `A`, `C` the validator
intersects `table r s` over every feature `B` with known `A r B` and `B s C`
(using converses for facts stated the other way), then answers:

- entailed `t`: only `t` is left, so every model has `A t C`
  (`Graph.check_entailed`).
- possible `S`: several relations are left; every model has one of them
  (`Graph.check_possible`). For a single triangle each of them also occurs
  (`triangle_realizes`); with more features, other facts may rule out more.
- contradictory: nothing is left, or the stated `A`–`C` relation is not among
  what is left, so no model exists (`Graph.check_contradictory`).

A model gives every feature a nonempty area making every fact true. The
three verdict theorems rest on the soundness half of the composition table
and on "exactly one relation holds". `Examples/Validator.lean` proves the
three sample cases as theorems; CI also runs the command on `samples/` and
compares with `samples/expected.out`.

## What Lean proves

These hold for every region, whatever its shape or source:

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

For the nine cells, with `A` and `B` areas:

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
proof device only; the relations are the definitions in the table.

For weak composition:

- `mem_compose_converse` and `compose_converse`: the converse of `r ⋄ s` is
  `s˘ ⋄ r˘`.
- `eq_compose` and `compose_eq`: `EQ ⋄ r = {r} = r ⋄ EQ`. This needs every
  relation to occur between some pair of nonempty areas
  (`Relation.realizable`, witnessed by the squares of `RCC8Witnesses.lean`).
- `ntpp_compose_ntpp`: `NTPP ⋄ NTPP = {NTPP}`. One direction is
  `ntpp_trans`, the other is three nested squares. `ntppi_compose_ntppi`
  follows from the converse law.

The full table is derived below.

## The composition table

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

With concrete coordinates it also proves numeric facts, for example that the
distance from `(0,0)` to `(10,10)` is `10 * √2` and that the 10 × 10 square has
shoelace area `100`.

## What is an assumption about external data

Lean does not know where District A is. In
`Examples/Administrative.lean` the facts

```lean
(hDistrictCity : Within DistrictA CityB)
(hCityProvince : Within CityB ProvinceC)
```

are hypotheses. They stand for claims from outside Lean: a boundary file, a
gazetteer, an official statement. Lean checks only that
`Within DistrictA ProvinceC` follows from them, which it does by the general
`within_trans`. If a hypothesis is false in the real world, the conclusion is
unsupported, and Lean cannot notice that.

Other things that are not modelled yet:

- Which set of points a general polygon encloses. Only `Rect` has a region,
  and so only `Rect` has a computed interior and boundary.
- Whether a real place is an area. Building a `RegularClosedRegion` needs a
  proof of `closure (interior A) = A`, which Lean can give for a `Rect` but not
  for a boundary loaded from outside. For such data it is an assumption, made
  once when the value is built.
- Coordinate reference systems. Coordinates are plain real numbers in a flat
  plane, and `distance` is Euclidean, not a distance on the Earth.
- Reading real data.

## Out of scope for now

DE-9IM dimensions (`0`, `1`, `2`), points and lines with their OGC boundary,
`crosses`, the Egenhofer relations, GeoSPARQL beyond areas, coordinate
reference systems and GIS I/O.
