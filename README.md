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
| `LeanGeospatial/Examples/Administrative.lean` | District A / City B / Province C |
| `LeanGeospatial/Examples/Intersects.lean` | Three rectangles showing `Intersects` is not transitive |
| `LeanGeospatial/Examples/Measurement.lean` | Distance and area on concrete coordinates |
| `LeanGeospatial/Examples/Touches.lean` | Two squares that touch, and two that overlap |
| `LeanGeospatial/Examples/Axioms.lean` | Axiom audit of the main theorems |

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
- Whether a real region is closed, or equal to the closure of its interior.
  Lemmas that need this take it as a hypothesis.
- Coordinate reference systems. Coordinates are plain real numbers in a flat
  plane, and `distance` is Euclidean, not a distance on the Earth.
- Reading real data.

## Out of scope for now

DE-9IM, RCC8, GeoSPARQL, coordinate reference systems and GIS I/O.
