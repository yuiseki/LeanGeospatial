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
| `LeanGeospatial/Examples/Administrative.lean` | District A / City B / Province C |
| `LeanGeospatial/Examples/Intersects.lean` | Three rectangles showing `Intersects` is not transitive |
| `LeanGeospatial/Examples/Measurement.lean` | Distance and area on concrete coordinates |
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

Boundaries are not distinguished from interiors. Two regions that only touch
along an edge therefore `Intersect`, and are not `Disjoint`.

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

- Which set of points a general polygon encloses. Only `Rect` has a region.
- Coordinate reference systems. Coordinates are plain real numbers in a flat
  plane, and `distance` is Euclidean, not a distance on the Earth.
- Reading real data.

## Out of scope for now

DE-9IM, RCC8, GeoSPARQL, coordinate reference systems and GIS I/O.
