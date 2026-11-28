import LeanGeospatial.DimensionIndependent3D
import Mathlib.Geometry.Manifold.Instances.Sphere

/-!
# Unified Geospatial Semantics across `ℝ²`, `S²`, and `ℝ³`

Consolidates the three canonical geospatial spaces on Mathlib's Euclidean
foundation without introducing wrapper types:

- `E2 := Geospatial.Point2D` (`EuclideanSpace ℝ (Fin 2)`) — the flat plane `ℝ²`
- `S2 := Metric.sphere (0 : E3) 1` — the unit 2-sphere `S² ⊂ ℝ³`
- `E3 := Geospatial.DE9IM.Space3.E3` (`EuclideanSpace ℝ (Fin 3)`) — 3D space `ℝ³`

## Audit: arbitrary `[TopologicalSpace α]` vs 2D-specific definitions

| Concept | Scope in `LeanGeospatial` | Applies to `ℝ²`, `S²`, `ℝ³`? |
| --- | --- | --- |
| `Within`, `Contains`, `Intersects`, `Disjoint` | Any `Type*` (`Region.lean`) | Yes |
| `boundary`, `exterior`, `Touches`, `RegularClosedRegion α` | Any `[TopologicalSpace α]` (`Topology.lean`, `RegularClosed.lean`, `NineIntersection.lean`) | Yes |
| `RCC8` base relations, `existsUnique_relation`, composition soundness | Any `[TopologicalSpace α]` (`RCC8.lean`, `Composition.lean`, `CompositionTable/Abstract.lean`) | Yes |
| `RCC8Complete α` (composition table completeness) | Needs non-discrete local model; proved for `ℝ²`, `S²`, `ℝ³` | Yes (`rcc8Complete_E2`, `rcc8Complete_S2`, `rcc8Complete_E3`) |
| `RCC8ConnectedComplete α` (connected completeness) | Fails in `ℝ`; holds in `ℝ²`, `S²`, `ℝ³` | Yes (`rcc8ConnectedComplete_E2`, `rcc8ConnectedComplete_S2`, `rcc8ConnectedComplete_E3`) |
| `DE9IM.Pattern` (`T`/`F`/`*`), `DE9IM.de9im (cubeDim n)` | Any `[TopologicalSpace α]` (`DE9IM.lean`, `DE9IM/DimensionFunction.lean`, `DE9IM/CubeDimension.lean`) | Yes (`cubeDim 2` on `ℝ²`/`S²`, `cubeDim 3` on `ℝ³`) |
| `Geometry`, `SFA.*`, `GeoSPARQL.*`, `DE9IM.DimValue`, `ComputationalPolygon` | Inherently 2D (`Point2D`) | `ℝ²` only (OGC SFA 1.2.1 is 2D) |
| `DE9IM3D.de9im3D` (`Solid3D`) | Custom 3D topological extension (NOT OGC standard) | `ℝ³` |

## New theorem

- `rcc8ConnectedComplete_S2`: the RCC8 composition table is complete on `S²`
  even when restricted to **connected** regular closed regions on the sphere,
  proved by transporting the plane's compact connected witnesses through an
  open chart embedding into Hausdorff `S²`.
-/

namespace Geospatial.Spaces

open Set Topology Geospatial Geospatial.DE9IM Geospatial.DE9IM.Space3 Geospatial.DE9IM3D

/-- The 2D Euclidean plane `ℝ²`. -/
abbrev E2 := Geospatial.Point2D

/-- The 3D Euclidean space `ℝ³`. -/
abbrev E3 := Geospatial.DE9IM.Space3.E3

/-- The unit 2-sphere `S² ⊂ ℝ³`. -/
abbrev S2 := Metric.sphere (0 : E3) 1

/-- The north pole `(0, 0, 1)` on `S²`. -/
noncomputable def northPole : S2 :=
  ⟨EuclideanSpace.single 2 1, by simp⟩

/-- The south pole `(0, 0, -1)` on `S²`. -/
noncomputable def southPole : S2 :=
  ⟨EuclideanSpace.single 2 (-1), by simp⟩

instance : Nonempty S2 := ⟨northPole⟩

theorem northPole_ne_southPole : northPole ≠ southPole := by
  intro h
  have h2 := congrArg (fun p : S2 => (p : E3) 2) h
  simp [northPole, southPole] at h2
  norm_num at h2

/-! ## Unified RCC8 theorems across `ℝ²`, `S²`, `ℝ³` -/

theorem rcc8_existsUnique_E2 (A B : RegularClosedRegion E2)
    (hA : (A : Set E2).Nonempty) (hB : (B : Set E2).Nonempty) :
    ∃! r : RCC8.Relation, r.holds A B :=
  RCC8.existsUnique_relation A B hA hB

theorem rcc8_existsUnique_S2 (A B : RegularClosedRegion S2)
    (hA : (A : Set S2).Nonempty) (hB : (B : Set S2).Nonempty) :
    ∃! r : RCC8.Relation, r.holds A B :=
  RCC8.existsUnique_relation A B hA hB

theorem rcc8_existsUnique_E3 (A B : RegularClosedRegion E3)
    (hA : (A : Set E3).Nonempty) (hB : (B : Set E3).Nonempty) :
    ∃! r : RCC8.Relation, r.holds A B :=
  RCC8.existsUnique_relation A B hA hB

theorem rcc8Complete_E2 : RCC8Complete E2 := rcc8Complete_plane

theorem rcc8Complete_S2 : RCC8Complete S2 := rcc8Complete_of_chartedSpace S2

theorem rcc8Complete_E3 : RCC8Complete E3 := rcc8Complete_euclideanSpace3

/-- An open embedding of `ℝ²` into a Hausdorff space `α` transfers **connected**
RCC8 completeness, because the plane's witnesses in `realizes_of_mem_table`
are both compact and connected. -/
theorem rcc8ConnectedComplete_of_isOpenEmbedding {α : Type*} [TopologicalSpace α] [T2Space α]
    {f : Point2D → α} (hf : IsOpenEmbedding f) : RCC8ConnectedComplete α := by
  intro r s
  apply Set.Subset.antisymm
  · rintro t ⟨A, B, C, cA, cB, cC, hr, hs, ht⟩
    exact Finset.mem_coe.mpr
      (RCC8.mem_table_of_mem_compose ⟨A, B, C, cA.nonempty, cB.nonempty, cC.nonempty, hr, hs, ht⟩)
  · intro t ht
    obtain ⟨A, B, C, kA, kB, kC, cA, cB, cC, -, -, -, hr, hs, ht'⟩ :=
      RCC8.realizes_of_mem_table r s t (Finset.mem_coe.mp ht)
    exact ⟨A.mapCompact hf kA, B.mapCompact hf kB, C.mapCompact hf kC,
      cA.image f hf.continuous.continuousOn,
      cB.image f hf.continuous.continuousOn,
      cC.image f hf.continuous.continuousOn,
      (RCC8.Relation.holds_mapCompact_iff hf kA kB r).mpr hr,
      (RCC8.Relation.holds_mapCompact_iff hf kB kC s).mpr hs,
      (RCC8.Relation.holds_mapCompact_iff hf kA kC t).mpr ht'⟩

/-- Every nonempty Hausdorff 2-manifold is complete for **connected** RCC8. -/
theorem rcc8ConnectedComplete_of_chartedSpace (M : Type*) [TopologicalSpace M]
    [ChartedSpace E2 M] [T2Space M] [Nonempty M] : RCC8ConnectedComplete M := by
  obtain ⟨x⟩ := ‹Nonempty M›
  let e := chartAt E2 x
  obtain ⟨g, hg, hrange⟩ :=
    exists_isOpenEmbedding_into e.open_target ⟨e x, mem_chart_target _ x⟩
  refine rcc8ConnectedComplete_of_isOpenEmbedding (f := e.symm ∘ g) ?_
  refine IsOpenEmbedding.of_continuous_injective_isOpenMap ?_ ?_ ?_
  · exact e.continuousOn_symm.comp_continuous hg.continuous fun y => hrange ⟨y, rfl⟩
  · intro a b h
    exact hg.injective (e.symm.injOn (hrange ⟨a, rfl⟩) (hrange ⟨b, rfl⟩) h)
  · intro V hV
    rw [Set.image_comp]
    exact e.symm.isOpen_image_of_subset_source (hg.isOpenMap V hV)
      ((Set.image_subset_range g V).trans hrange)

theorem rcc8ConnectedComplete_E2 : RCC8ConnectedComplete E2 := rcc8ConnectedComplete_plane

/-- The RCC8 composition table is complete on `S²` even for **connected**
spherical regions. -/
theorem rcc8ConnectedComplete_S2 : RCC8ConnectedComplete S2 :=
  rcc8ConnectedComplete_of_chartedSpace S2

theorem rcc8ConnectedComplete_E3 : RCC8ConnectedComplete E3 :=
  DE9IM3D.rcc8ConnectedComplete_E3

/-! ## Canonical dimension functions on `ℝ²`, `S²`, `ℝ³` -/

/-- Canonical dimension function on `ℝ²` (`cubeDim 2 = planeDim`). -/
noncomputable abbrev dimE2 : DimensionFunction E2 := cubeDim 2

/-- Canonical intrinsic dimension function on `S²` (`cubeDim 2`). -/
noncomputable abbrev dimS2 : DimensionFunction S2 := cubeDim 2

/-- Canonical dimension function on `ℝ³` (`cubeDim 3`, non-OGC 3D extension). -/
noncomputable abbrev dimE3 : DimensionFunction E3 := cubeDim 3

theorem dimE2_eq_planeDim : dimE2 = planeDim := planeDim_eq_cubeDim.symm

end Geospatial.Spaces
