import LeanGeospatial.Topology

/-!
# Touches versus Intersects

Two closed squares side by side share an edge. They intersect, because the
edge belongs to both, but they only touch: no interior point is shared. A
third square shifted halfway over the first overlaps it, so those two
intersect without touching.

```
  y
  2 +-------+-------+
    |       |       |
    |   A   |   B   |       A = [0,2]×[0,2]
    |       |       |       B = [2,4]×[0,2]
  0 +-------+-------+       C = [1,3]×[0,2]
    0       2       4  x
        |-------|
            C
```
-/

namespace Geospatial.Examples.Touches

open Geospatial

noncomputable section

def squareA : Rect := ⟨0, 2, 0, 2⟩
def squareB : Rect := ⟨2, 4, 0, 2⟩
def squareC : Rect := ⟨1, 3, 0, 2⟩

/-- `(2, 1)` is on the shared edge of A and B. -/
def edgePoint : Point2D := ⟨2, 1⟩

theorem A_intersects_B : Intersects squareA.toRegion squareB.toRegion :=
  ⟨edgePoint, by
    simp only [Set.mem_inter_iff, Rect.toRegion, squareA, squareB, edgePoint,
      Set.mem_setOf_eq]
    norm_num⟩

theorem interiors_A_B_disjoint :
    Geospatial.Disjoint (interior squareA.toRegion) (interior squareB.toRegion) := by
  rw [Geospatial.Disjoint, Rect.interior_toRegion, Rect.interior_toRegion,
    Set.eq_empty_iff_forall_not_mem]
  rintro p ⟨⟨_, hA, _⟩, ⟨hB, _⟩⟩
  simp only [squareA, squareB] at hA hB
  linarith

/-- A and B touch. -/
theorem A_touches_B : Touches squareA.toRegion squareB.toRegion :=
  ⟨A_intersects_B, interiors_A_B_disjoint⟩

/-- The shared point lies on the boundary of both squares. -/
theorem edgePoint_on_both_boundaries :
    edgePoint ∈ boundary squareA.toRegion ∩ boundary squareB.toRegion := by
  rw [Rect.boundary_toRegion, Rect.boundary_toRegion]
  simp only [Set.mem_inter_iff, Set.mem_diff, Rect.toRegion, Rect.openRegion,
    squareA, squareB, edgePoint, Set.mem_setOf_eq]
  norm_num

/-- The same fact from the general lemma: squares are the closure of their
interior, so any shared point of touching squares is on both boundaries. -/
theorem A_inter_B_subset_boundaries :
    squareA.toRegion ∩ squareB.toRegion ⊆
      boundary squareA.toRegion ∩ boundary squareB.toRegion := by
  have hA : closure (interior squareA.toRegion) = squareA.toRegion := by
    rw [Rect.interior_toRegion, Rect.openRegion_eq_preimage,
      ← Point2D.homeomorphProd.preimage_closure, closure_prod_eq,
      closure_Ioo (by norm_num [squareA]), closure_Ioo (by norm_num [squareA]),
      ← Rect.toRegion_eq_preimage]
  have hB : closure (interior squareB.toRegion) = squareB.toRegion := by
    rw [Rect.interior_toRegion, Rect.openRegion_eq_preimage,
      ← Point2D.homeomorphProd.preimage_closure, closure_prod_eq,
      closure_Ioo (by norm_num [squareB]), closure_Ioo (by norm_num [squareB]),
      ← Rect.toRegion_eq_preimage]
  exact A_touches_B.inter_subset_boundary hA hB

/-- `(3/2, 1)` is inside both A and C. -/
def overlapPoint : Point2D := ⟨3 / 2, 1⟩

theorem A_intersects_C : Intersects squareA.toRegion squareC.toRegion :=
  ⟨overlapPoint, by
    simp only [Set.mem_inter_iff, Rect.toRegion, squareA, squareC, overlapPoint,
      Set.mem_setOf_eq]
    norm_num⟩

theorem interiors_A_C_intersect :
    Intersects (interior squareA.toRegion) (interior squareC.toRegion) :=
  ⟨overlapPoint, by
    rw [Rect.interior_toRegion, Rect.interior_toRegion]
    simp only [Set.mem_inter_iff, Rect.openRegion, squareA, squareC, overlapPoint,
      Set.mem_setOf_eq]
    norm_num⟩

/-- A and C intersect but do not touch: they overlap. -/
theorem A_not_touches_C : ¬ Touches squareA.toRegion squareC.toRegion :=
  fun h => h.not_intersects_interior interiors_A_C_intersect

/-- `Intersects` does not imply `Touches`. -/
theorem intersects_not_imp_touches :
    ¬ ∀ A B : Region, Intersects A B → Touches A B :=
  fun h => A_not_touches_C (h _ _ A_intersects_C)

/-- Both pairs intersect; only the first touches. -/
theorem touches_distinguishes_from_intersects :
    (Intersects squareA.toRegion squareB.toRegion ∧
      Touches squareA.toRegion squareB.toRegion) ∧
    (Intersects squareA.toRegion squareC.toRegion ∧
      ¬ Touches squareA.toRegion squareC.toRegion) :=
  ⟨⟨A_intersects_B, A_touches_B⟩, ⟨A_intersects_C, A_not_touches_C⟩⟩

end

end Geospatial.Examples.Touches
