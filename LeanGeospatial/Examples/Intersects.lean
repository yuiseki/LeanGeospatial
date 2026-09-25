import LeanGeospatial.Polygon

/-!
# Intersects is not transitive, with rectangles

`intersects_not_transitive` in `Region.lean` gives the minimal counterexample
with single points. This file shows the same failure with shapes that look like
map features: three unit-high strips laid side by side.

```
  A = [0,2]×[0,1]   B = [1,4]×[0,1]   C = [3,5]×[0,1]

  0    1    2    3    4    5
  |----A----|
       |--------B-------|
                 |----C----|
```

A overlaps B, B overlaps C, but A and C are separated by the gap `(2,3)`.
-/

namespace Geospatial.Examples.Intersects

open Geospatial

noncomputable section

def stripA : Rect := ⟨0, 2, 0, 1⟩
def stripB : Rect := ⟨1, 4, 0, 1⟩
def stripC : Rect := ⟨3, 5, 0, 1⟩

theorem A_intersects_B : Intersects stripA.toRegion stripB.toRegion :=
  ⟨⟨3 / 2, 0⟩, by
    simp only [Set.mem_inter_iff, Rect.toRegion, stripA, stripB, Set.mem_setOf_eq]
    norm_num⟩

theorem B_intersects_C : Intersects stripB.toRegion stripC.toRegion :=
  ⟨⟨7 / 2, 0⟩, by
    simp only [Set.mem_inter_iff, Rect.toRegion, stripB, stripC, Set.mem_setOf_eq]
    norm_num⟩

theorem A_disjoint_C : Geospatial.Disjoint stripA.toRegion stripC.toRegion := by
  rw [Geospatial.Disjoint, Set.eq_empty_iff_forall_not_mem]
  rintro p ⟨⟨_, hA, _⟩, ⟨hC, _⟩⟩
  simp only [stripA, stripC] at hA hC
  linarith

theorem A_not_intersects_C : ¬ Intersects stripA.toRegion stripC.toRegion :=
  A_disjoint_C.not_intersects

/-- The premises of "transitivity" hold while its conclusion fails. -/
theorem intersects_chain_does_not_close :
    Intersects stripA.toRegion stripB.toRegion ∧
    Intersects stripB.toRegion stripC.toRegion ∧
    ¬ Intersects stripA.toRegion stripC.toRegion :=
  ⟨A_intersects_B, B_intersects_C, A_not_intersects_C⟩

end

end Geospatial.Examples.Intersects
