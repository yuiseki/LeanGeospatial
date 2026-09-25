import LeanGeospatial.RCC8
import LeanGeospatial.Examples.NineIntersection

/-!
# RCC8 on squares

```
  y
  2 +-------+-------+           +---+
    |  +-+  |       |           |   |
    |  |N|  |   B   |           | D |
    +--+ +  |       |           |   |
    | T  |  |       |           |   |
  0 +----+--+-------+           +---+
    0    1  2       4           5   6  x

  A = [0,2]×[0,2]       B = [2,4]×[0,2]    C = [1,3]×[0,2]
  D = [5,6]×[0,2]       N = [1/2,3/2]²     T = [0,1]×[0,1]
```

| Pair | Relation |
| --- | --- |
| A, D | `DC` |
| A, B | `EC` |
| A, C | `PO` |
| A, A | `EQ` |
| T, A | `TPP` (T shares the corner and two edges with A) |
| N, A | `NTPP` (N stays off A's boundary) |
| A, T | `TPPi` |
| A, N | `NTPPi` |

Each pair gets one relation proved, and `existsUnique_relation` then rules out
the other seven.
-/

namespace Geospatial.Examples.RCC8

open Geospatial Geospatial.RCC8
open Geospatial.Examples.Touches Geospatial.Examples.NineIntersection

noncomputable section

def areaC : RegularClosedRegion :=
  squareC.toRegularClosed (by norm_num [squareC]) (by norm_num [squareC])

def squareT : Rect := ⟨0, 1, 0, 1⟩
def areaT : RegularClosedRegion :=
  squareT.toRegularClosed (by norm_num [squareT]) (by norm_num [squareT])

/-- Membership in a rectangle's area, as inequalities. -/
theorem mem_area (r : Rect) (hx : r.xmin < r.xmax) (hy : r.ymin < r.ymax) (p : Point2D) :
    p ∈ ((r.toRegularClosed hx hy : RegularClosedRegion) : Region) ↔
      r.xmin ≤ p.x ∧ p.x ≤ r.xmax ∧ r.ymin ≤ p.y ∧ p.y ≤ r.ymax :=
  Iff.rfl

theorem areaA_nonempty : (areaA : Region).Nonempty :=
  ⟨⟨0, 0⟩, by rw [areaA, mem_area]; norm_num [squareA]⟩

theorem areaT_nonempty : (areaT : Region).Nonempty :=
  ⟨⟨0, 0⟩, by rw [areaT, mem_area]; norm_num [squareT]⟩

theorem A_D_dc : DC areaA areaD := A_disjoint_D

theorem A_B_ec : EC areaA areaB := areaA_touches_areaB

theorem A_C_po : PO areaA areaC := by
  refine ⟨interiors_A_C_intersect, fun h => ?_, fun h => ?_⟩
  · have hp : (⟨0, 1⟩ : Point2D) ∈ (areaA : Region) := by
      rw [areaA, mem_area]; norm_num [squareA]
    have := h hp
    rw [areaC, mem_area] at this
    norm_num [squareC] at this
  · have hp : (⟨3, 1⟩ : Point2D) ∈ (areaC : Region) := by
      rw [areaC, mem_area]; norm_num [squareC]
    have := h hp
    rw [areaA, mem_area] at this
    norm_num [squareA] at this

theorem A_A_eq : EQ areaA areaA := rfl

theorem T_A_tpp : TPP areaT areaA := by
  refine ⟨Rect.within_of_bounds (by norm_num [squareT, squareA])
      (by norm_num [squareT, squareA]) (by norm_num [squareT, squareA])
      (by norm_num [squareT, squareA]), fun h => ?_, fun h => ?_⟩
  · -- (2, 2) is a corner of A but not in T.
    have hp : (⟨2, 2⟩ : Point2D) ∈ (areaA : Region) := by
      rw [areaA, mem_area]; norm_num [squareA]
    rw [← h, areaT, mem_area] at hp
    norm_num [squareT] at hp
  · -- (0, 0) is in T but on A's boundary, not in its interior.
    have hp : (⟨0, 0⟩ : Point2D) ∈ (areaT : Region) := by
      rw [areaT, mem_area]; norm_num [squareT]
    have := h hp
    rw [areaA, Rect.coe_toRegularClosed, Rect.interior_toRegion] at this
    obtain ⟨h₁, -⟩ := this
    norm_num [squareA] at h₁

theorem N_A_ntpp : NTPP areaN areaA := by
  refine ⟨fun p hp => ?_, fun h => ?_⟩
  · rw [areaN, mem_area] at hp
    rw [areaA, Rect.coe_toRegularClosed, Rect.interior_toRegion]
    simp only [squareN] at hp
    obtain ⟨h₁, h₂, h₃, h₄⟩ := hp
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [squareA] <;> linarith
  · have hp : (⟨0, 0⟩ : Point2D) ∈ (areaA : Region) := by
      rw [areaA, mem_area]; norm_num [squareA]
    rw [← h, areaN, mem_area] at hp
    norm_num [squareN] at hp

theorem A_T_tppi : TPPi areaA areaT := T_A_tpp

theorem A_N_ntppi : NTPPi areaA areaN := N_A_ntpp

/-- The relation between T and A is `TPP` and nothing else. -/
theorem T_A_only_tpp (r : Relation) : r.holds areaT areaA ↔ r = .tpp :=
  ⟨fun h => relation_unique areaT areaA areaT_nonempty areaA_nonempty h T_A_tpp,
    fun h => h ▸ T_A_tpp⟩

/-- The relation between A and C is `PO` and nothing else. -/
theorem A_C_only_po (r : Relation) : r.holds areaA areaC ↔ r = .po :=
  ⟨fun h => relation_unique areaA areaC areaA_nonempty
      ⟨⟨3 / 2, 1⟩, by rw [areaC, mem_area]; norm_num [squareC]⟩ h A_C_po,
    fun h => h ▸ A_C_po⟩

end

end Geospatial.Examples.RCC8
