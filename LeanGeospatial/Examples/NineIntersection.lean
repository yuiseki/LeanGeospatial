import LeanGeospatial.NineIntersection
import LeanGeospatial.Examples.Touches

/-!
# The nine cells on concrete squares

The characterisations in `NineIntersection.lean` read off which cells are
empty. Here they are applied to squares, and two counterexamples show why the
`Within` characterisation asks for a nonempty area.

```
  y
  2 +-------+-------+           +---+
    |  +-+  |       |           |   |
    |  |N|  |   B   |           | D |
    |  +-+  |       |           |   |
  0 +-------+-------+           +---+
    0   A   2       4           5   6  x
```
-/

namespace Geospatial.Examples.NineIntersection

open Geospatial
open Geospatial.Examples.Touches

noncomputable section

/-! ## Touching squares: interiors miss, boundaries meet -/

theorem A_B_cells :
    II (areaA : Region) areaB = ∅ ∧
    ((IB (areaA : Region) areaB).Nonempty ∨ (BI (areaA : Region) areaB).Nonempty ∨
      (BB (areaA : Region) areaB).Nonempty) :=
  (areaA.touches_iff_cells areaB).mp areaA_touches_areaB

/-- Concretely, it is the boundary-boundary cell that is nonempty. -/
theorem A_B_BB_nonempty : (BB (areaA : Region) areaB).Nonempty :=
  ⟨edgePoint, edgePoint_on_both_boundaries⟩

/-! ## Separated squares: the four non-exterior cells are empty -/

def squareD : Rect := ⟨5, 6, 0, 2⟩
def areaD : RegularClosedRegion :=
  squareD.toRegularClosed (by norm_num [squareD]) (by norm_num [squareD])

theorem A_disjoint_D : Geospatial.Disjoint (areaA : Region) areaD := by
  rw [Geospatial.Disjoint, Set.eq_empty_iff_forall_not_mem]
  rintro p ⟨⟨_, hA, _⟩, ⟨hD, _⟩⟩
  simp only [squareA, squareD] at hA hD
  linarith

theorem A_D_cells :
    II (areaA : Region) areaD = ∅ ∧ IB (areaA : Region) areaD = ∅ ∧
    BI (areaA : Region) areaD = ∅ ∧ BB (areaA : Region) areaD = ∅ :=
  (areaA.disjoint_iff_cells areaD).mp A_disjoint_D

/-! ## A nested square -/

def squareN : Rect := ⟨1 / 2, 3 / 2, 1 / 2, 3 / 2⟩
def areaN : RegularClosedRegion :=
  squareN.toRegularClosed (by norm_num [squareN]) (by norm_num [squareN])

theorem N_within_A : Within (areaN : Region) areaA :=
  Rect.within_of_bounds (by norm_num [squareN, squareA]) (by norm_num [squareN, squareA])
    (by norm_num [squareN, squareA]) (by norm_num [squareN, squareA])

theorem areaN_nonempty : (areaN : Region).Nonempty :=
  ⟨⟨1, 1⟩, by
    show (1 / 2 : ℝ) ≤ 1 ∧ (1 : ℝ) ≤ 3 / 2 ∧ (1 / 2 : ℝ) ≤ 1 ∧ (1 : ℝ) ≤ 3 / 2
    norm_num⟩

theorem N_A_cells :
    (II (areaN : Region) areaA).Nonempty ∧
    IE (areaN : Region) areaA = ∅ ∧ BE (areaN : Region) areaA = ∅ :=
  (areaN.within_iff_cells areaA areaN_nonempty).mp N_within_A

/-! ## Why `Within` needs a nonempty area -/

/-- The empty area lies within every area, yet its interior meets nothing. So
the nonemptiness hypothesis of `within_iff_cells` cannot be dropped. -/
theorem empty_within_but_II_empty (B : RegularClosedRegion) :
    Within ((⊥ : RegularClosedRegion) : Region) B ∧
    II ((⊥ : RegularClosedRegion) : Region) B = ∅ := by
  refine ⟨?_, ?_⟩
  · intro p hp
    exact absurd hp (Set.not_mem_empty p)
  · simp [cell, Stratum.set]

/-- A segment on the left edge of square A: closed and nonempty, but not an
area. -/
def segment : Rect := ⟨0, 0, 0, 2⟩

/-- The segment lies within A, yet its interior is empty, so `II` is empty.
The characterisation of `Within` fails for closed regions that are not areas;
that is why it is stated for `RegularClosedRegion`. -/
theorem segment_within_but_II_empty :
    IsClosed segment.toRegion ∧ segment.toRegion.Nonempty ∧
    Within segment.toRegion areaA ∧ II segment.toRegion areaA = ∅ := by
  refine ⟨segment.isClosed_toRegion, ⟨⟨0, 0⟩, ?_⟩, ?_, ?_⟩
  · show (0 : ℝ) ≤ 0 ∧ (0 : ℝ) ≤ 0 ∧ (0 : ℝ) ≤ 0 ∧ (0 : ℝ) ≤ 2
    norm_num
  · exact Rect.within_of_bounds (by norm_num [segment, squareA])
      (by norm_num [segment, squareA]) (by norm_num [segment, squareA])
      (by norm_num [segment, squareA])
  · have hempty : segment.openRegion = ∅ := by
      rw [Set.eq_empty_iff_forall_not_mem]
      rintro p ⟨h₁, h₂, -, -⟩
      simp only [segment] at h₁ h₂
      linarith
    simp only [cell, Stratum.set, Rect.interior_toRegion, hempty, Set.empty_inter]

end

end Geospatial.Examples.NineIntersection
