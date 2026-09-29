import LeanGeospatial.RCC8
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Order.Interval.Set.Infinite

/-!
# Areas of the line made of unit cells

For a finite set `S` of integers, `cells S` is the union of the unit cells
`[i, i + 1]`, `i ∈ S`. It is an area of the line (`area S`). Between two such
areas every building block of RCC8 is a condition on the integer sets:

| Fact | Condition |
| --- | --- |
| the areas meet | some `i ∈ S`, `j ∈ T` with `j ∈ {i - 1, i, i + 1}` (`intersects_cells_iff`) |
| the interiors meet | `S ∩ T` nonempty (`intersects_interior_cells_iff`) |
| one within the other | `S ⊆ T` (`cells_subset_cells_iff`) |
| one within the other's interior | `i - 1, i, i + 1 ∈ T` for every `i ∈ S` (`cells_subset_interior_iff`) |

`cellRel S T` runs RCC8's decision tree on those conditions, so it is
computable, and it is the relation between the areas (`cellRel_holds`).

The conditions are proved for any set of integers `P`, finite or not, as
`cellsOf P`; `cells S` is the finite case. Infinite sets arise on the circle,
whose cells lift to periodic sets of the line (`Circle.lean`).
-/

namespace Geospatial.Line

open Set Geospatial RCC8

/-- The union of the unit cells `[i, i + 1]` for `i ∈ P`. -/
def cellsOf (P : Set ℤ) : Set ℝ := ⋃ i ∈ P, Icc (i : ℝ) (i + 1)

/-- The union of the unit cells `[i, i + 1]` for `i ∈ S`, a finite set. -/
abbrev cells (S : Finset ℤ) : Set ℝ := cellsOf (S : Set ℤ)

variable {S T : Finset ℤ} {P Q : Set ℤ}

theorem mem_cellsOf {x : ℝ} : x ∈ cellsOf P ↔ ∃ i ∈ P, (i : ℝ) ≤ x ∧ x ≤ i + 1 := by
  simp only [cellsOf, mem_iUnion, mem_Icc, exists_prop]

theorem mem_cells {x : ℝ} : x ∈ cells S ↔ ∃ i ∈ S, (i : ℝ) ≤ x ∧ x ≤ i + 1 := by
  simp only [cells, mem_cellsOf, Finset.mem_coe]

theorem isClosed_cells : IsClosed (cells S) := by
  simp only [cells, cellsOf, Finset.mem_coe]
  exact isClosed_biUnion_finset fun _ _ => isClosed_Icc

/-- A point strictly inside the cell `j` lies in `cellsOf Q` only if `j ∈ Q`. -/
theorem mem_of_lt_of_lt {x : ℝ} {j : ℤ} (hx : x ∈ cellsOf Q) (h₁ : (j : ℝ) < x)
    (h₂ : x < j + 1) : j ∈ Q := by
  obtain ⟨i, hi, hix, hxi⟩ := mem_cellsOf.mp hx
  have hji : j < i + 1 := by exact_mod_cast h₁.trans_le hxi
  have hij : i < j + 1 := by exact_mod_cast hix.trans_lt h₂
  obtain rfl : j = i := by omega
  exact hi

/-- The open cell `(i, i + 1)` lies in the interior of `cellsOf P` when `i ∈ P`. -/
theorem Ioo_subset_interior {i : ℤ} (hi : i ∈ P) : Ioo (i : ℝ) (i + 1) ⊆ interior (cellsOf P) :=
  interior_maximal (fun _ hy => mem_cellsOf.mpr ⟨i, hi, hy.1.le, hy.2.le⟩) isOpen_Ioo

theorem isCompact_cells : IsCompact (cells S) := by
  simp only [cells, cellsOf, Finset.mem_coe]
  exact S.isCompact_biUnion fun _ _ => isCompact_Icc

/-- Consecutive cells make one interval. -/
theorem cells_Ico {a b : ℤ} (hab : a < b) : cells (Finset.Ico a b) = Icc (a : ℝ) b := by
  ext y
  rw [mem_cells]
  constructor
  · rintro ⟨i, hi, h₁, h₂⟩
    rw [Finset.mem_Ico] at hi
    have ha : (a : ℝ) ≤ i := by exact_mod_cast hi.1
    have hb : (i : ℝ) + 1 ≤ b := by exact_mod_cast hi.2
    exact ⟨ha.trans h₁, h₂.trans hb⟩
  · rintro ⟨h₁, h₂⟩
    rcases h₂.lt_or_eq with h | h
    · refine ⟨⌊y⌋, Finset.mem_Ico.mpr ⟨Int.le_floor.mpr h₁, Int.floor_lt.mpr h⟩,
        Int.floor_le y, (Int.lt_floor_add_one y).le⟩
    · refine ⟨b - 1, Finset.mem_Ico.mpr ⟨by omega, by omega⟩, ?_, ?_⟩ <;> push_cast <;> linarith

theorem closure_interior_cells : closure (interior (cells S)) = cells S := by
  apply Subset.antisymm (closure_minimal interior_subset isClosed_cells)
  intro x hx
  obtain ⟨i, hi, h₁, h₂⟩ := mem_cells.mp hx
  have hcl : closure (Ioo (i : ℝ) (i + 1)) = Icc (i : ℝ) (i + 1) :=
    closure_Ioo (by linarith)
  exact closure_mono (Ioo_subset_interior (P := (S : Set ℤ)) hi) (hcl ▸ ⟨h₁, h₂⟩)

/-- `cells S` as an area of the line. -/
def area (S : Finset ℤ) : RegularClosedRegion ℝ := ⟨cells S, closure_interior_cells⟩

@[simp] theorem coe_area : ((area S : RegularClosedRegion ℝ) : Set ℝ) = cells S := rfl

theorem area_nonempty (hS : S.Nonempty) : ((area S : RegularClosedRegion ℝ) : Set ℝ).Nonempty := by
  obtain ⟨i, hi⟩ := hS
  exact ⟨i, mem_cells.mpr ⟨i, hi, le_rfl, by linarith⟩⟩

/-! ## The building blocks as conditions on integer sets -/

theorem cells_subset_cells_iff : cellsOf P ⊆ cellsOf Q ↔ P ⊆ Q := by
  constructor
  · intro h i hi
    exact mem_of_lt_of_lt (h (mem_cellsOf.mpr ⟨i, hi, by linarith, by linarith⟩))
      (show (i : ℝ) < i + 1 / 2 by linarith) (show (i : ℝ) + 1 / 2 < i + 1 by linarith)
  · intro h x hx
    obtain ⟨i, hi, h₁, h₂⟩ := mem_cellsOf.mp hx
    exact mem_cellsOf.mpr ⟨i, h hi, h₁, h₂⟩

theorem cells_eq_cells_iff : cellsOf P = cellsOf Q ↔ P = Q :=
  ⟨fun h => Set.Subset.antisymm (cells_subset_cells_iff.mp h.le)
    (cells_subset_cells_iff.mp h.ge), fun h => h ▸ rfl⟩

theorem intersects_cells_iff :
    Intersects (cellsOf P) (cellsOf Q) ↔ ∃ i ∈ P, ∃ j ∈ Q, j = i - 1 ∨ j = i ∨ j = i + 1 := by
  constructor
  · rintro ⟨x, hxS, hxT⟩
    obtain ⟨i, hi, h₁, h₂⟩ := mem_cellsOf.mp hxS
    obtain ⟨j, hj, h₃, h₄⟩ := mem_cellsOf.mp hxT
    have hij : i ≤ j + 1 := by exact_mod_cast h₁.trans h₄
    have hji : j ≤ i + 1 := by exact_mod_cast h₃.trans h₂
    exact ⟨i, hi, j, hj, by omega⟩
  · rintro ⟨i, hi, j, hj, h | h | h⟩
    · refine ⟨i, mem_cellsOf.mpr ⟨i, hi, le_rfl, by linarith⟩, mem_cellsOf.mpr ⟨j, hj, ?_, ?_⟩⟩ <;>
        · subst h; push_cast; linarith
    · exact ⟨i, mem_cellsOf.mpr ⟨i, hi, le_rfl, by linarith⟩,
        mem_cellsOf.mpr ⟨j, hj, by rw [h], by rw [h]; linarith⟩⟩
    · refine ⟨i + 1, mem_cellsOf.mpr ⟨i, hi, by linarith, le_rfl⟩, mem_cellsOf.mpr ⟨j, hj, ?_, ?_⟩⟩ <;>
        · subst h; push_cast; linarith

theorem intersects_interior_cells_iff :
    Intersects (interior (cellsOf P)) (interior (cellsOf Q)) ↔ (P ∩ Q).Nonempty := by
  constructor
  · rintro ⟨x, hxS, hxT⟩
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp (isOpen_interior.inter isOpen_interior) x ⟨hxS, hxT⟩
    rw [Real.ball_eq_Ioo] at hball
    set a := x - ε with ha_def
    set j := ⌊a⌋
    set m := min (x + ε) ((j : ℝ) + 1) with hm_def
    have hm₁ : m ≤ x + ε := min_le_left _ _
    have hm₂ : m ≤ (j : ℝ) + 1 := min_le_right _ _
    have ha : a < m := lt_min (by linarith) (Int.lt_floor_add_one a)
    set y := (a + m) / 2 with hy_def
    have hy : y ∈ interior (cellsOf P) ∩ interior (cellsOf Q) :=
      hball ⟨by linarith, by linarith⟩
    have hj₁ : (j : ℝ) < y := (Int.floor_le a).trans_lt (by linarith)
    have hj₂ : y < j + 1 := by linarith
    exact ⟨j, mem_of_lt_of_lt (interior_subset hy.1) hj₁ hj₂,
      mem_of_lt_of_lt (interior_subset hy.2) hj₁ hj₂⟩
  · rintro ⟨i, hi⟩
    rw [Set.mem_inter_iff] at hi
    have hmem : (i : ℝ) + 1 / 2 ∈ Ioo (i : ℝ) (i + 1) := ⟨by linarith, by linarith⟩
    exact ⟨_, Ioo_subset_interior hi.1 hmem, Ioo_subset_interior hi.2 hmem⟩

/-- An integer point in the interior of `cellsOf Q` has both of its cells in `T`. -/
theorem mem_of_int_mem_interior {n : ℤ} (h : (n : ℝ) ∈ interior (cellsOf Q)) :
    n - 1 ∈ Q ∧ n ∈ Q := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp h)
  rw [Real.ball_eq_Ioo] at hball
  set δ := min ε 1 / 2 with hδ_def
  have hmin₁ : min ε 1 ≤ 1 := min_le_right ε 1
  have hmin₂ : min ε 1 ≤ ε := min_le_left ε 1
  have hmin₀ : 0 < min ε 1 := lt_min hε one_pos
  have hδ : 0 < δ := by linarith
  have hδ₁ : δ < 1 := by linarith
  have hδε : δ < ε := by linarith
  constructor
  · refine mem_of_lt_of_lt (x := n - δ) (hball ⟨by linarith, by linarith⟩) ?_ ?_ <;>
      push_cast <;> linarith
  · exact mem_of_lt_of_lt (x := n + δ) (hball ⟨by linarith, by linarith⟩) (by linarith)
      (by linarith)

theorem cells_subset_interior_iff :
    cellsOf P ⊆ interior (cellsOf Q) ↔ ∀ i ∈ P, i - 1 ∈ Q ∧ i ∈ Q ∧ i + 1 ∈ Q := by
  constructor
  · intro h i hi
    have h₀ := mem_of_int_mem_interior (h (mem_cellsOf.mpr ⟨i, hi, le_rfl, by linarith⟩))
    have h₁ := mem_of_int_mem_interior (n := i + 1)
      (by push_cast; exact h (mem_cellsOf.mpr ⟨i, hi, by linarith, le_rfl⟩))
    exact ⟨h₀.1, h₀.2, h₁.2⟩
  · intro h x hx
    obtain ⟨i, hi, h₁, h₂⟩ := mem_cellsOf.mp hx
    obtain ⟨hl, hm, hr⟩ := h i hi
    have hsub : Ioo ((i : ℝ) - 1) (i + 2) ⊆ cellsOf Q := by
      intro y hy
      rcases le_or_gt y i with hyi | hyi
      · exact mem_cellsOf.mpr ⟨i - 1, hl, by push_cast; linarith [hy.1], by push_cast; linarith⟩
      rcases le_or_gt y (i + 1) with hyi' | hyi'
      · exact mem_cellsOf.mpr ⟨i, hm, hyi.le, hyi'⟩
      · exact mem_cellsOf.mpr ⟨i + 1, hr, by push_cast; linarith, by push_cast; linarith [hy.2]⟩
    exact interior_maximal hsub isOpen_Ioo ⟨by linarith, by linarith⟩

/-! ## The relation, computed -/

/-- RCC8's decision tree run on the integer conditions. -/
def cellRel (S T : Finset ℤ) : Relation :=
  if ¬ (∃ i ∈ S, ∃ j ∈ T, j = i - 1 ∨ j = i ∨ j = i + 1) then .dc
  else if ¬ (S ∩ T).Nonempty then .ec
  else if S = T then .eq
  else if S ⊆ T then
    (if ∀ i ∈ S, i - 1 ∈ T ∧ i ∈ T ∧ i + 1 ∈ T then .ntpp else .tpp)
  else if T ⊆ S then
    (if ∀ i ∈ T, i - 1 ∈ S ∧ i ∈ S ∧ i + 1 ∈ S then .ntppi else .tppi)
  else .po

/-- The relation the decision tree computes is the one that holds. -/
theorem cellRel_holds (hS : S.Nonempty) (hT : T.Nonempty) :
    (cellRel S T).holds (area S) (area T) := by
  obtain ⟨r, hr⟩ := exists_relation (area S) (area T) (area_nonempty hS) (area_nonempty hT)
  have hc := classify_eq_of_holds (area S) (area T) (area_nonempty hS) (area_nonempty hT) hr
  have : cellRel S T = classify (area S) (area T) := by
    simp only [cellRel, classify, coe_area, cells, intersects_cells_iff,
      intersects_interior_cells_iff, cells_eq_cells_iff, Within, cells_subset_cells_iff,
      cells_subset_interior_iff, Finset.mem_coe, Finset.coe_subset, ← Finset.coe_inter,
      Finset.coe_nonempty, Finset.coe_inj]
  rw [this, hc]
  exact hr

end Geospatial.Line
