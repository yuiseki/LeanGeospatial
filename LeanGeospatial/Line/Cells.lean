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
-/

namespace Geospatial.Line

open Set Geospatial RCC8

/-- The union of the unit cells `[i, i + 1]` for `i ∈ S`. -/
def cells (S : Finset ℤ) : Set ℝ := ⋃ i ∈ S, Icc (i : ℝ) (i + 1)

variable {S T : Finset ℤ}

theorem mem_cells {x : ℝ} : x ∈ cells S ↔ ∃ i ∈ S, (i : ℝ) ≤ x ∧ x ≤ i + 1 := by
  simp only [cells, mem_iUnion, mem_Icc, exists_prop]

theorem isClosed_cells : IsClosed (cells S) :=
  isClosed_biUnion_finset fun _ _ => isClosed_Icc

/-- A point strictly inside the cell `j` lies in `cells T` only if `j ∈ T`. -/
theorem mem_of_lt_of_lt {x : ℝ} {j : ℤ} (hx : x ∈ cells T) (h₁ : (j : ℝ) < x)
    (h₂ : x < j + 1) : j ∈ T := by
  obtain ⟨i, hi, hix, hxi⟩ := mem_cells.mp hx
  have hji : j < i + 1 := by exact_mod_cast h₁.trans_le hxi
  have hij : i < j + 1 := by exact_mod_cast hix.trans_lt h₂
  obtain rfl : j = i := by omega
  exact hi

/-- The open cell `(i, i + 1)` lies in the interior of `cells S` when `i ∈ S`. -/
theorem Ioo_subset_interior {i : ℤ} (hi : i ∈ S) : Ioo (i : ℝ) (i + 1) ⊆ interior (cells S) :=
  interior_maximal (fun _ hy => mem_cells.mpr ⟨i, hi, hy.1.le, hy.2.le⟩) isOpen_Ioo

theorem closure_interior_cells : closure (interior (cells S)) = cells S := by
  apply Subset.antisymm (closure_minimal interior_subset isClosed_cells)
  intro x hx
  obtain ⟨i, hi, h₁, h₂⟩ := mem_cells.mp hx
  have hcl : closure (Ioo (i : ℝ) (i + 1)) = Icc (i : ℝ) (i + 1) :=
    closure_Ioo (by linarith)
  exact closure_mono (Ioo_subset_interior hi) (hcl ▸ ⟨h₁, h₂⟩)

/-- `cells S` as an area of the line. -/
def area (S : Finset ℤ) : RegularClosedRegion ℝ := ⟨cells S, closure_interior_cells⟩

@[simp] theorem coe_area : ((area S : RegularClosedRegion ℝ) : Set ℝ) = cells S := rfl

theorem area_nonempty (hS : S.Nonempty) : ((area S : RegularClosedRegion ℝ) : Set ℝ).Nonempty := by
  obtain ⟨i, hi⟩ := hS
  exact ⟨i, mem_cells.mpr ⟨i, hi, le_rfl, by linarith⟩⟩

/-! ## The building blocks as conditions on integer sets -/

theorem cells_subset_cells_iff : cells S ⊆ cells T ↔ S ⊆ T := by
  constructor
  · intro h i hi
    exact mem_of_lt_of_lt (h (mem_cells.mpr ⟨i, hi, by linarith, by linarith⟩))
      (show (i : ℝ) < i + 1 / 2 by linarith) (show (i : ℝ) + 1 / 2 < i + 1 by linarith)
  · intro h x hx
    obtain ⟨i, hi, h₁, h₂⟩ := mem_cells.mp hx
    exact mem_cells.mpr ⟨i, h hi, h₁, h₂⟩

theorem cells_eq_cells_iff : cells S = cells T ↔ S = T :=
  ⟨fun h => Finset.Subset.antisymm (cells_subset_cells_iff.mp h.le)
    (cells_subset_cells_iff.mp h.ge), fun h => h ▸ rfl⟩

theorem intersects_cells_iff :
    Intersects (cells S) (cells T) ↔ ∃ i ∈ S, ∃ j ∈ T, j = i - 1 ∨ j = i ∨ j = i + 1 := by
  constructor
  · rintro ⟨x, hxS, hxT⟩
    obtain ⟨i, hi, h₁, h₂⟩ := mem_cells.mp hxS
    obtain ⟨j, hj, h₃, h₄⟩ := mem_cells.mp hxT
    have hij : i ≤ j + 1 := by exact_mod_cast h₁.trans h₄
    have hji : j ≤ i + 1 := by exact_mod_cast h₃.trans h₂
    exact ⟨i, hi, j, hj, by omega⟩
  · rintro ⟨i, hi, j, hj, h | h | h⟩
    · refine ⟨i, mem_cells.mpr ⟨i, hi, le_rfl, by linarith⟩, mem_cells.mpr ⟨j, hj, ?_, ?_⟩⟩ <;>
        · subst h; push_cast; linarith
    · exact ⟨i, mem_cells.mpr ⟨i, hi, le_rfl, by linarith⟩,
        mem_cells.mpr ⟨j, hj, by rw [h], by rw [h]; linarith⟩⟩
    · refine ⟨i + 1, mem_cells.mpr ⟨i, hi, by linarith, le_rfl⟩, mem_cells.mpr ⟨j, hj, ?_, ?_⟩⟩ <;>
        · subst h; push_cast; linarith

theorem intersects_interior_cells_iff :
    Intersects (interior (cells S)) (interior (cells T)) ↔ (S ∩ T).Nonempty := by
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
    have hy : y ∈ interior (cells S) ∩ interior (cells T) :=
      hball ⟨by linarith, by linarith⟩
    have hj₁ : (j : ℝ) < y := (Int.floor_le a).trans_lt (by linarith)
    have hj₂ : y < j + 1 := by linarith
    exact ⟨j, Finset.mem_inter.mpr ⟨mem_of_lt_of_lt (interior_subset hy.1) hj₁ hj₂,
      mem_of_lt_of_lt (interior_subset hy.2) hj₁ hj₂⟩⟩
  · rintro ⟨i, hi⟩
    rw [Finset.mem_inter] at hi
    have hmem : (i : ℝ) + 1 / 2 ∈ Ioo (i : ℝ) (i + 1) := ⟨by linarith, by linarith⟩
    exact ⟨_, Ioo_subset_interior hi.1 hmem, Ioo_subset_interior hi.2 hmem⟩

/-- An integer point in the interior of `cells T` has both of its cells in `T`. -/
theorem mem_of_int_mem_interior {n : ℤ} (h : (n : ℝ) ∈ interior (cells T)) :
    n - 1 ∈ T ∧ n ∈ T := by
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
    cells S ⊆ interior (cells T) ↔ ∀ i ∈ S, i - 1 ∈ T ∧ i ∈ T ∧ i + 1 ∈ T := by
  constructor
  · intro h i hi
    have h₀ := mem_of_int_mem_interior (h (mem_cells.mpr ⟨i, hi, le_rfl, by linarith⟩))
    have h₁ := mem_of_int_mem_interior (n := i + 1)
      (by push_cast; exact h (mem_cells.mpr ⟨i, hi, by linarith, le_rfl⟩))
    exact ⟨h₀.1, h₀.2, h₁.2⟩
  · intro h x hx
    obtain ⟨i, hi, h₁, h₂⟩ := mem_cells.mp hx
    obtain ⟨hl, hm, hr⟩ := h i hi
    have hsub : Ioo ((i : ℝ) - 1) (i + 2) ⊆ cells T := by
      intro y hy
      rcases le_or_gt y i with hyi | hyi
      · exact mem_cells.mpr ⟨i - 1, hl, by push_cast; linarith [hy.1], by push_cast; linarith⟩
      rcases le_or_gt y (i + 1) with hyi' | hyi'
      · exact mem_cells.mpr ⟨i, hm, hyi.le, hyi'⟩
      · exact mem_cells.mpr ⟨i + 1, hr, by push_cast; linarith, by push_cast; linarith [hy.2]⟩
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
    simp only [cellRel, classify, coe_area, intersects_cells_iff, intersects_interior_cells_iff,
      cells_eq_cells_iff, Within, cells_subset_cells_iff, cells_subset_interior_iff]
  rw [this, hc]
  exact hr

end Geospatial.Line
