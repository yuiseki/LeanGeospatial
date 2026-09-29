import LeanGeospatial.Line.Cells
import Mathlib.Topology.Instances.AddCircle.Real

/-!
# Areas of the circle made of cells

The circle here is `AddCircle 6`, the line wrapped with period `6`, so that it
is cut into six unit cells. For a finite set `S` of integers, `area S` is the
image of the line's `cells S` under the projection `proj : ℝ → AddCircle 6`.

The projection is continuous, open and onto. So a set of the circle and its
preimage on the line have the same relations: meeting, containment and
equality are read off preimages, and the preimage of an interior is the
interior of the preimage. The preimage of `area S` is the periodic union of
cells over the integers congruent mod `6` to a member of `S`
(`preimage_area`), and on those `Line/Cells.lean` computes everything. Reduced
mod `6`, the conditions are finite (`cycRel`), and `cycRel_holds` says the
relation they compute is the one that holds.
-/

namespace Geospatial.Cyc

open Set Geospatial RCC8 Line

instance : Fact ((0 : ℝ) < 6) := ⟨by norm_num⟩

/-- The circle cut into six unit cells. -/
abbrev C6 := AddCircle (6 : ℝ)

/-- Wrapping the line onto the circle. -/
def proj (x : ℝ) : C6 := (x : C6)

theorem continuous_proj : Continuous proj := AddCircle.continuous_mk' 6

theorem isOpenMap_proj : IsOpenMap proj := QuotientAddGroup.isOpenMap_coe

theorem proj_surjective : Function.Surjective proj := QuotientAddGroup.mk_surjective

theorem proj_eq_proj_iff {x y : ℝ} : proj x = proj y ↔ ∃ k : ℤ, y = x + 6 * k := by
  unfold proj
  rw [QuotientAddGroup.eq, AddSubgroup.mem_zmultiples_iff]
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k, by rw [zsmul_eq_mul] at hk; linarith⟩
  · rintro ⟨k, hk⟩
    exact ⟨k, by rw [zsmul_eq_mul]; linarith⟩

/-! ## Areas -/

/-- The image of the line's cells `S` on the circle. -/
def area (S : Finset ℤ) : RegularClosedRegion C6 where
  carrier := proj '' cells S
  closure_interior_eq' := by
    apply Subset.antisymm
    · exact closure_minimal interior_subset (isCompact_cells.image continuous_proj).isClosed
    · rintro _ ⟨x, hx, rfl⟩
      obtain ⟨i, hi, h₁, h₂⟩ := mem_cells.mp hx
      have hsub : proj '' Ioo (i : ℝ) (i + 1) ⊆ interior (proj '' cells S) :=
        interior_maximal (image_mono fun y hy => mem_cells.mpr ⟨i, hi, hy.1.le, hy.2.le⟩)
          (isOpenMap_proj _ isOpen_Ioo)
      have hx' : x ∈ closure (Ioo (i : ℝ) (i + 1)) := by
        rw [closure_Ioo (by linarith)]
        exact ⟨h₁, h₂⟩
      exact closure_mono hsub (image_closure_subset_closure_image continuous_proj ⟨x, hx', rfl⟩)

@[simp] theorem coe_area (S : Finset ℤ) :
    ((area S : RegularClosedRegion C6) : Set C6) = proj '' cells S := rfl

theorem area_nonempty {S : Finset ℤ} (hS : S.Nonempty) : ((area S : Set C6)).Nonempty :=
  (Line.area_nonempty hS).image proj

/-- An arc of consecutive cells is connected. -/
theorem isConnected_area_Ico {a b : ℤ} (hab : a < b) :
    IsConnected ((area (Finset.Ico a b) : Set C6)) := by
  rw [coe_area, cells_Ico hab]
  exact (isConnected_Icc (by exact_mod_cast hab.le)).image proj continuous_proj.continuousOn

/-! ## Reading relations off preimages -/

section Preimage

variable {X Y : Set C6}

theorem intersects_iff_preimage :
    Intersects X Y ↔ Intersects (proj ⁻¹' X) (proj ⁻¹' Y) := by
  unfold Intersects
  constructor
  · rintro ⟨z, hzX, hzY⟩
    obtain ⟨x, rfl⟩ := proj_surjective z
    exact ⟨x, hzX, hzY⟩
  · rintro ⟨x, hx⟩
    exact ⟨proj x, hx⟩

theorem subset_iff_preimage : X ⊆ Y ↔ proj ⁻¹' X ⊆ proj ⁻¹' Y :=
  (preimage_subset_preimage_iff (by rw [proj_surjective.range_eq]; exact subset_univ _)).symm

theorem eq_iff_preimage : X = Y ↔ proj ⁻¹' X = proj ⁻¹' Y :=
  (preimage_injective.mpr proj_surjective).eq_iff.symm

theorem preimage_interior (X : Set C6) : proj ⁻¹' interior X = interior (proj ⁻¹' X) :=
  isOpenMap_proj.preimage_interior_eq_interior_preimage continuous_proj X

end Preimage

/-! ## Preimages of areas -/

/-- Residues mod `6`. -/
def norm (S : Finset ℤ) : Finset ℤ := S.image (· % 6)

/-- The integers whose residue mod `6` is in `T`. -/
def liftR (T : Finset ℤ) : Set ℤ := {n | n % 6 ∈ T}

theorem mem_norm_mod {S : Finset ℤ} {a : ℤ} (ha : a ∈ norm S) : a % 6 = a := by
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp ha
  omega

/-- The preimage of an area is the periodic union of its cells. -/
theorem preimage_area (S : Finset ℤ) :
    proj ⁻¹' (area S : Set C6) = cellsOf (liftR (norm S)) := by
  ext y
  simp only [coe_area, mem_preimage, mem_image, mem_cellsOf]
  constructor
  · rintro ⟨x, ⟨i, hi, h₁, h₂⟩, hxy⟩
    obtain ⟨k, hk⟩ := proj_eq_proj_iff.mp hxy
    refine ⟨i + 6 * k, Finset.mem_image.mpr ⟨i, hi, by omega⟩, ?_, ?_⟩ <;> push_cast <;> linarith
  · rintro ⟨n, hn, h₁, h₂⟩
    obtain ⟨i, hi, hin⟩ := Finset.mem_image.mp hn
    have hk : n = i + 6 * ((n - i) / 6) := by omega
    have hkR : (n : ℝ) = i + 6 * (((n - i) / 6 : ℤ) : ℝ) := by exact_mod_cast hk
    refine ⟨y - 6 * (((n - i) / 6 : ℤ) : ℝ), ⟨i, hi, by linarith, by linarith⟩,
      proj_eq_proj_iff.mpr ⟨(n - i) / 6, by ring⟩⟩

/-! ## The periodic conditions, reduced mod 6 -/

variable {S T : Finset ℤ}

theorem adj_liftR_iff :
    (∃ i ∈ liftR (norm S), ∃ j ∈ liftR (norm T), j = i - 1 ∨ j = i ∨ j = i + 1) ↔
      ∃ i ∈ norm S, ∃ j ∈ norm T, j = (i - 1) % 6 ∨ j = i ∨ j = (i + 1) % 6 := by
  constructor
  · rintro ⟨i, hi, j, hj, h⟩
    exact ⟨i % 6, hi, j % 6, hj, by omega⟩
  · rintro ⟨i, hi, j, hj, h⟩
    have hi6 := mem_norm_mod hi
    have hj6 := mem_norm_mod hj
    rcases h with h | h | h
    · exact ⟨i, show i % 6 ∈ norm S by rw [hi6]; exact hi, i - 1,
        show (i - 1) % 6 ∈ norm T by rw [← h]; exact hj, Or.inl rfl⟩
    · exact ⟨i, show i % 6 ∈ norm S by rw [hi6]; exact hi, i,
        show i % 6 ∈ norm T by rw [hi6, ← h]; exact hj, Or.inr (Or.inl rfl)⟩
    · exact ⟨i, show i % 6 ∈ norm S by rw [hi6]; exact hi, i + 1,
        show (i + 1) % 6 ∈ norm T by rw [← h]; exact hj, Or.inr (Or.inr rfl)⟩

theorem inter_liftR_nonempty_iff :
    (liftR (norm S) ∩ liftR (norm T)).Nonempty ↔ (norm S ∩ norm T).Nonempty := by
  constructor
  · rintro ⟨n, hnS, hnT⟩
    exact ⟨n % 6, Finset.mem_inter.mpr ⟨hnS, hnT⟩⟩
  · rintro ⟨a, ha⟩
    rw [Finset.mem_inter] at ha
    have h6 := mem_norm_mod ha.1
    exact ⟨a, show a % 6 ∈ norm S by rw [h6]; exact ha.1, show a % 6 ∈ norm T by rw [h6]; exact ha.2⟩

theorem liftR_subset_iff : liftR (norm S) ⊆ liftR (norm T) ↔ norm S ⊆ norm T := by
  constructor
  · intro h a ha
    have h6 := mem_norm_mod ha
    have h' : a % 6 ∈ norm T := h (show a % 6 ∈ norm S by rw [h6]; exact ha)
    rwa [h6] at h'
  · intro h n hn
    exact h hn

theorem liftR_eq_iff : liftR (norm S) = liftR (norm T) ↔ norm S = norm T :=
  ⟨fun h => Finset.Subset.antisymm (liftR_subset_iff.mp h.le) (liftR_subset_iff.mp h.ge),
    fun h => h ▸ rfl⟩

theorem nbhd_liftR_iff :
    (∀ i ∈ liftR (norm S), i - 1 ∈ liftR (norm T) ∧ i ∈ liftR (norm T) ∧
      i + 1 ∈ liftR (norm T)) ↔
      ∀ i ∈ norm S, (i - 1) % 6 ∈ norm T ∧ i ∈ norm T ∧ (i + 1) % 6 ∈ norm T := by
  constructor
  · intro h i hi
    have h6 := mem_norm_mod hi
    obtain ⟨h₁, h₂, h₃⟩ := h i (show i % 6 ∈ norm S by rw [h6]; exact hi)
    have h₂' : i % 6 ∈ norm T := h₂
    exact ⟨h₁, by rwa [h6] at h₂', h₃⟩
  · intro h n hn
    obtain ⟨h₁, h₂, h₃⟩ := h (n % 6) hn
    refine ⟨?_, h₂, ?_⟩
    · show (n - 1) % 6 ∈ norm T
      rwa [show (n - 1) % 6 = (n % 6 - 1) % 6 by omega]
    · show (n + 1) % 6 ∈ norm T
      rwa [show (n + 1) % 6 = (n % 6 + 1) % 6 by omega]

/-! ## The relation, computed -/

/-- RCC8's decision tree on residue sets, with neighbours taken mod `6`. -/
def cycRel (A B : Finset ℤ) : Relation :=
  if ¬ (∃ i ∈ A, ∃ j ∈ B, j = (i - 1) % 6 ∨ j = i ∨ j = (i + 1) % 6) then .dc
  else if ¬ (A ∩ B).Nonempty then .ec
  else if A = B then .eq
  else if A ⊆ B then
    (if ∀ i ∈ A, (i - 1) % 6 ∈ B ∧ i ∈ B ∧ (i + 1) % 6 ∈ B then .ntpp else .tpp)
  else if B ⊆ A then
    (if ∀ i ∈ B, (i - 1) % 6 ∈ A ∧ i ∈ A ∧ (i + 1) % 6 ∈ A then .ntppi else .tppi)
  else .po

/-- The relation the decision tree computes is the one that holds. -/
theorem cycRel_holds (hS : S.Nonempty) (hT : T.Nonempty) :
    (cycRel (norm S) (norm T)).holds (area S) (area T) := by
  obtain ⟨r, hr⟩ := exists_relation (area S) (area T) (area_nonempty hS) (area_nonempty hT)
  have hc := classify_eq_of_holds (area S) (area T) (area_nonempty hS) (area_nonempty hT) hr
  have : cycRel (norm S) (norm T) = classify (area S) (area T) := by
    simp only [cycRel, classify, intersects_iff_preimage, Within, subset_iff_preimage, eq_iff_preimage,
      preimage_interior, preimage_area, intersects_cells_iff, adj_liftR_iff,
      intersects_interior_cells_iff, inter_liftR_nonempty_iff, cells_eq_cells_iff,
      liftR_eq_iff, cells_subset_cells_iff, liftR_subset_iff, cells_subset_interior_iff,
      nbhd_liftR_iff]
  rw [this, hc]
  exact hr

end Geospatial.Cyc
