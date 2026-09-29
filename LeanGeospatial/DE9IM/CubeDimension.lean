import LeanGeospatial.DE9IM.DimensionFunction

/-!
# Dimension by embedded cubes

`HasCube k S`: `S` contains an embedded copy of the cube `[0, 1]ᵏ`, a
continuous injective image of it. `cubeDim n` is the dimension function for
spaces meant to be `n`-dimensional:

- `⊥` on the empty set;
- `n` on a set with interior;
- otherwise the largest `k < n` with `HasCube k S` (every nonempty set has
  `HasCube 0`).

Each clause is topological, so `cubeDim n` is compatible with every
homeomorphism between any two spaces (`cubeDim_compatible`).

The plane's values `F, 0, 1, 2` are the case `n = 2`: `planeDim`, the
dimension function made from `DimValue`, equals `cubeDim 2`
(`planeDim_eq_cubeDim`), because an arc is an embedded `1`-cube. So the
existing matrix is `de9im planeDim` (`matrix_toWithBot`).

In `E3 := EuclideanSpace ℝ (Fin 3)`, `cubeDim 3` takes every value
`⊥, 0, 1, 2, 3` (`Space3`). The upper bounds there, that a segment contains
no embedded square, rest on `not_injOn_square`: the square does not inject
continuously into the line.
-/

namespace Geospatial.DE9IM

open Set

variable {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]

/-- `S` contains an embedded `k`-cube. -/
def HasCube (k : ℕ) (S : Set α) : Prop :=
  ∃ f : (Fin k → ℝ) → α, ContinuousOn f (Icc 0 1) ∧ InjOn f (Icc 0 1) ∧ f '' Icc 0 1 ⊆ S

theorem hasCube_zero_iff {S : Set α} : HasCube 0 S ↔ S.Nonempty := by
  constructor
  · rintro ⟨f, -, -, hf⟩
    exact ⟨f 0, hf ⟨0, ⟨le_rfl, zero_le_one⟩, rfl⟩⟩
  · rintro ⟨p, hp⟩
    exact ⟨fun _ => p, continuousOn_const, fun x _ y _ _ => Subsingleton.elim x y,
      by rintro _ ⟨_, -, rfl⟩; exact hp⟩

theorem HasCube.image {k : ℕ} {S : Set α} (e : α ≃ₜ β) (h : HasCube k S) :
    HasCube k (e '' S) := by
  obtain ⟨f, hc, hi, hf⟩ := h
  refine ⟨e ∘ f, e.continuous.comp_continuousOn hc, e.injective.comp_injOn hi, ?_⟩
  rw [image_comp]
  exact image_mono hf

theorem hasCube_image_iff {k : ℕ} {S : Set α} (e : α ≃ₜ β) : HasCube k (e '' S) ↔ HasCube k S :=
  ⟨fun h => by
    simpa only [image_image, Homeomorph.symm_apply_apply, image_id'] using h.image e.symm,
    HasCube.image e⟩

theorem not_hasCube_of_subsingleton {k : ℕ} (hk : 0 < k) {S : Set α} (hS : S.Subsingleton) :
    ¬ HasCube k S := by
  rintro ⟨f, -, hi, hf⟩
  have h0 : (0 : Fin k → ℝ) ∈ Icc 0 1 := ⟨le_rfl, zero_le_one⟩
  have h1 : (1 : Fin k → ℝ) ∈ Icc 0 1 := ⟨zero_le_one, le_rfl⟩
  have := hi h0 h1 (hS (hf ⟨0, h0, rfl⟩) (hf ⟨1, h1, rfl⟩))
  have := congrFun this ⟨0, hk⟩
  simp at this

/-! ## The cube dimension -/

open Classical in
/-- The dimension of `S` in a space meant to be `n`-dimensional. -/
noncomputable def cubeDim (n : ℕ) : DimensionFunction α where
  dim S := if S = ∅ then ⊥ else if (interior S).Nonempty then (n : WithBot ℕ)
    else ((Nat.findGreatest (fun k => HasCube k S) (n - 1) : ℕ) : WithBot ℕ)
  dim_eq_bot_iff := by
    intro S
    by_cases h : S = ∅
    · simp [h]
    · simp only [h, iff_false]
      split_ifs with h₁
      · exact h₁.elim
      · exact WithBot.coe_ne_bot
      · exact WithBot.coe_ne_bot

open Classical in
theorem cubeDim_dim (n : ℕ) (S : Set α) :
    (cubeDim n : DimensionFunction α).dim S = if S = ∅ then ⊥ else
      if (interior S).Nonempty then (n : WithBot ℕ)
      else ((Nat.findGreatest (fun k => HasCube k S) (n - 1) : ℕ) : WithBot ℕ) := rfl

open Classical in
/-- `cubeDim n` is compatible with every homeomorphism. -/
theorem cubeDim_compatible (n : ℕ) (e : α ≃ₜ β) :
    DimensionCompatible (cubeDim n) (cubeDim n) e := by
  intro S
  have hF : Nat.findGreatest (fun k => HasCube k (e '' S)) (n - 1) =
      Nat.findGreatest (fun k => HasCube k S) (n - 1) := by
    simp only [hasCube_image_iff e]
  simp only [cubeDim_dim, image_eq_empty, interior_image e, image_nonempty, hF]

/-- A set with interior has dimension `n`. -/
theorem cubeDim_of_interior {n : ℕ} {S : Set α} (h : (interior S).Nonempty) :
    (cubeDim n : DimensionFunction α).dim S = n := by
  simp [cubeDim_dim, (h.mono interior_subset).ne_empty, h]

open Classical in
/-- A nonempty set without interior has dimension `k` when it holds a `k`-cube
and no bigger one below `n`. -/
theorem cubeDim_of_cube {n k : ℕ} {S : Set α} (hne : S.Nonempty) (hint : interior S = ∅)
    (hk : k ≤ n - 1) (hc : HasCube k S) (hmax : ∀ j, k < j → j ≤ n - 1 → ¬ HasCube j S) :
    (cubeDim n : DimensionFunction α).dim S = k := by
  simp only [cubeDim_dim, hne.ne_empty, hint, Set.not_nonempty_empty, ↓reduceIte]
  congr 1
  exact Nat.findGreatest_eq_iff.mpr ⟨hk, fun _ => hc, fun j hj hjn => hmax j hj hjn⟩

/-! ## The plane's values are `cubeDim 2` -/

/-- A `DimValue` as a dimension. -/
def DimValue.toWithBot : DimValue → WithBot ℕ
  | .F => ⊥
  | .d0 => 0
  | .d1 => 1
  | .d2 => 2

/-- The plane's dimension function, from `DimValue`. -/
noncomputable def planeDim : DimensionFunction Point2D where
  dim S := (DimValue.of S).toWithBot
  dim_eq_bot_iff := by
    intro S
    rw [← DimValue.of_eq_F_iff]
    cases DimValue.of S <;> simp [DimValue.toWithBot]

/-- `planeDim` is compatible with every homeomorphism of the plane. -/
theorem planeDim_compatible (e : Point2D ≃ₜ Point2D) : DimensionCompatible planeDim planeDim e :=
  fun S => by simp only [planeDim, DimValue.of_image]

/-- The existing matrix of two areas is `de9im planeDim`. -/
theorem matrix_toWithBot (A B : RegularClosedRegion Point2D) (s t : Stratum) :
    (matrix (.area A) (.area B) s t).toWithBot = de9im planeDim (A : Region) B s t := by
  simp only [matrix, Geometry.cell_area_area, de9im, planeDim]

/-- An embedded `1`-cube is an arc. -/
theorem hasCube_one_iff {S : Set α} :
    HasCube 1 S ↔ ∃ f : ℝ → α, ContinuousOn f (Icc 0 1) ∧ InjOn f (Icc 0 1) ∧
      f '' Icc 0 1 ⊆ S := by
  let u : (Fin 1 → ℝ) ≃ₜ ℝ := Homeomorph.funUnique (Fin 1) ℝ
  have hmem : ∀ x : Fin 1 → ℝ, x ∈ Icc (0 : Fin 1 → ℝ) 1 ↔ u x ∈ Icc (0 : ℝ) 1 := by
    intro x
    simp only [mem_Icc, Pi.le_def, Fin.forall_fin_one, Pi.zero_apply, Pi.one_apply, u,
      Homeomorph.funUnique_apply]
    rfl
  have himg : u '' Icc 0 1 = Icc 0 1 := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (hmem x).mp hx
    · intro hy
      exact ⟨u.symm y, (hmem _).mpr (by simpa using hy), by simp⟩
  constructor
  · rintro ⟨f, hc, hi, hf⟩
    refine ⟨f ∘ u.symm, hc.comp u.symm.continuous.continuousOn ?_, hi.comp u.symm.injective.injOn ?_,
      ?_⟩
    · intro y hy
      exact (hmem _).mpr (by simpa using hy)
    · intro y hy
      exact (hmem _).mpr (by simpa using hy)
    · have himg' : u.symm '' Icc 0 1 = Icc 0 1 := by
        rw [← himg]
        simp [image_image]
      rw [image_comp, himg']
      exact hf
  · rintro ⟨g, hc, hi, hg⟩
    refine ⟨g ∘ u, hc.comp u.continuous.continuousOn fun x hx => (hmem x).mp hx,
      hi.comp u.injective.injOn fun x hx => (hmem x).mp hx, ?_⟩
    rw [image_comp, himg]
    exact hg

theorem hasCube_one_iff_hasArc {S : Region} : HasCube 1 S ↔ HasArc S := hasCube_one_iff

/-- The plane's values `F, 0, 1, 2` are `cubeDim 2`. -/
theorem planeDim_eq_cubeDim : planeDim = cubeDim 2 := by
  refine DimensionFunction.ext' fun S => ?_
  have hd := DimValue.of_describes S
  show (DimValue.of S).toWithBot = _
  cases h : DimValue.of S <;> rw [h] at hd
  · rw [(cubeDim 2).dim_eq_bot_iff.mpr hd]
    rfl
  · obtain ⟨hne, hint, harc⟩ := hd
    rw [cubeDim_of_cube hne hint (Nat.zero_le _) (hasCube_zero_iff.mpr hne)]
    · rfl
    · intro j hj hj1
      obtain rfl : j = 1 := by omega
      exact fun hc => harc (hasCube_one_iff_hasArc.mp hc)
  · obtain ⟨hint, harc⟩ := hd
    rw [cubeDim_of_cube harc.nonempty hint le_rfl (hasCube_one_iff_hasArc.mpr harc)]
    · rfl
    · intro j hj hj1
      omega
  · rw [cubeDim_of_interior hd]
    rfl

end Geospatial.DE9IM
