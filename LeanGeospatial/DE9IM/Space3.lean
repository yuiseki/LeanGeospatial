import LeanGeospatial.DE9IM.CubeDimension

/-!
# `⊥, 0, 1, 2, 3` in space

In `E3 := EuclideanSpace ℝ (Fin 3)`, `cubeDim 3` gives the empty set `⊥`, a
point `0`, a segment `1`, a flat square `2` and a ball `3`. The two middle
values need an upper bound as well as a cube: a segment contains no embedded
square. That rests on `not_injOn_square`: two paths join opposite corners of
the square and meet only there; a continuous injective map to the line would
send both across the midpoint of their end values, at two different points.
-/

namespace Geospatial.DE9IM

open Set

/-! ## The square does not inject into the line -/

/-- The points of the unit square with coordinates `x, y`. -/
def sq (x y : ℝ) : Fin 2 → ℝ := ![x, y]

theorem sq_mem {x y : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 1) :
    sq x y ∈ Icc (0 : Fin 2 → ℝ) 1 := by
  simp only [mem_Icc, Pi.le_def, Fin.forall_fin_two, sq, Matrix.cons_val_zero,
    Matrix.cons_val_one, Pi.zero_apply, Pi.one_apply]
  exact ⟨⟨hx.1, hy.1⟩, ⟨hx.2, hy.2⟩⟩

theorem continuous_sq_left (y : ℝ) : Continuous fun x => sq x y :=
  continuous_pi fun i => by fin_cases i <;> simp [sq] <;> fun_prop

theorem continuous_sq_right (x : ℝ) : Continuous fun y => sq x y :=
  continuous_pi fun i => by fin_cases i <;> simp [sq] <;> fun_prop

/-- A continuous map from the square to the line is never injective. -/
theorem not_injOn_square {g : (Fin 2 → ℝ) → ℝ} (hc : ContinuousOn g (Icc 0 1)) :
    ¬ InjOn g (Icc 0 1) := by
  intro hi
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have h1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  -- two paths from `sq 0 0` to `sq 1 1`
  set L₁ := (fun t => sq t 0) '' Icc 0 1 ∪ (fun t => sq 1 t) '' Icc 0 1 with hL₁
  set L₂ := (fun t => sq 0 t) '' Icc 0 1 ∪ (fun t => sq t 1) '' Icc 0 1 with hL₂
  have sub₁ : L₁ ⊆ Icc 0 1 := by
    rintro _ (⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩)
    · exact sq_mem ht h0
    · exact sq_mem h1 ht
  have sub₂ : L₂ ⊆ Icc 0 1 := by
    rintro _ (⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩)
    · exact sq_mem h0 ht
    · exact sq_mem ht h1
  have c₁ : IsPreconnected L₁ :=
    IsPreconnected.union (sq 1 0) (⟨1, h1, rfl⟩) (⟨0, h0, rfl⟩)
      (isPreconnected_Icc.image _ (continuous_sq_left 0).continuousOn)
      (isPreconnected_Icc.image _ (continuous_sq_right 1).continuousOn)
  have c₂ : IsPreconnected L₂ :=
    IsPreconnected.union (sq 0 1) (⟨1, h1, rfl⟩) (⟨0, h0, rfl⟩)
      (isPreconnected_Icc.image _ (continuous_sq_right 0).continuousOn)
      (isPreconnected_Icc.image _ (continuous_sq_left 1).continuousOn)
  have ha₁ : sq 0 0 ∈ L₁ := Or.inl ⟨0, h0, rfl⟩
  have hb₁ : sq 1 1 ∈ L₁ := Or.inr ⟨1, h1, rfl⟩
  have ha₂ : sq 0 0 ∈ L₂ := Or.inl ⟨0, h0, rfl⟩
  have hb₂ : sq 1 1 ∈ L₂ := Or.inr ⟨1, h1, rfl⟩
  have hab : g (sq 0 0) ≠ g (sq 1 1) := by
    intro h
    have := congrFun (hi (sq_mem h0 h0) (sq_mem h1 h1) h) 0
    simp [sq] at this
  -- a value strictly between the ends is taken on both paths
  set v := (g (sq 0 0) + g (sq 1 1)) / 2 with hv
  have hit : ∀ L : Set (Fin 2 → ℝ), IsPreconnected L → L ⊆ Icc 0 1 → sq 0 0 ∈ L →
      sq 1 1 ∈ L → ∃ x ∈ L, g x = v := by
    intro L hL hsub ha hb
    rcases lt_or_gt_of_ne hab with h | h
    · exact hL.intermediate_value ha hb (hc.mono hsub) ⟨by linarith, by linarith⟩
    · exact hL.intermediate_value hb ha (hc.mono hsub) ⟨by linarith, by linarith⟩
  obtain ⟨x₁, hx₁, hgx₁⟩ := hit L₁ c₁ sub₁ ha₁ hb₁
  obtain ⟨x₂, hx₂, hgx₂⟩ := hit L₂ c₂ sub₂ ha₂ hb₂
  have hx : x₁ = x₂ := hi (sub₁ hx₁) (sub₂ hx₂) (hgx₁.trans hgx₂.symm)
  -- the paths meet only at the corners
  have e₁ : x₁ 1 = 0 ∨ x₁ 0 = 1 := by
    rcases hx₁ with ⟨t, -, rfl⟩ | ⟨t, -, rfl⟩ <;> simp [sq]
  have e₂ : x₁ 0 = 0 ∨ x₁ 1 = 1 := by
    rw [hx]
    rcases hx₂ with ⟨t, -, rfl⟩ | ⟨t, -, rfl⟩ <;> simp [sq]
  have corner : x₁ = sq 0 0 ∨ x₁ = sq 1 1 := by
    rcases e₁ with h₁ | h₁ <;> rcases e₂ with h₂ | h₂
    · left; ext i; fin_cases i <;> simp [sq, h₁, h₂]
    · rw [h₁] at h₂; norm_num at h₂
    · rw [h₁] at h₂; norm_num at h₂
    · right; ext i; fin_cases i <;> simp [sq, h₁, h₂]
  rcases corner with h | h <;> rw [h] at hgx₁
  · have : g (sq 0 0) = g (sq 1 1) := by linarith
    exact hab this
  · have : g (sq 0 0) = g (sq 1 1) := by linarith
    exact hab this

/-! ## Space -/

namespace Space3

/-- Space. -/
abbrev E3 := EuclideanSpace ℝ (Fin 3)

/-- The point `(x, y, z)`. -/
noncomputable def pt (x y z : ℝ) : E3 := !₂[x, y, z]

@[simp] theorem pt_zero (x y z : ℝ) : pt x y z 0 = x := rfl
@[simp] theorem pt_one (x y z : ℝ) : pt x y z 1 = y := rfl
@[simp] theorem pt_two (x y z : ℝ) : pt x y z 2 = z := rfl

theorem eq_pt (p : E3) : p = pt (p 0) (p 1) (p 2) := by
  ext i
  fin_cases i <;> rfl

theorem continuous_pt {X : Type*} [TopologicalSpace X] {f g h : X → ℝ} (hf : Continuous f)
    (hg : Continuous g) (hh : Continuous h) : Continuous fun a => pt (f a) (g a) (h a) := by
  refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => ?_)
  fin_cases i
  · exact hf
  · exact hg
  · exact hh

/-- A set in the plane `z = 0` has no interior in space. -/
theorem interior_eq_empty_of_flat {S : Set E3} (hS : ∀ p ∈ S, p 2 = 0) : interior S = ∅ := by
  rw [eq_empty_iff_forall_notMem]
  intro x hx
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hx)
  have hx2 : x 2 = 0 := hS x (interior_subset hx)
  set y : E3 := x + (ε / 2) • EuclideanSpace.single 2 1
  have hy : y ∈ Metric.ball x ε := by
    rw [Metric.mem_ball, dist_eq_norm, show y - x = (ε / 2) • EuclideanSpace.single 2 1 by
      simp [y], norm_smul, PiLp.norm_single, norm_one, mul_one,
      Real.norm_of_nonneg (by positivity)]
    linarith
  have := hS y (hball hy)
  simp [y, hx2] at this
  linarith

/-- The segment from the origin to `(1, 0, 0)`. -/
def segment3 : Set E3 := (fun x : Fin 1 → ℝ => pt (x 0) 0 0) '' Icc 0 1

/-- The unit square in the plane `z = 0`. -/
def square3 : Set E3 := (fun x : Fin 2 → ℝ => pt (x 0) (x 1) 0) '' Icc 0 1

theorem cubeDim_point : (cubeDim 3 : DimensionFunction E3).dim {0} = 0 := by
  refine cubeDim_of_cube (k := 0) (singleton_nonempty _) (interior_singleton _) (by norm_num)
    (hasCube_zero_iff.mpr (singleton_nonempty _)) fun j hj _ => ?_
  exact not_hasCube_of_subsingleton hj subsingleton_singleton

theorem cubeDim_segment : (cubeDim 3 : DimensionFunction E3).dim segment3 = 1 := by
  have hflat : ∀ p ∈ segment3, p 2 = 0 := by
    rintro _ ⟨x, -, rfl⟩
    rfl
  have hcube : HasCube 1 segment3 := by
    refine ⟨fun x : Fin 1 → ℝ => pt (x 0) 0 0, (continuous_pt (continuous_apply 0)
      continuous_const continuous_const).continuousOn, fun x _ y _ h => ?_, subset_rfl⟩
    have h0 := congrArg (fun p : E3 => p 0) h
    ext i
    fin_cases i
    exact h0
  refine cubeDim_of_cube (k := 1) ⟨_, ⟨0, ⟨le_rfl, zero_le_one⟩, rfl⟩⟩ (interior_eq_empty_of_flat hflat)
    (by norm_num) hcube fun j hj hj2 => ?_
  obtain rfl : j = 2 := by omega
  rintro ⟨f, hc, hi, hf⟩
  apply not_injOn_square (g := fun x => f x 0)
  · exact (continuous_apply 0 |>.comp (PiLp.continuous_ofLp 2 _)).comp_continuousOn hc
  · have onSeg : ∀ z ∈ Icc (0 : Fin 2 → ℝ) 1, f z = pt (f z 0) 0 0 := by
      intro z hz
      obtain ⟨a, -, ha⟩ := hf ⟨z, hz, rfl⟩
      rw [← ha]
      rfl
    intro x hx y hy h
    apply hi hx hy
    rw [onSeg x hx, onSeg y hy, show f x 0 = f y 0 from h]

theorem cubeDim_square : (cubeDim 3 : DimensionFunction E3).dim square3 = 2 := by
  have hflat : ∀ p ∈ square3, p 2 = 0 := by
    rintro _ ⟨x, -, rfl⟩
    rfl
  have hcube : HasCube 2 square3 := by
    refine ⟨fun x : Fin 2 → ℝ => pt (x 0) (x 1) 0, (continuous_pt (continuous_apply 0)
      (continuous_apply 1) continuous_const).continuousOn, fun x _ y _ h => ?_, subset_rfl⟩
    have h0 := congrArg (fun p : E3 => p 0) h
    have h1 := congrArg (fun p : E3 => p 1) h
    ext i
    fin_cases i
    · exact h0
    · exact h1
  exact cubeDim_of_cube (k := 2) ⟨_, ⟨0, ⟨le_rfl, zero_le_one⟩, rfl⟩⟩
    (interior_eq_empty_of_flat hflat) (by norm_num) hcube fun j hj hj2 => by omega

theorem cubeDim_ball : (cubeDim 3 : DimensionFunction E3).dim (Metric.closedBall 0 1) = 3 :=
  cubeDim_of_interior ⟨0, Metric.ball_subset_interior_closedBall (Metric.mem_ball_self one_pos)⟩

/-- In space the interior-interior entry of a ball with itself is `3`. -/
theorem de9im_ball_ball_II :
    de9im (cubeDim 3) (Metric.closedBall (0 : E3) 1) (Metric.closedBall 0 1) .I .I = 3 := by
  apply cubeDim_of_interior
  show (interior (interior (Metric.closedBall (0 : E3) 1) ∩ interior (Metric.closedBall 0 1))).Nonempty
  rw [inter_self, interior_interior]
  exact ⟨0, Metric.ball_subset_interior_closedBall (Metric.mem_ball_self one_pos)⟩

end Space3

end Geospatial.DE9IM
