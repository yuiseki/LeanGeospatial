import LeanGeospatial.Spaces.Unified

/-!
# Maps Between `ℝ²`, `S²`, and `ℝ³` and Spatial Relation Preservation

Separates the five levels of map regularity — general functions, injective maps,
continuous maps, open embeddings, and homeomorphisms — and formalizes the
canonical maps between `ℝ²`, `S²`, and `ℝ³`:

- `embedPlane z₀ : E2 → E3` and `projXY : E3 → E2` (from `Approximation2D3D.lean`)
- `inclS2 : S2 → E3` (inclusion of the unit sphere into `ℝ³`)
- `radialProj : {p : E3 // p ≠ 0} → S2` (radial projection `p ↦ ‖p‖⁻¹ • p`)
- `stereoHomeomorph : {p : S2 // p ≠ northPole} ≃ₜ E2` (stereographic
  projection, a global homeomorphism between the punctured sphere `S² \ {N}`
  and the plane `ℝ²`, preserving all RCC8 and `cubeDim 2` DE-9IM relations
  while distorting metric distances)
- `embedGraph h : E2 → E3` and `extrude z₁ z₂` (from `Approximation2D3D.lean`)

## Preservation hierarchy summary

| Map class | Preserves | Does NOT preserve (counterexample) |
| --- | --- | --- |
| General `f : α → β` | `Within`, `Intersects`, reflects `Disjoint` | `Disjoint`, `=` (`counterexample_noninjective_disjoint`) |
| Injective `f` | `Within`, `Intersects`, `Disjoint`, `=` | `IsConnected`, `interior` |
| Continuous `f` | `IsConnected`, `IsCompact` | `interior` (`interior_inclS2_eq_empty`, `interior_embedPlane_eq_empty`) |
| Open embedding `f` (`T2Space β`) | `interior`, `Touches`, compact `RegularClosedRegion`, compact `RCC8` | — (on compact areas) |
| Homeomorphism `e : α ≃ₜ β` | `interior`, `boundary`, `exterior`, `Touches`, `RegularClosedRegion`, `RCC8`, `cubeDim n`, `de9im (cubeDim n)` | Metric `dist` (`counterexample_stereo_not_isometry`) |
-/

namespace Geospatial.Spaces

open Set Topology Geospatial Geospatial.DE9IM Geospatial.DE9IM.Space3

/-! ## 1. Abstract preservation hierarchy -/

section AbstractMaps

variable {α β : Type*}

/-- Any function preserves `Within` (`⊆`). -/
theorem image_within_mono (f : α → β) {A B : Set α} (h : Within A B) :
    Within (f '' A) (f '' B) :=
  Set.image_mono h

/-- Any function preserves `Intersects`. -/
theorem image_intersects_of_intersects (f : α → β) {A B : Set α} (h : Intersects A B) :
    Intersects (f '' A) (f '' B) := by
  obtain ⟨x, hxA, hxB⟩ := h
  exact ⟨f x, ⟨x, hxA, rfl⟩, ⟨x, hxB, rfl⟩⟩

/-- Any function reflects `Disjoint`: if images are disjoint, pre-sets are disjoint. -/
theorem disjoint_of_image_disjoint (f : α → β) {A B : Set α}
    (h : Geospatial.Disjoint (f '' A) (f '' B)) :
    Geospatial.Disjoint A B := by
  rw [disjoint_iff_not_intersects] at h ⊢
  exact fun hi => h (image_intersects_of_intersects f hi)

/-- An injective function preserves and reflects `Within`, `Intersects`, `Disjoint`, `=`. -/
theorem image_within_iff_of_inj {f : α → β} (hf : Function.Injective f) (A B : Set α) :
    Within (f '' A) (f '' B) ↔ Within A B :=
  Set.image_subset_image_iff hf

theorem image_intersects_iff_of_inj {f : α → β} (hf : Function.Injective f) (A B : Set α) :
    Intersects (f '' A) (f '' B) ↔ Intersects A B := by
  unfold Intersects
  rw [← Set.image_inter hf, Set.image_nonempty]

theorem image_disjoint_iff_of_inj {f : α → β} (hf : Function.Injective f) (A B : Set α) :
    Geospatial.Disjoint (f '' A) (f '' B) ↔ Geospatial.Disjoint A B := by
  rw [disjoint_iff_not_intersects, disjoint_iff_not_intersects, image_intersects_iff_of_inj hf]

theorem image_eq_iff_of_inj {f : α → β} (hf : Function.Injective f) (A B : Set α) :
    f '' A = f '' B ↔ A = B :=
  (Set.image_injective.mpr hf).eq_iff

/-- A continuous function preserves connectedness and compactness. -/
theorem image_isConnected_of_continuous [TopologicalSpace α] [TopologicalSpace β]
    {f : α → β} (hf : Continuous f) {A : Set α} (hA : IsConnected A) :
    IsConnected (f '' A) :=
  hA.image f hf.continuousOn

theorem image_isCompact_of_continuous [TopologicalSpace α] [TopologicalSpace β]
    {f : α → β} (hf : Continuous f) {A : Set α} (hA : IsCompact A) :
    IsCompact (f '' A) :=
  hA.image hf

/-- **Minimal counterexample**: a non-injective map fails to preserve `Disjoint`
and fails to reflect `=`. -/
theorem counterexample_noninjective_disjoint :
    let f : Bool → Unit := fun _ => ()
    Geospatial.Disjoint ({true} : Set Bool) {false} ∧
      Intersects (f '' {true}) (f '' {false}) ∧
      f '' ({true} : Set Bool) = f '' {false} := by
  intro f
  refine ⟨?_, ⟨(), ⟨true, rfl, rfl⟩, ⟨false, rfl, rfl⟩⟩, ?_⟩
  · rw [Geospatial.Disjoint, eq_empty_iff_forall_notMem]
    rintro x ⟨rfl, h⟩
    cases h
  · ext u; simp [f]

end AbstractMaps

/-! ## 2. Inclusion `inclS2 : S² → ℝ³` -/

/-- Canonical inclusion of the unit 2-sphere `S²` into ambient `ℝ³`. -/
def inclS2 : S2 → E3 := Subtype.val

theorem inclS2_injective : Function.Injective inclS2 := Subtype.val_injective

@[fun_prop] theorem continuous_inclS2 : Continuous inclS2 := continuous_subtype_val

theorem isClosedEmbedding_inclS2 : IsClosedEmbedding inclS2 :=
  (Metric.isClosed_sphere (x := (0 : E3)) (ε := 1)).isClosedEmbedding_subtypeVal

/-- `inclS2` is an isometry (for the chordal/ambient Euclidean metric on `S2`). -/
theorem dist_inclS2 (p q : S2) : dist (inclS2 p) (inclS2 q) = dist p q := rfl

theorem inclS2_within_iff (A B : Set S2) :
    Within (inclS2 '' A) (inclS2 '' B) ↔ Within A B :=
  image_within_iff_of_inj inclS2_injective A B

theorem inclS2_intersects_iff (A B : Set S2) :
    Intersects (inclS2 '' A) (inclS2 '' B) ↔ Intersects A B :=
  image_intersects_iff_of_inj inclS2_injective A B

theorem inclS2_disjoint_iff (A B : Set S2) :
    Geospatial.Disjoint (inclS2 '' A) (inclS2 '' B) ↔ Geospatial.Disjoint A B :=
  image_disjoint_iff_of_inj inclS2_injective A B

theorem inclS2_isConnected_iff {A : Set S2} :
    IsConnected (inclS2 '' A) ↔ IsConnected A := by
  simp only [IsConnected, Set.image_nonempty,
    isClosedEmbedding_inclS2.isInducing.isPreconnected_image]

theorem inclS2_isCompact_iff {A : Set S2} :
    IsCompact (inclS2 '' A) ↔ IsCompact A :=
  isClosedEmbedding_inclS2.isInducing.isCompact_iff.symm

/-- **Ambient 3D interior of any spherical subset is EMPTY**:
every ball `B(x, ε)` in `ℝ³` around a point `x ∈ S²` contains `(1 + ε/2) • x`,
which has norm `1 + ε/2 ≠ 1` and therefore lies outside `S²`. -/
theorem interior_inclS2_eq_empty (A : Set S2) :
    interior (inclS2 '' A) = ∅ := by
  rw [eq_empty_iff_forall_notMem]
  intro x hx
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hx)
  obtain ⟨p, -, rfl⟩ := interior_subset hx
  have hnorm : ‖(p : E3)‖ = 1 := by
    have := p.2
    rwa [Metric.mem_sphere, dist_zero_right] at this
  set y : E3 := (1 + ε / 2) • (p : E3)
  have hy_ball : y ∈ Metric.ball (p : E3) ε := by
    rw [Metric.mem_ball, dist_eq_norm]
    have hsub : y - (p : E3) = (ε / 2) • (p : E3) := by
      simp only [y]; module
    rw [hsub, norm_smul, hnorm, mul_one, Real.norm_of_nonneg (by positivity)]
    linarith
  obtain ⟨q, -, hq⟩ := hball hy_ball
  have hnorm_y : ‖y‖ = 1 := by
    rw [← hq]
    have := q.2
    rwa [Metric.mem_sphere, dist_zero_right] at this
  have hnorm_y' : ‖y‖ = 1 + ε / 2 := by
    simp only [y, norm_smul, hnorm, mul_one, Real.norm_eq_abs, abs_of_pos (by linarith : 0 < 1 + ε / 2)]
  linarith

/-- No nonempty subset of `S²` is a 3D `RegularClosedRegion E3`. -/
theorem inclS2_not_regularClosed {A : Set S2} (hA : A.Nonempty) :
    closure (interior (inclS2 '' A)) ≠ inclS2 '' A := by
  rw [interior_inclS2_eq_empty, closure_empty]
  exact (hA.image _).ne_empty.symm

/-- In ambient `ℝ³`, two spherical subsets `Touches` iff they merely `Intersects`. -/
theorem ambient_touches_inclS2_iff_intersects (A B : Set S2) :
    Touches (inclS2 '' A) (inclS2 '' B) ↔ Intersects A B := by
  unfold Touches
  rw [inclS2_intersects_iff, interior_inclS2_eq_empty, interior_inclS2_eq_empty]
  simp [Geospatial.Disjoint]

/-! ## 3. Radial projection `radialProj : ℝ³ \ {0} → S²` -/

/-- Radial projection from punctured 3D space `ℝ³ \ {0}` onto the unit sphere `S²`. -/
noncomputable def radialProj (p : {x : E3 // x ≠ 0}) : S2 :=
  ⟨‖p.1‖⁻¹ • p.1, by
    rw [Metric.mem_sphere, dist_zero_right, norm_smul, norm_inv, norm_norm]
    exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr p.2)⟩

theorem continuous_radialProj : Continuous radialProj := by
  refine Continuous.subtype_mk ?_ _
  exact (continuous_norm.comp continuous_subtype_val |>.inv₀ fun p =>
    norm_ne_zero_iff.mpr p.2).smul continuous_subtype_val

theorem radialProj_inclS2 (p : S2) :
    radialProj ⟨p.1, by
      intro h0
      have := p.2
      rw [h0, Metric.mem_sphere, dist_self] at this
      norm_num at this⟩ = p := by
  apply Subtype.ext
  have hnorm : ‖(p : E3)‖ = 1 := by
    have := p.2
    rwa [Metric.mem_sphere, dist_zero_right] at this
  simp [radialProj, hnorm]

theorem radialProj_surjective : Function.Surjective radialProj := fun p =>
  ⟨⟨p.1, by
    intro h0
    have := p.2
    rw [h0, Metric.mem_sphere, dist_self] at this
    norm_num at this⟩, radialProj_inclS2 p⟩

theorem disjoint_of_radialProj_disjoint {A B : Set {x : E3 // x ≠ 0}}
    (h : Geospatial.Disjoint (radialProj '' A) (radialProj '' B)) :
    Geospatial.Disjoint A B :=
  disjoint_of_image_disjoint radialProj h

/-- **Minimal counterexample**: `radialProj` does NOT preserve `Disjoint` or `=`.
`(1, 0, 0)` and `(2, 0, 0)` are distinct (disjoint singletons) in `ℝ³ \ {0}`,
yet project to the same point on `S²`. -/
theorem counterexample_radialProj_not_disjoint :
    let p₁ : {x : E3 // x ≠ 0} := ⟨pt 1 0 0, fun h => by
      have := congrArg (fun q : E3 => q 0) h; simp [pt] at this⟩
    let p₂ : {x : E3 // x ≠ 0} := ⟨pt 2 0 0, fun h => by
      have := congrArg (fun q : E3 => q 0) h; simp [pt] at this⟩
    Geospatial.Disjoint ({p₁} : Set _) {p₂} ∧ radialProj p₁ = radialProj p₂ := by
  intro p₁ p₂
  refine ⟨?_, ?_⟩
  · rw [Geospatial.Disjoint, eq_empty_iff_forall_notMem]
    rintro x ⟨rfl, h⟩
    have h0 := congrArg (fun q : {x : E3 // x ≠ 0} => q.1 0) h
    simp [p₁, p₂, pt] at h0
  · apply Subtype.ext
    have h1 : ‖p₁.1‖ = 1 := by
      rw [EuclideanSpace.norm_eq, Fin.sum_univ_three]
      simp [p₁, pt]
    have h2 : ‖p₂.1‖ = 2 := by
      rw [EuclideanSpace.norm_eq, Fin.sum_univ_three]
      simp only [p₂, pt, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons, norm_zero, zero_pow two_ne_zero, add_zero,
        Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      exact Real.sqrt_sq (by norm_num)
    show ‖p₁.1‖⁻¹ • p₁.1 = ‖p₂.1‖⁻¹ • p₂.1
    rw [h1, h2]
    ext i
    fin_cases i <;> simp [p₁, p₂, pt]

/-! ## 4. Local Homeomorphism `S² \ {northPole} ≃ₜ ℝ²` (Stereographic Projection) -/

/-- The punctured unit sphere `S² \ {northPole}`. -/
abbrev PuncturedS2 := {p : S2 // p ≠ northPole}

private theorem one_sub_z_ne_zero (p : PuncturedS2) : 1 - (p.1 : E3) 2 ≠ 0 := by
  intro h
  have hz : (p.1 : E3) 2 = 1 := by linarith
  have hnorm : ((p.1 : E3) 0) ^ 2 + ((p.1 : E3) 1) ^ 2 + ((p.1 : E3) 2) ^ 2 = 1 := by
    have hp := p.1.2
    rw [Metric.mem_sphere, dist_zero_right, EuclideanSpace.norm_eq, Fin.sum_univ_three] at hp
    have hsq := congrArg (· ^ 2) hp
    rw [Real.sq_sqrt (by positivity), one_pow] at hsq
    simpa [Real.norm_eq_abs, sq_abs] using hsq
  have hx : (p.1 : E3) 0 = 0 := by nlinarith [sq_nonneg ((p.1 : E3) 0), sq_nonneg ((p.1 : E3) 1)]
  have hy : (p.1 : E3) 1 = 0 := by nlinarith [sq_nonneg ((p.1 : E3) 0), sq_nonneg ((p.1 : E3) 1)]
  apply p.2
  apply Subtype.ext
  ext i
  fin_cases i
  · simpa [northPole] using hx
  · simpa [northPole] using hy
  · simpa [northPole] using hz

/-- Stereographic projection from `northPole`: `S² \ {N} → ℝ²`. -/
noncomputable def stereoProj (p : PuncturedS2) : E2 :=
  Point2D.mk ((p.1 : E3) 0 / (1 - (p.1 : E3) 2)) ((p.1 : E3) 1 / (1 - (p.1 : E3) 2))

/-- Inverse stereographic projection: `ℝ² → S² \ {N}`. -/
noncomputable def stereoInv (q : E2) : PuncturedS2 :=
  let r2 := q.x ^ 2 + q.y ^ 2
  have hd : r2 + 1 ≠ 0 := by positivity
  ⟨⟨pt (2 * q.x / (r2 + 1)) (2 * q.y / (r2 + 1)) ((r2 - 1) / (r2 + 1)), by
    rw [Metric.mem_sphere, dist_zero_right, EuclideanSpace.norm_eq, Fin.sum_univ_three]
    have hsum : (2 * q.x / (r2 + 1)) ^ 2 + (2 * q.y / (r2 + 1)) ^ 2 +
        ((r2 - 1) / (r2 + 1)) ^ 2 = 1 := by
      field_simp
      simp only [r2]
      ring
    simp only [pt, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, Real.norm_eq_abs, sq_abs, hsum, Real.sqrt_one]⟩,
   by
    intro heq
    have h2 := congrArg (fun p : S2 => (p : E3) 2) heq
    change (r2 - 1) / (r2 + 1) = (1 : ℝ) at h2
    have : r2 - 1 = r2 + 1 := (div_eq_one_iff_eq hd).mp h2
    linarith⟩

/-- **Stereographic Homeomorphism `S² \ {northPole} ≃ₜ ℝ²`**. -/
noncomputable def stereoHomeomorph : PuncturedS2 ≃ₜ E2 where
  toFun := stereoProj
  invFun := stereoInv
  left_inv p := by
    apply Subtype.ext; apply Subtype.ext
    have hne : 1 - (p.1 : E3) 2 ≠ 0 := one_sub_z_ne_zero p
    have hnorm : ((p.1 : E3) 0) ^ 2 + ((p.1 : E3) 1) ^ 2 + ((p.1 : E3) 2) ^ 2 = 1 := by
      have hp := p.1.2
      rw [Metric.mem_sphere, dist_zero_right, EuclideanSpace.norm_eq, Fin.sum_univ_three] at hp
      have hsq := congrArg (· ^ 2) hp
      rw [Real.sq_sqrt (by positivity), one_pow] at hsq
      simpa [Real.norm_eq_abs, sq_abs] using hsq
    have hr2 : ((p.1 : E3) 0 / (1 - (p.1 : E3) 2)) ^ 2 +
        ((p.1 : E3) 1 / (1 - (p.1 : E3) 2)) ^ 2 + 1 = 2 / (1 - (p.1 : E3) 2) := by
      field_simp
      linear_combination hnorm
    ext i
    fin_cases i
    · change 2 * ((p.1 : E3) 0 / (1 - (p.1 : E3) 2)) /
          (Point2D.x (stereoProj p) ^ 2 + Point2D.y (stereoProj p) ^ 2 + 1) = (p.1 : E3) 0
      simp only [stereoProj, Point2D.x_mk, Point2D.y_mk]
      rw [hr2]; field_simp
    · change 2 * ((p.1 : E3) 1 / (1 - (p.1 : E3) 2)) /
          (Point2D.x (stereoProj p) ^ 2 + Point2D.y (stereoProj p) ^ 2 + 1) = (p.1 : E3) 1
      simp only [stereoProj, Point2D.x_mk, Point2D.y_mk]
      rw [hr2]; field_simp
    · change (((p.1 : E3) 0 / (1 - (p.1 : E3) 2)) ^ 2 +
          ((p.1 : E3) 1 / (1 - (p.1 : E3) 2)) ^ 2 - 1) /
          (Point2D.x (stereoProj p) ^ 2 + Point2D.y (stereoProj p) ^ 2 + 1) = (p.1 : E3) 2
      simp only [stereoProj, Point2D.x_mk, Point2D.y_mk]
      rw [hr2]
      have hr2' : ((p.1 : E3) 0 / (1 - (p.1 : E3) 2)) ^ 2 +
          ((p.1 : E3) 1 / (1 - (p.1 : E3) 2)) ^ 2 - 1 =
          2 * (p.1 : E3) 2 / (1 - (p.1 : E3) 2) := by
        field_simp
        linear_combination hnorm
      rw [hr2']
      field_simp
  right_inv q := by
    set r2 := q.x ^ 2 + q.y ^ 2
    have hd : r2 + 1 ≠ 0 := by positivity
    have h1z : 1 - (r2 - 1) / (r2 + 1) = 2 / (r2 + 1) := by field_simp; ring
    apply Point2D.ext
    · change (2 * q.x / (r2 + 1)) / (1 - (r2 - 1) / (r2 + 1)) = q.x
      rw [h1z]; field_simp
    · change (2 * q.y / (r2 + 1)) / (1 - (r2 - 1) / (r2 + 1)) = q.y
      rw [h1z]; field_simp
  continuous_toFun := by
    have h0 : Continuous fun p : PuncturedS2 => (p.1 : E3) 0 :=
      (PiLp.continuous_apply 2 _ 0).comp (continuous_subtype_val.comp continuous_subtype_val)
    have h1 : Continuous fun p : PuncturedS2 => (p.1 : E3) 1 :=
      (PiLp.continuous_apply 2 _ 1).comp (continuous_subtype_val.comp continuous_subtype_val)
    have h2 : Continuous fun p : PuncturedS2 => 1 - (p.1 : E3) 2 :=
      continuous_const.sub ((PiLp.continuous_apply 2 _ 2).comp
        (continuous_subtype_val.comp continuous_subtype_val))
    exact Point2D.continuous_mk (h0.div h2 one_sub_z_ne_zero) (h1.div h2 one_sub_z_ne_zero)
  continuous_invFun := by
    refine Continuous.subtype_mk (Continuous.subtype_mk ?_ _) _
    have hx : Continuous Point2D.x := Point2D.continuous_x
    have hy : Continuous Point2D.y := Point2D.continuous_y
    have hr2 : Continuous fun q : E2 => q.x ^ 2 + q.y ^ 2 := (hx.pow 2).add (hy.pow 2)
    have hd : Continuous fun q : E2 => q.x ^ 2 + q.y ^ 2 + 1 := hr2.add continuous_const
    have hne : ∀ q : E2, q.x ^ 2 + q.y ^ 2 + 1 ≠ 0 := fun q => by positivity
    exact continuous_pt
      ((continuous_const.mul hx).div hd hne)
      ((continuous_const.mul hy).div hd hne)
      ((hr2.sub continuous_const).div hd hne)

/-- **Local map projection preserves ALL RCC8 relations**:
on `S² \ {N}`, stereographic projection to `ℝ²` preserves every RCC8 relation. -/
theorem stereoHomeomorph_rcc8_iff (A B : RegularClosedRegion PuncturedS2) (r : RCC8.Relation) :
    r.holds (A.map stereoHomeomorph) (B.map stereoHomeomorph) ↔ r.holds A B :=
  RCC8.Relation.holds_map_iff stereoHomeomorph A B r

/-- **Local map projection preserves the ENTIRE `cubeDim 2` DE-9IM matrix**. -/
theorem stereoHomeomorph_de9im_eq (A B : Set PuncturedS2) :
    de9im (cubeDim 2) (stereoHomeomorph '' A) (stereoHomeomorph '' B) =
      de9im (cubeDim 2) A B :=
  de9im_map (cubeDim_compatible 2 stereoHomeomorph) A B

/-- **Topological exactness vs metric distortion**:
stereographic projection is a homeomorphism (preserving all RCC8 & DE-9IM
relations) yet is NOT an isometry: `(0, 0)` and `(1, 0)` in `ℝ²` have planar
distance `1`, whereas their preimages on `S²` (`(0, 0, -1)` and `(1, 0, 0)`)
have Euclidean chordal distance `√2 ≠ 1`. -/
theorem counterexample_stereo_not_isometry :
    let q₁ : E2 := Point2D.mk 0 0
    let q₂ : E2 := Point2D.mk 1 0
    dist q₁ q₂ = 1 ∧ dist (stereoInv q₁).1 (stereoInv q₂).1 = Real.sqrt 2 ∧
      dist q₁ q₂ ≠ dist (stereoInv q₁).1 (stereoInv q₂).1 := by
  intro q₁ q₂
  have h1 : dist q₁ q₂ = 1 := by
    rw [EuclideanSpace.dist_eq, Fin.sum_univ_two]
    simp [q₁, q₂, Point2D.mk]
  have h2 : dist (stereoInv q₁).1 (stereoInv q₂).1 = Real.sqrt 2 := by
    change dist ((stereoInv q₁).1 : E3) ((stereoInv q₂).1 : E3) = Real.sqrt 2
    rw [EuclideanSpace.dist_eq, Fin.sum_univ_three]
    simp only [stereoInv, q₁, q₂, Point2D.x_mk, Point2D.y_mk, pt,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    norm_num
  refine ⟨h1, h2, ?_⟩
  rw [h1, h2]
  intro heq
  have := congrArg (· ^ 2) heq
  norm_num at this

end Geospatial.Spaces
