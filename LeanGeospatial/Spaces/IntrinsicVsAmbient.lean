import LeanGeospatial.Spaces.Maps

/-!
# Intrinsic Space vs Ambient Space (`ℝ²`, `S²`, `ℝ³`)

Demonstrates formally that the **same point set** has different `interior`,
`boundary`, `exterior`, `Touches`, `RegularClosedRegion`, and `RCC8` semantics
depending on which space is taken as the ambient topological space:

- `RegularClosedRegion α` and `RCC8.Relation.holds` are parameterized explicitly
  by the ambient topological space `α` (`E2`, `S2`, or `E3`).
- `isOpenEmbedding_stereoEmbed`: inverse stereographic projection
  `stereoEmbed : E2 → S2` is an open embedding into Hausdorff `S²`, lifting any
  compact `RegularClosedRegion E2` to a genuine intrinsic `RegularClosedRegion S2`.
- **Intrinsic `S²` vs ambient `ℝ³`**:
  - A lifted compact planar area `S : RegularClosedRegion S2` has **nonempty**
    intrinsic interior in `S²` (`intrinsic_interior_S2_nonempty`) and intrinsic
    dimension `dimS2.dim S = 2` (`intrinsic_dim_S2_eq_two`).
  - Its image `inclS2 '' S` in ambient `ℝ³` has **empty** 3D interior
    (`interior_inclS2_eq_empty`), its ambient 3D boundary is the **entire set**
    (`ambient_boundary_S2_eq_self`), it is NOT a `RegularClosedRegion E3`, and
    its ambient `cubeDim 3` dimension is `2` (`ambient_dim_S2_eq_two`) rather
    than `3` (contrasting with 3D solids like `Metric.closedBall 0 1`).
  - **Relations flip across ambient spaces**: two overlapping spherical areas
    satisfy `RCC8.PO` (and `¬ Touches`) in intrinsic `S²`, yet satisfy ambient
    `Touches` in `ℝ³` (`intrinsic_po_but_ambient_touches_S2`), and likewise for
    two overlapping planar squares embedded in `ℝ³` (`intrinsic_po_but_ambient_touches_E2`).
-/

namespace Geospatial.Spaces

open Set Topology Geospatial Geospatial.DE9IM Geospatial.DE9IM.Space3 Geospatial.Space2D3D

/-! ## Lifting compact planar areas into intrinsic `S²` -/

/-- Inverse stereographic projection viewed as a map `ℝ² → S²`. -/
noncomputable def stereoEmbed (q : E2) : S2 := (stereoInv q).1

/-- `stereoEmbed : ℝ² → S²` is an open embedding (image is `S² \ {northPole}`). -/
theorem isOpenEmbedding_stereoEmbed : IsOpenEmbedding stereoEmbed := by
  have hopen : IsOpen ({northPole}ᶜ : Set S2) := isClosed_singleton.isOpen_compl
  have hval : IsOpenEmbedding (Subtype.val : PuncturedS2 → S2) :=
    hopen.isOpenEmbedding_subtypeVal
  exact hval.comp stereoHomeomorph.symm.isOpenEmbedding

/-- Lift any compact `RegularClosedRegion E2` to a `RegularClosedRegion S2`. -/
noncomputable def liftToS2 (A : RegularClosedRegion E2) (hA : IsCompact (A : Set E2)) :
    RegularClosedRegion S2 :=
  A.mapCompact isOpenEmbedding_stereoEmbed hA

@[simp] theorem coe_liftToS2 (A : RegularClosedRegion E2) (hA : IsCompact (A : Set E2)) :
    ((liftToS2 A hA : RegularClosedRegion S2) : Set S2) = stereoEmbed '' (A : Set E2) := rfl

/-- Lifting compact planar areas to `S²` preserves all 8 RCC8 relations. -/
theorem liftToS2_rcc8_iff {A B : RegularClosedRegion E2}
    (hA : IsCompact (A : Set E2)) (hB : IsCompact (B : Set E2)) (r : RCC8.Relation) :
    r.holds (liftToS2 A hA) (liftToS2 B hB) ↔ r.holds A B :=
  RCC8.Relation.holds_mapCompact_iff isOpenEmbedding_stereoEmbed hA hB r

/-! ## Intrinsic `S²` vs ambient `ℝ³` -/

/-- A nonempty compact planar area lifted to `S²` has **nonempty** intrinsic
interior in `S²`. -/
theorem intrinsic_interior_S2_nonempty {A : RegularClosedRegion E2}
    (hA : IsCompact (A : Set E2)) (hne : (A : Set E2).Nonempty) :
    (interior ((liftToS2 A hA : RegularClosedRegion S2) : Set S2)).Nonempty := by
  rw [coe_liftToS2, interior_image_of_isOpenEmbedding isOpenEmbedding_stereoEmbed]
  exact (A.nonempty_iff_interior_nonempty.mp hne).image stereoEmbed

/-- Its intrinsic dimension in `S²` is `2`. -/
theorem intrinsic_dim_S2_eq_two {A : RegularClosedRegion E2}
    (hA : IsCompact (A : Set E2)) (hne : (A : Set E2).Nonempty) :
    dimS2.dim ((liftToS2 A hA : RegularClosedRegion S2) : Set S2) = 2 :=
  cubeDim_of_interior (intrinsic_interior_S2_nonempty hA hne)

/-- In ambient `ℝ³`, the boundary of any closed subset of `S²` (including a
lifted spherical area) is the **entire set itself** (since ambient interior is `∅`). -/
theorem ambient_boundary_S2_eq_self {S : Set S2} (hS : IsClosed S) :
    Geospatial.boundary (inclS2 '' S) = inclS2 '' S := by
  rw [Geospatial.boundary_eq, (isClosedEmbedding_inclS2.isClosedMap S hS).closure_eq,
    interior_inclS2_eq_empty, sdiff_empty]

/-- In ambient `ℝ³`, a lifted spherical area has `cubeDim 3 = 2` (NOT `3`):
its ambient interior is empty, yet it contains an embedded 2-cube via `stereoEmbed`. -/
theorem ambient_dim_S2_eq_two {r : Rect} (hx : r.xmin < r.xmax) (hy : r.ymin < r.ymax) :
    let A := r.toRegularClosed hx hy
    let S := liftToS2 A r.isCompact_toRegion
    dimE3.dim (inclS2 '' (S : Set S2)) = 2 := by
  intro A S
  have hne : (inclS2 '' (S : Set S2)).Nonempty := by
    refine ⟨inclS2 (stereoEmbed (Point2D.mk r.xmin r.ymin)),
      ⟨stereoEmbed (Point2D.mk r.xmin r.ymin),
        ⟨Point2D.mk r.xmin r.ymin, ⟨le_rfl, hx.le, le_rfl, hy.le⟩, rfl⟩, rfl⟩⟩
  have hcube : HasCube 2 (inclS2 '' (S : Set S2)) := by
    let f : (Fin 2 → ℝ) → E2 := fun t =>
      Point2D.mk (r.xmin + t 0 * (r.xmax - r.xmin)) (r.ymin + t 1 * (r.ymax - r.ymin))
    have hf_cont : Continuous f := Point2D.continuous_mk
      (continuous_const.add ((continuous_apply 0).mul continuous_const))
      (continuous_const.add ((continuous_apply 1).mul continuous_const))
    have hf_inj : Function.Injective f := by
      intro t₁ t₂ h
      have h0 := congrArg Geospatial.Point2D.x h
      have h1 := congrArg Geospatial.Point2D.y h
      simp only [f, Point2D.x_mk, Point2D.y_mk] at h0 h1
      have hdx : r.xmax - r.xmin ≠ 0 := by linarith
      have hdy : r.ymax - r.ymin ≠ 0 := by linarith
      ext i; fin_cases i
      · exact mul_right_cancel₀ hdx (add_left_cancel h0)
      · exact mul_right_cancel₀ hdy (add_left_cancel h1)
    refine ⟨inclS2 ∘ stereoEmbed ∘ f,
      ((continuous_inclS2.comp isOpenEmbedding_stereoEmbed.continuous).comp hf_cont).continuousOn,
      (inclS2_injective.comp (isOpenEmbedding_stereoEmbed.injective.comp hf_inj)).injOn, ?_⟩
    rintro _ ⟨t, ht, rfl⟩
    have ht0_lo : (0 : ℝ) ≤ t 0 := ht.1 0
    have ht0_hi : t 0 ≤ (1 : ℝ) := ht.2 0
    have ht1_lo : (0 : ℝ) ≤ t 1 := ht.1 1
    have ht1_hi : t 1 ≤ (1 : ℝ) := ht.2 1
    refine ⟨stereoEmbed (f t), ⟨f t, ?_, rfl⟩, rfl⟩
    show f t ∈ r.toRegion
    simp only [Rect.toRegion, f, mem_ofPred_eq, Point2D.x_mk, Point2D.y_mk]
    exact ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith⟩
  exact cubeDim_of_cube (k := 2) hne (interior_inclS2_eq_empty _) (by norm_num) hcube
    fun j hj hj2 => by omega

/-- **Same spherical regions, opposite topological verdict**:
two overlapping spherical regions on `S²` satisfy `RCC8.PO` (and `¬ Touches`)
in intrinsic `S²`, yet their ambient images in `ℝ³` satisfy `Touches`! -/
theorem intrinsic_po_but_ambient_touches_S2 :
    let r₁ : Rect := ⟨0, 2, 0, 2⟩
    let r₂ : Rect := ⟨1, 3, 0, 2⟩
    let S₁ := liftToS2 (r₁.toRegularClosed (by norm_num) (by norm_num)) r₁.isCompact_toRegion
    let S₂ := liftToS2 (r₂.toRegularClosed (by norm_num) (by norm_num)) r₂.isCompact_toRegion
    RCC8.PO S₁ S₂ ∧ ¬ Touches (S₁ : Set S2) (S₂ : Set S2) ∧
      Touches (inclS2 '' (S₁ : Set S2)) (inclS2 '' (S₂ : Set S2)) := by
  intro r₁ r₂ S₁ S₂
  have hPO2D : RCC8.PO (r₁.toRegularClosed (by norm_num) (by norm_num))
      (r₂.toRegularClosed (by norm_num) (by norm_num)) := by
    refine ⟨⟨Point2D.mk (3 / 2) 1, ?_, ?_⟩, ?_, ?_⟩
    · rw [Rect.coe_toRegularClosed, Rect.interior_toRegion]
      exact ⟨by norm_num [r₁], by norm_num [r₁], by norm_num [r₁], by norm_num [r₁]⟩
    · rw [Rect.coe_toRegularClosed, Rect.interior_toRegion]
      exact ⟨by norm_num [r₂], by norm_num [r₂], by norm_num [r₂], by norm_num [r₂]⟩
    · intro hsub
      have h := hsub (show Point2D.mk 0 0 ∈ r₁.toRegion by
        simp [Rect.toRegion, r₁])
      norm_num [Rect.toRegion, r₂] at h
    · intro hsub
      have h := hsub (show Point2D.mk 3 0 ∈ r₂.toRegion by
        simp [Rect.toRegion, r₂])
      norm_num [Rect.toRegion, r₁] at h
  have hPO : RCC8.PO S₁ S₂ := (liftToS2_rcc8_iff r₁.isCompact_toRegion r₂.isCompact_toRegion .po).mpr hPO2D
  have hnotT : ¬ Touches (S₁ : Set S2) (S₂ : Set S2) := fun hT =>
    hT.not_intersects_interior hPO.1
  have hAmbT : Touches (inclS2 '' (S₁ : Set S2)) (inclS2 '' (S₂ : Set S2)) := by
    rw [ambient_touches_inclS2_iff_intersects]
    exact hPO.1.mono (inter_subset_inter interior_subset interior_subset)
  exact ⟨hPO, hnotT, hAmbT⟩

/-! ## Intrinsic `ℝ²` vs ambient `ℝ³` -/

/-- For any closed planar region `A` in `ℝ²`, its ambient 3D boundary under
`embedPlane z₀` is the entire embedded set `embedPlane z₀ '' A`. -/
theorem ambient_boundary_embedPlane_eq_self (z₀ : ℝ) {A : Region} (hA : IsClosed A) :
    Geospatial.boundary (embedPlane z₀ '' A) = embedPlane z₀ '' A := by
  have hclosed : IsClosed (embedPlane z₀ '' A) := by
    have heq : embedPlane z₀ '' A = e3HomeomorphProd ⁻¹' (A ×ˢ {z₀}) := by
      ext p
      simp only [mem_image, mem_preimage, e3HomeomorphProd_apply, mem_prod, mem_singleton_iff]
      constructor
      · rintro ⟨q, hq, rfl⟩
        exact ⟨by simpa using hq, rfl⟩
      · rintro ⟨hpA, hpz⟩
        refine ⟨projXY p, hpA, ?_⟩
        ext i; fin_cases i
        · rfl
        · rfl
        · exact hpz.symm
    rw [heq]
    exact (hA.prod isClosed_singleton).preimage e3HomeomorphProd.continuous
  rw [Geospatial.boundary_eq, hclosed.closure_eq, interior_embedPlane_eq_empty, sdiff_empty]

/-- **Same planar squares, opposite topological verdict**:
two overlapping squares in `ℝ²` satisfy `RCC8.PO` (and `¬ Touches`) in `ℝ²`,
yet their images under `embedPlane 0` satisfy ambient `Touches` in `ℝ³`! -/
theorem intrinsic_po_but_ambient_touches_E2 :
    let r₁ : Rect := ⟨0, 2, 0, 2⟩
    let r₂ : Rect := ⟨1, 3, 0, 2⟩
    let A₁ := r₁.toRegularClosed (by norm_num) (by norm_num)
    let A₂ := r₂.toRegularClosed (by norm_num) (by norm_num)
    RCC8.PO A₁ A₂ ∧ ¬ Touches (A₁ : Region) (A₂ : Region) ∧
      Touches (embedPlane 0 '' (A₁ : Region)) (embedPlane 0 '' (A₂ : Region)) := by
  intro r₁ r₂ A₁ A₂
  have hPO : RCC8.PO A₁ A₂ := by
    refine ⟨⟨Point2D.mk (3 / 2) 1, ?_, ?_⟩, ?_, ?_⟩
    · rw [Rect.coe_toRegularClosed, Rect.interior_toRegion]
      exact ⟨by norm_num [r₁], by norm_num [r₁], by norm_num [r₁], by norm_num [r₁]⟩
    · rw [Rect.coe_toRegularClosed, Rect.interior_toRegion]
      exact ⟨by norm_num [r₂], by norm_num [r₂], by norm_num [r₂], by norm_num [r₂]⟩
    · intro hsub
      have h : Point2D.mk 0 0 ∈ r₂.toRegion :=
        hsub (show Point2D.mk 0 0 ∈ r₁.toRegion by simp [Rect.toRegion, r₁])
      norm_num [Rect.toRegion, r₂] at h
    · intro hsub
      have h : Point2D.mk 3 0 ∈ r₁.toRegion :=
        hsub (show Point2D.mk 3 0 ∈ r₂.toRegion by simp [Rect.toRegion, r₂])
      norm_num [Rect.toRegion, r₁] at h
  refine ⟨hPO, fun hT => hT.not_intersects_interior hPO.1, ?_⟩
  rw [ambient_touches_embedPlane_iff_intersects]
  exact hPO.1.mono (inter_subset_inter interior_subset interior_subset)

end Geospatial.Spaces
