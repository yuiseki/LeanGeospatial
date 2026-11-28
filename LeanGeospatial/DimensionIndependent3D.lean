import LeanGeospatial.Approximation2D3D
import LeanGeospatial.ConnectedComplete
import LeanGeospatial.Euclidean
import LeanGeospatial.Manifold

/-!
# Dimension-Independent Spatial Semantics and 3D DE-9IM Extension

## 1. Dimension-independent vs inherently 2D audit

In `LeanGeospatial`:

- **Already generalized to any `[TopologicalSpace α]`**:
  - Set relations: `Within`, `Contains`, `Intersects`, `Disjoint` (`Region.lean`)
  - Topological operators: `boundary`, `exterior`, `Touches`, `RegularClosedRegion α`,
    `Stratum`, `cell`, `Pattern` (`Topology.lean`, `RegularClosed.lean`, `NineIntersection.lean`, `DE9IM.lean`)
  - RCC8 base relations, pairwise disjointness, joint exhaustiveness, and composition
    table soundness (`RCC8.lean`, `Composition.lean`, `CompositionTable/Abstract.lean`)
  - Homeomorphism invariance (`Homeomorph.lean`)
  - Abstract `DimensionFunction α`, `de9im`, `CellPattern`, and `cubeDim n`
    (`DE9IM/DimensionFunction.lean`, `DE9IM/CubeDimension.lean`)

- **Topological conditions for RCC8**:
  - Pairwise disjointness, joint exhaustiveness, and composition-table **soundness**
    require NO topological separation or dimension assumptions beyond `[TopologicalSpace α]`
    and nonemptiness of `RegularClosedRegion α`.
  - Composition-table **completeness** (`RCC8Complete α`) fails in discrete spaces
    (`not_rcc8Complete_of_discrete`) and holds in every Euclidean space `ℝⁿ` for `n ≥ 1`
    (`rcc8Complete_euclideanSpace`), including `E3` (`rcc8Complete_euclideanSpace3`),
    as well as every nonempty Hausdorff 2-manifold (`rcc8Complete_of_chartedSpace`).
  - **Connected** RCC8 completeness (`RCC8ConnectedComplete α`) fails in `ℝ`
    (`not_rcc8ConnectedComplete_real`), holds in `E2` (`rcc8ConnectedComplete_plane`),
    and holds in `E3` (`rcc8ConnectedComplete_E3`, proved below via `e3HomeomorphProd`).

- **Inherently 2D**:
  - `Point2D`, `Polygon`, `Rect`, `LineString`, `Geometry`, `SFA.*`, `GeoSPARQL.*`,
    `DE9IM.DimValue` (`F, 0, 1, 2`), `planeDim = cubeDim 2`, `ComputationalPolygon`.

## 2. 3D DE-9IM Extension for 3D Solids (Non-OGC-Standard)

> **Important disclaimer**: The 3D DE-9IM definitions below (`de9im3D`) are a
> **mathematical topological extension** of DE-9IM to 3D Euclidean space `E3`
> using `cubeDim 3` with values in `{⊥, 0, 1, 2, 3}`. They are **NOT** part of
> OGC Simple Feature Access 1.2.1 (which is 2D) and do **NOT** claim OGC
> standard compliance.

Main results for 3D solids (`Solid3D := RegularClosedRegion E3`):
- `solid3D_II_cases`, `solid3D_IE_cases`, `solid3D_EI_cases`: open-set cells
  take only `⊥` or `3`.
- Exact 3D DE-9IM characterizations of `DC`, `EC`, `PO`, `EQ`, `TPP`, `NTPP`
  for nonempty 3D solids.
- `solid3D_ec_face_BB_eq_two` and `solid3D_ec_vertex_BB_eq_zero`: two touching
  3D boxes (`EC`) can share a 2D face (`BB = 2`) or a 0D vertex (`BB = 0`).
-/

namespace Geospatial.DE9IM3D

open Set Geospatial Geospatial.DE9IM Geospatial.DE9IM.Space3 Geospatial.Space2D3D

/-! ## Dimension-independent RCC8 conditions and 3D RCC8 theorems -/

/-- In ANY topological space `α`, nonempty `RegularClosedRegion`s satisfy RCC8
pairwise disjointness and joint exhaustiveness without any dimension or
separation assumptions. -/
theorem rcc8_existsUnique_any_space {α : Type*} [TopologicalSpace α]
    (A B : RegularClosedRegion α) (hA : (A : Set α).Nonempty) (hB : (B : Set α).Nonempty) :
    ∃! r : RCC8.Relation, r.holds A B :=
  RCC8.existsUnique_relation A B hA hB

/-- In 3D Euclidean space `E3`, the RCC8 composition table is both sound and
complete (`compose = table`). -/
theorem rcc8_compose_eq_table_E3 (r s : RCC8.Relation) :
    RCC8.compose (α := E3) r s = RCC8.table r s :=
  rcc8Complete_euclideanSpace3 r s

/-- In 3D Euclidean space `E3`, the RCC8 composition table is complete even when
restricted to **connected** 3D solids (proved by transferring `E2` connected
completeness along `e3HomeomorphProd : E3 ≃ₜ Point2D × ℝ`). -/
theorem rcc8ConnectedComplete_E3 : RCC8ConnectedComplete E3 :=
  (RCC8ConnectedComplete.homeomorph e3HomeomorphProd).mpr rcc8ConnectedComplete_plane.prod_right

/-! ## 3D Solids and Non-OGC 3D DE-9IM Extension -/

/-- A 3D solid: a regular closed region in `E3 := EuclideanSpace ℝ (Fin 3)`. -/
abbrev Solid3D := RegularClosedRegion E3

/-- **3D DE-9IM matrix** of two 3D solids using `cubeDim 3` (values in `{⊥, 0, 1, 2, 3}`).
Mathematical extension only; NOT OGC SFA compliant. -/
noncomputable def de9im3D (A B : Solid3D) (s t : Stratum) : WithBot ℕ :=
  de9im (cubeDim 3) (A : Set E3) B s t

/-- Any homeomorphism of `E3` preserves the 3D DE-9IM matrix. -/
theorem de9im3D_map (e : E3 ≃ₜ E3) (A B : Solid3D) :
    de9im3D (A.map e) (B.map e) = de9im3D A B :=
  de9im_map (cubeDim_compatible 3 e) (A : Set E3) B

/-- The `II` cell of two 3D solids is open, so its 3D DE-9IM value is `⊥` or `3`. -/
theorem solid3D_II_cases (A B : Solid3D) :
    de9im3D A B .I .I = ⊥ ∨ de9im3D A B .I .I = 3 := by
  by_cases h : (cell .I .I (A : Set E3) B).Nonempty
  · right
    apply cubeDim_of_interior
    have hopen : IsOpen (cell .I .I (A : Set E3) B) := isOpen_interior.inter isOpen_interior
    rwa [hopen.interior_eq]
  · left
    exact (de9im_eq_bot_iff (cubeDim 3) (A : Set E3) B .I .I).mpr
      (not_nonempty_iff_eq_empty.mp h)

/-- The `IE` cell of two 3D solids is open, so its 3D DE-9IM value is `⊥` or `3`. -/
theorem solid3D_IE_cases (A B : Solid3D) :
    de9im3D A B .I .E = ⊥ ∨ de9im3D A B .I .E = 3 := by
  by_cases h : (cell .I .E (A : Set E3) B).Nonempty
  · right
    apply cubeDim_of_interior
    have hopen : IsOpen (cell .I .E (A : Set E3) B) := isOpen_interior.inter isOpen_interior
    rwa [hopen.interior_eq]
  · left
    exact (de9im_eq_bot_iff (cubeDim 3) (A : Set E3) B .I .E).mpr
      (not_nonempty_iff_eq_empty.mp h)

/-- The `EI` cell of two 3D solids is open, so its 3D DE-9IM value is `⊥` or `3`. -/
theorem solid3D_EI_cases (A B : Solid3D) :
    de9im3D A B .E .I = ⊥ ∨ de9im3D A B .E .I = 3 := by
  by_cases h : (cell .E .I (A : Set E3) B).Nonempty
  · right
    apply cubeDim_of_interior
    have hopen : IsOpen (cell .E .I (A : Set E3) B) := isOpen_interior.inter isOpen_interior
    rwa [hopen.interior_eq]
  · left
    exact (de9im_eq_bot_iff (cubeDim 3) (A : Set E3) B .E .I).mpr
      (not_nonempty_iff_eq_empty.mp h)

/-! ## 3D RCC8 ↔ 3D DE-9IM Characterizations -/

theorem dc_iff_de9im3D (A B : Solid3D) :
    RCC8.DC A B ↔
      de9im3D A B .I .I = ⊥ ∧ de9im3D A B .I .B = ⊥ ∧
      de9im3D A B .B .I = ⊥ ∧ de9im3D A B .B .B = ⊥ := by
  rw [RCC8.dc_iff_cells]
  simp only [de9im3D, de9im_eq_bot_iff, II, IB, BI, BB]

theorem ec_iff_de9im3D (A B : Solid3D) :
    RCC8.EC A B ↔
      de9im3D A B .I .I = ⊥ ∧ de9im3D A B .I .B = ⊥ ∧
      de9im3D A B .B .I = ⊥ ∧ de9im3D A B .B .B ≠ ⊥ := by
  simp only [de9im3D, de9im_eq_bot_iff, de9im_ne_bot_iff]
  constructor
  · intro hEC
    have hsub := A.inter_subset_boundary_of_touches B hEC
    have hII : cell .I .I (A : Set E3) B = ∅ := hEC.2
    have hIB : cell .I .B (A : Set E3) B = ∅ := by
      rw [eq_empty_iff_forall_notMem]
      rintro p ⟨hpI, hpB⟩
      have hB : p ∈ (B : Set E3) := B.isClosed.closure_eq ▸ hpB.1
      exact (hsub ⟨interior_subset hpI, hB⟩).1.2 hpI
    have hBI : cell .B .I (A : Set E3) B = ∅ := by
      rw [eq_empty_iff_forall_notMem]
      rintro p ⟨hpB, hpI⟩
      have hA : p ∈ (A : Set E3) := A.isClosed.closure_eq ▸ hpB.1
      exact (hsub ⟨hA, interior_subset hpI⟩).2.2 hpI
    obtain ⟨p, hpA, hpB⟩ := hEC.1
    exact ⟨hII, hIB, hBI, ⟨p, hsub ⟨hpA, hpB⟩⟩⟩
  · rintro ⟨hII, -, -, ⟨p, hpA, hpB⟩⟩
    exact ⟨⟨p, A.isClosed.closure_eq ▸ hpA.1, B.isClosed.closure_eq ▸ hpB.1⟩, hII⟩

theorem po_iff_de9im3D (A B : Solid3D) :
    RCC8.PO A B ↔
      de9im3D A B .I .I = 3 ∧ de9im3D A B .I .E = 3 ∧ de9im3D A B .E .I = 3 := by
  rw [RCC8.po_iff_cells]
  have h1 : (II (A : Set E3) B).Nonempty ↔ de9im3D A B .I .I = 3 := by
    rw [← de9im_ne_bot_iff (cubeDim 3) (A : Set E3) B .I .I]
    rcases solid3D_II_cases A B with h | h <;> simp [de9im3D] at h ⊢ <;> simp [h]
  have h2 : (IE (A : Set E3) B).Nonempty ↔ de9im3D A B .I .E = 3 := by
    rw [← de9im_ne_bot_iff (cubeDim 3) (A : Set E3) B .I .E]
    rcases solid3D_IE_cases A B with h | h <;> simp [de9im3D] at h ⊢ <;> simp [h]
  have h3 : (EI (A : Set E3) B).Nonempty ↔ de9im3D A B .E .I = 3 := by
    rw [← de9im_ne_bot_iff (cubeDim 3) (A : Set E3) B .E .I]
    rcases solid3D_EI_cases A B with h | h <;> simp [de9im3D] at h ⊢ <;> simp [h]
  rw [h1, h2, h3]

/-! ## 3D `EC` Boundary Dimension Witnesses (`BB = 2` face vs `BB = 0` vertex) -/

/-- Two 3D unit cubes `[0, 1]³` and `[0, 1] × [0, 1] × [1, 2]` are externally
connected (`EC`) and share a 2D face (`BB = 2`). -/
theorem solid3D_ec_face_BB_eq_two :
    let r : Rect := ⟨0, 1, 0, 1⟩
    let A : Solid3D := extrudeRegularClosed (by norm_num : (0 : ℝ) < 1)
      (r.toRegularClosed (by norm_num) (by norm_num))
    let B : Solid3D := extrudeRegularClosed (by norm_num : (1 : ℝ) < 2)
      (r.toRegularClosed (by norm_num) (by norm_num))
    RCC8.EC A B ∧ de9im3D A B .B .B = 2 := by
  intro r A B
  have hA_int : interior (A : Set E3) = e3HomeomorphProd ⁻¹' (r.openRegion ×ˢ Ioo 0 1) := by
    change interior (extrude 0 1 r.toRegion) = _
    rw [interior_extrude, Rect.interior_toRegion]
  have hB_int : interior (B : Set E3) = e3HomeomorphProd ⁻¹' (r.openRegion ×ˢ Ioo 1 2) := by
    change interior (extrude 1 2 r.toRegion) = _
    rw [interior_extrude, Rect.interior_toRegion]
  have hEC : RCC8.EC A B := by
    refine ⟨⟨pt 0 0 1, ⟨⟨by norm_num [r], by norm_num [r], by norm_num [r], by norm_num [r]⟩,
      ⟨by norm_num, by norm_num⟩⟩,
      ⟨⟨by norm_num [r], by norm_num [r], by norm_num [r], by norm_num [r]⟩,
      ⟨by norm_num, by norm_num⟩⟩⟩, ?_⟩
    rw [Geospatial.Disjoint, hA_int, hB_int, eq_empty_iff_forall_notMem]
    rintro p ⟨h1, h2⟩
    linarith [h1.2.2, h2.2.1]
  refine ⟨hEC, ?_⟩
  have hBB_flat : ∀ p ∈ cell .B .B (A : Set E3) B, p 2 = 1 := by
    rintro p ⟨hpA, hpB⟩
    have hA1 : p ∈ (A : Set E3) := A.isClosed.closure_eq ▸ hpA.1
    have hB1 : p ∈ (B : Set E3) := B.isClosed.closure_eq ▸ hpB.1
    change projXY p ∈ r.toRegion ∧ p 2 ∈ Icc (0 : ℝ) 1 at hA1
    change projXY p ∈ r.toRegion ∧ p 2 ∈ Icc (1 : ℝ) 2 at hB1
    linarith [hA1.2.2, hB1.2.1]
  have hBB_int_empty : interior (cell .B .B (A : Set E3) B) = ∅ := by
    rw [eq_empty_iff_forall_notMem]
    intro x hx
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hx)
    have hx2 : x 2 = 1 := hBB_flat x (interior_subset hx)
    set y : E3 := x + (ε / 2) • EuclideanSpace.single 2 1
    have hy : y ∈ Metric.ball x ε := by
      rw [Metric.mem_ball, dist_eq_norm, show y - x = (ε / 2) • EuclideanSpace.single 2 1 by
        simp [y], norm_smul, PiLp.norm_single, norm_one, mul_one,
        Real.norm_of_nonneg (by positivity)]
      linarith
    have hy2 := hBB_flat y (hball hy)
    simp [y, hx2] at hy2
    linarith
  have hcube : HasCube 2 (cell .B .B (A : Set E3) B) := by
    refine ⟨fun x : Fin 2 → ℝ => pt (x 0) (x 1) 1,
      (continuous_pt (continuous_apply 0) (continuous_apply 1) continuous_const).continuousOn,
      fun x _ y _ h => ?_, ?_⟩
    · have h0 := congrArg (fun p : E3 => p 0) h
      have h1 := congrArg (fun p : E3 => p 1) h
      ext i; fin_cases i
      · exact h0
      · exact h1
    · rintro _ ⟨x, hx, rfl⟩
      have hx0 : x 0 ∈ Icc (0 : ℝ) 1 := ⟨hx.1 0, hx.2 0⟩
      have hx1 : x 1 ∈ Icc (0 : ℝ) 1 := ⟨hx.1 1, hx.2 1⟩
      have hmemA : pt (x 0) (x 1) 1 ∈ (A : Set E3) :=
        ⟨⟨hx0.1, hx0.2, hx1.1, hx1.2⟩, ⟨by norm_num, by norm_num⟩⟩
      have hmemB : pt (x 0) (x 1) 1 ∈ (B : Set E3) :=
        ⟨⟨hx0.1, hx0.2, hx1.1, hx1.2⟩, ⟨by norm_num, by norm_num⟩⟩
      exact A.mem_boundary_of_touches B hEC hmemA hmemB
  exact cubeDim_of_cube (k := 2) ⟨pt 0 0 1, A.mem_boundary_of_touches B hEC
    ⟨⟨by norm_num [r], by norm_num [r], by norm_num [r], by norm_num [r]⟩, ⟨by norm_num, by norm_num⟩⟩
    ⟨⟨by norm_num [r], by norm_num [r], by norm_num [r], by norm_num [r]⟩, ⟨by norm_num, by norm_num⟩⟩⟩
    hBB_int_empty (by norm_num) hcube fun j hj hj2 => by omega

/-- Two 3D unit cubes `[0, 1]³` and `[1, 2]³` are externally connected (`EC`)
and meet only at the single vertex `(1, 1, 1)` (`BB = 0`). -/
theorem solid3D_ec_vertex_BB_eq_zero :
    let rA : Rect := ⟨0, 1, 0, 1⟩
    let rB : Rect := ⟨1, 2, 1, 2⟩
    let A : Solid3D := extrudeRegularClosed (by norm_num : (0 : ℝ) < 1)
      (rA.toRegularClosed (by norm_num) (by norm_num))
    let B : Solid3D := extrudeRegularClosed (by norm_num : (1 : ℝ) < 2)
      (rB.toRegularClosed (by norm_num) (by norm_num))
    RCC8.EC A B ∧ de9im3D A B .B .B = 0 := by
  intro rA rB A B
  have hA_int : interior (A : Set E3) = e3HomeomorphProd ⁻¹' (rA.openRegion ×ˢ Ioo 0 1) := by
    change interior (extrude 0 1 rA.toRegion) = _
    rw [interior_extrude, Rect.interior_toRegion]
  have hB_int : interior (B : Set E3) = e3HomeomorphProd ⁻¹' (rB.openRegion ×ˢ Ioo 1 2) := by
    change interior (extrude 1 2 rB.toRegion) = _
    rw [interior_extrude, Rect.interior_toRegion]
  have hmemA : pt 1 1 1 ∈ (A : Set E3) :=
    ⟨⟨by norm_num [rA], by norm_num [rA], by norm_num [rA], by norm_num [rA]⟩,
      ⟨by norm_num, by norm_num⟩⟩
  have hmemB : pt 1 1 1 ∈ (B : Set E3) :=
    ⟨⟨by norm_num [rB], by norm_num [rB], by norm_num [rB], by norm_num [rB]⟩,
      ⟨by norm_num, by norm_num⟩⟩
  have hEC : RCC8.EC A B := by
    refine ⟨⟨pt 1 1 1, hmemA, hmemB⟩, ?_⟩
    rw [Geospatial.Disjoint, hA_int, hB_int, eq_empty_iff_forall_notMem]
    rintro p ⟨h1, h2⟩
    linarith [h1.2.2, h2.2.1]
  have hBB_sub : cell .B .B (A : Set E3) B ⊆ {pt 1 1 1} := by
    rintro p ⟨hpA, hpB⟩
    have hA1 : p ∈ (A : Set E3) := A.isClosed.closure_eq ▸ hpA.1
    have hB1 : p ∈ (B : Set E3) := B.isClosed.closure_eq ▸ hpB.1
    change (0 ≤ p 0 ∧ p 0 ≤ 1 ∧ 0 ≤ p 1 ∧ p 1 ≤ 1) ∧ p 2 ∈ Icc (0 : ℝ) 1 at hA1
    change (1 ≤ p 0 ∧ p 0 ≤ 2 ∧ 1 ≤ p 1 ∧ p 1 ≤ 2) ∧ p 2 ∈ Icc (1 : ℝ) 2 at hB1
    rw [mem_singleton_iff]
    ext i
    fin_cases i
    · change p 0 = 1; linarith [hA1.1.2.1, hB1.1.1]
    · change p 1 = 1; linarith [hA1.1.2.2.2, hB1.1.2.2.1]
    · change p 2 = 1; linarith [hA1.2.2, hB1.2.1]
  have hne : (cell .B .B (A : Set E3) B).Nonempty :=
    ⟨pt 1 1 1, A.mem_boundary_of_touches B hEC hmemA hmemB⟩
  have hint_empty : interior (cell .B .B (A : Set E3) B) = ∅ :=
    eq_empty_of_subset_empty ((interior_mono hBB_sub).trans (interior_singleton _).subset)
  refine ⟨hEC, cubeDim_of_cube (k := 0) hne hint_empty (by norm_num) (hasCube_zero_iff.mpr hne)
    fun j hj _ => not_hasCube_of_subsingleton hj (subsingleton_singleton.anti hBB_sub)⟩

end Geospatial.DE9IM3D
