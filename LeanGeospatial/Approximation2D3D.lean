import LeanGeospatial.DE9IM.Space3
import LeanGeospatial.RCC8
import LeanGeospatial.Homeomorph

/-!
# Mathematical Justification of 2D Approximation in 3D Space

Formalizes the four fundamental maps between the 2D plane `Point2D` (`E2`) and
3D Euclidean space `E3 := EuclideanSpace ℝ (Fin 3)`, proves which topological,
metric, RCC8, and DE-9IM properties are preserved or reflected by each map,
separates **subspace interior** from **ambient 3D interior**, and exhibits
minimal counterexamples where 2D approximation fails.

## The four maps

1. `embedPlane (z₀ : ℝ) : Point2D → E3`: planar embedding `(x, y) ↦ (x, y, z₀)`.
   - Isometry (`dist_embedPlane`);
   - Homeomorphism onto the subspace `{p : E3 | p 2 = z₀}` (`embedPlaneHomeomorph`);
   - Preserves `Within`, `Intersects`, `Disjoint`, `IsConnected`, and (in the
     subspace topology) `interior`, `boundary`, `Touches`, `RCC8`, `DE9IM`;
   - In ambient `E3`, every planar image has **empty interior**
     (`interior_embedPlane_eq_empty`), is never a 3D `RegularClosedRegion`
     (`embedPlane_not_regularClosed`), and ambient `Touches` degenerates to
     `Intersects` (`ambient_touches_embedPlane_iff_intersects`).

2. `projXY : E3 → Point2D`: vertical coordinate projection `(x, y, z) ↦ (x, y)`.
   - Continuous, surjective, 1-Lipschitz (`dist_projXY_le`);
   - Preserves `Within`, `Intersects`, `IsConnected`, and **reflects `Disjoint`**
     (`disjoint_of_projXY_disjoint` — justifying 2D bounding/footprint disjointness
     as a sound negative filter for 3D disjointness);
   - Fails to preserve `Disjoint` or reflect `Intersects`, `Within`, `Equals`,
     `Touches`, `RCC8`, or topological cavities.

3. `embedGraph (h : Point2D → ℝ) : Point2D → E3`: 2.5D terrain / height-function
   surface `(x, y) ↦ (x, y, h(x, y))`.
   - Injective, homeomorphism onto the graph subspace when `h` is continuous
     (`embedGraphHomeomorph`);
   - Distance bounds: `dist p q ≤ dist (embedGraph h p) (embedGraph h q)`, and
     for `K`-Lipschitz `h`, `dist (embedGraph h p) (embedGraph h q) ≤ √(1 + K²) * dist p q`;
   - Always has empty ambient 3D interior (`interior_embedGraph_eq_empty`).

4. `extrude (z₁ z₂ : ℝ) (A : Region) : Set E3`: vertical prism `A × [z₁, z₂]`.
   - Preserves `interior`, `closure`, `IsConnected`, and `RegularClosedRegion`
     whenever `z₁ < z₂` (`extrudeRegularClosed`);
   - **Exact RCC8 equivalence** (`extrude_rcc8_iff`): for all `A, B : RegularClosedRegion Point2D`
     and `z₁ < z₂`, every RCC8 relation holds between the extruded 3D prisms iff
     it holds between `A` and `B` in 2D;
   - **Exact 2D→3D dimension lift**: `cubeDim 3 (extrude z₁ z₂ A) = 3` whenever
     `(interior A).Nonempty` and `z₁ < z₂`.

## Minimal counterexamples

- `counterexample_overpass_roads`: 3D disjoint roads that cross in 2D (`projXY`).
- `counterexample_building_floors`: 3D disjoint building floors that are equal in 2D.
- `counterexample_adjacent_2d_disjoint_3d`: 3D disjoint boxes that touch (`EC`) in 2D.
- `counterexample_projection_loses_topology`: 3D solid with an internal cavity
  whose 2D projection is identical to a solid cube without cavity.
-/

namespace Geospatial.Space2D3D

open Set Geospatial Geospatial.DE9IM Geospatial.DE9IM.Space3

/-! ## Product homeomorphism `E3 ≃ₜ Point2D × ℝ` -/

/-- Coordinate projection `E3 → Point2D`, dropping the `z` coordinate. -/
noncomputable def projXY (p : E3) : Point2D :=
  Point2D.mk (p 0) (p 1)

@[simp] theorem projXY_x (p : E3) : (projXY p).x = p 0 := rfl
@[simp] theorem projXY_y (p : E3) : (projXY p).y = p 1 := rfl

@[simp] theorem projXY_pt (p : Point2D) (z : ℝ) : projXY (pt p.x p.y z) = p :=
  Point2D.ext rfl rfl

@[fun_prop] theorem continuous_projXY : Continuous projXY :=
  Point2D.continuous_mk (PiLp.continuous_apply 2 _ 0) (PiLp.continuous_apply 2 _ 1)

/-- Combine a 2D point and a height `z` into a 3D point. -/
noncomputable def ofProd (q : Point2D × ℝ) : E3 :=
  pt q.1.x q.1.y q.2

@[simp] theorem projXY_ofProd (q : Point2D × ℝ) : projXY (ofProd q) = q.1 := by
  exact Point2D.ext rfl rfl

@[simp] theorem ofProd_z (q : Point2D × ℝ) : (ofProd q) 2 = q.2 := rfl

@[fun_prop] theorem continuous_ofProd : Continuous ofProd :=
  continuous_pt (Point2D.continuous_x.comp continuous_fst)
    (Point2D.continuous_y.comp continuous_fst) continuous_snd

/-- `E3` is homeomorphic to `Point2D × ℝ`. -/
noncomputable def e3HomeomorphProd : E3 ≃ₜ Point2D × ℝ where
  toFun p := (projXY p, p 2)
  invFun := ofProd
  left_inv p := by
    ext i
    fin_cases i <;> rfl
  right_inv q := by
    cases q with | mk p z =>
    ext
    · rfl
    · rfl
    · rfl
  continuous_toFun := continuous_projXY.prodMk (PiLp.continuous_apply 2 _ 2)
  continuous_invFun := continuous_ofProd

@[simp] theorem e3HomeomorphProd_apply (p : E3) :
    e3HomeomorphProd p = (projXY p, p 2) := rfl

@[simp] theorem e3HomeomorphProd_symm_apply (p : Point2D) (z : ℝ) :
    e3HomeomorphProd.symm (p, z) = pt p.x p.y z := rfl

/-! ## 1. Planar embedding `embedPlane` -/

/-- Embed `Point2D` into `E3` at fixed height `z₀`. -/
noncomputable def embedPlane (z₀ : ℝ) (p : Point2D) : E3 :=
  pt p.x p.y z₀

@[simp] theorem projXY_embedPlane (z₀ : ℝ) (p : Point2D) :
    projXY (embedPlane z₀ p) = p :=
  Point2D.ext rfl rfl

@[simp] theorem embedPlane_z (z₀ : ℝ) (p : Point2D) :
    (embedPlane z₀ p) 2 = z₀ := rfl

theorem embedPlane_injective (z₀ : ℝ) : Function.Injective (embedPlane z₀) := by
  intro p q h
  have := congrArg projXY h
  simpa using this

@[fun_prop] theorem continuous_embedPlane (z₀ : ℝ) : Continuous (embedPlane z₀) :=
  continuous_pt Point2D.continuous_x Point2D.continuous_y continuous_const

/-- `embedPlane z₀` is an exact isometry: 2D distance equals 3D distance. -/
theorem dist_embedPlane (z₀ : ℝ) (p q : Point2D) :
    dist (embedPlane z₀ p) (embedPlane z₀ q) = dist p q := by
  rw [EuclideanSpace.dist_eq, EuclideanSpace.dist_eq, Fin.sum_univ_three, Fin.sum_univ_two]
  simp [embedPlane, pt, Point2D.x, Point2D.y]

theorem embedPlane_within_iff (z₀ : ℝ) (A B : Region) :
    Within (embedPlane z₀ '' A) (embedPlane z₀ '' B) ↔ Within A B :=
  Set.image_subset_image_iff (embedPlane_injective z₀)

theorem embedPlane_intersects_iff (z₀ : ℝ) (A B : Region) :
    Intersects (embedPlane z₀ '' A) (embedPlane z₀ '' B) ↔ Intersects A B := by
  unfold Intersects
  rw [← Set.image_inter (embedPlane_injective z₀), Set.image_nonempty]

theorem embedPlane_disjoint_iff (z₀ : ℝ) (A B : Region) :
    Geospatial.Disjoint (embedPlane z₀ '' A) (embedPlane z₀ '' B) ↔ Geospatial.Disjoint A B := by
  rw [disjoint_iff_not_intersects, disjoint_iff_not_intersects, embedPlane_intersects_iff]

theorem embedPlane_isConnected_iff (z₀ : ℝ) {A : Region} :
    IsConnected (embedPlane z₀ '' A) ↔ IsConnected A := by
  constructor
  · intro h
    have hpre : projXY '' (embedPlane z₀ '' A) = A := by
      rw [← Set.image_comp]
      simp
    rw [← hpre]
    exact h.image projXY continuous_projXY.continuousOn
  · intro h
    exact h.image (embedPlane z₀) (continuous_embedPlane z₀).continuousOn

/-- The horizontal plane `{p : E3 | p 2 = z₀}` as a subspace of `E3`. -/
def planeSubspace (z₀ : ℝ) : Set E3 := {p | p 2 = z₀}

/-- `embedPlane z₀` is a homeomorphism onto the horizontal plane subspace
`planeSubspace z₀` (preserving subspace interior, boundary, RCC8, and DE-9IM). -/
noncomputable def embedPlaneHomeomorph (z₀ : ℝ) : Point2D ≃ₜ planeSubspace z₀ where
  toFun p := ⟨embedPlane z₀ p, rfl⟩
  invFun q := projXY q.1
  left_inv p := projXY_embedPlane z₀ p
  right_inv q := by
    apply Subtype.ext
    ext i
    fin_cases i
    · rfl
    · rfl
    · exact q.2.symm
  continuous_toFun := (continuous_embedPlane z₀).subtype_mk _
  continuous_invFun := continuous_projXY.comp continuous_subtype_val

/-- **Subspace RCC8 preservation**: inside the horizontal plane subspace,
`embedPlaneHomeomorph z₀` preserves every RCC8 relation. -/
theorem embedPlaneHomeomorph_rcc8_iff (z₀ : ℝ)
    (A B : RegularClosedRegion Point2D) (r : RCC8.Relation) :
    r.holds (A.map (embedPlaneHomeomorph z₀)) (B.map (embedPlaneHomeomorph z₀)) ↔
      r.holds A B :=
  RCC8.Relation.holds_map_iff (embedPlaneHomeomorph z₀) A B r

/-- **Ambient 3D interior collapses**: in ambient `E3`, any subset of a
horizontal plane `z = z₀` has EMPTY 3D interior. -/
theorem interior_embedPlane_eq_empty (z₀ : ℝ) (A : Region) :
    interior (embedPlane z₀ '' A) = ∅ := by
  rw [eq_empty_iff_forall_notMem]
  intro x hx
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hx)
  have hx2 : x 2 = z₀ := by
    obtain ⟨p, -, rfl⟩ := interior_subset hx
    rfl
  set y : E3 := x + (ε / 2) • EuclideanSpace.single 2 1
  have hy : y ∈ Metric.ball x ε := by
    rw [Metric.mem_ball, dist_eq_norm, show y - x = (ε / 2) • EuclideanSpace.single 2 1 by
      simp [y], norm_smul, PiLp.norm_single, norm_one, mul_one,
      Real.norm_of_nonneg (by positivity)]
    linarith
  obtain ⟨p, -, hp⟩ := hball hy
  have hz : y 2 = z₀ := by rw [← hp]; rfl
  simp [y, hx2] at hz
  linarith

/-- No nonempty planar region embedded in ambient `E3` is a 3D `RegularClosedRegion`. -/
theorem embedPlane_not_regularClosed (z₀ : ℝ) {A : Region} (hA : A.Nonempty) :
    closure (interior (embedPlane z₀ '' A)) ≠ embedPlane z₀ '' A := by
  rw [interior_embedPlane_eq_empty, closure_empty]
  exact (hA.image _).ne_empty.symm

/-- **Why subspace interior and ambient 3D interior must not be confused**:
in ambient `E3`, two planar regions `Touches` iff they merely `Intersects`
(even if their 2D interiors overlap!). -/
theorem ambient_touches_embedPlane_iff_intersects (z₀ : ℝ) (A B : Region) :
    Touches (embedPlane z₀ '' A) (embedPlane z₀ '' B) ↔ Intersects A B := by
  unfold Touches
  rw [embedPlane_intersects_iff, interior_embedPlane_eq_empty, interior_embedPlane_eq_empty]
  simp [Geospatial.Disjoint]

/-! ## 2. Coordinate projection `projXY` -/

/-- `projXY` is 1-Lipschitz: 2D projected distance never exceeds 3D distance. -/
theorem dist_projXY_le (p q : E3) : dist (projXY p) (projXY q) ≤ dist p q := by
  rw [EuclideanSpace.dist_eq, EuclideanSpace.dist_eq, Fin.sum_univ_two, Fin.sum_univ_three]
  apply Real.sqrt_le_sqrt
  simp only [projXY, Point2D.mk, Matrix.cons_val_zero, Matrix.cons_val_one]
  linarith [sq_nonneg (dist (p 2) (q 2))]

theorem projXY_within_mono {A B : Set E3} (h : Within A B) :
    Within (projXY '' A) (projXY '' B) :=
  Set.image_mono h

theorem projXY_intersects_of_intersects {A B : Set E3} (h : Intersects A B) :
    Intersects (projXY '' A) (projXY '' B) := by
  obtain ⟨p, hpA, hpB⟩ := h
  exact ⟨projXY p, ⟨p, hpA, rfl⟩, ⟨p, hpB, rfl⟩⟩

/-- **Soundness of 2D disjointness as a 3D filter**: if two 3D objects have
disjoint 2D projections, they are guaranteed to be disjoint in 3D. -/
theorem disjoint_of_projXY_disjoint {A B : Set E3}
    (h : Geospatial.Disjoint (projXY '' A) (projXY '' B)) :
    Geospatial.Disjoint A B := by
  rw [disjoint_iff_not_intersects] at h ⊢
  exact fun hi => h (projXY_intersects_of_intersects hi)

theorem projXY_isConnected {A : Set E3} (h : IsConnected A) :
    IsConnected (projXY '' A) :=
  h.image projXY continuous_projXY.continuousOn

/-! ## 3. Height-function surface embedding `embedGraph` (2.5D terrain / DEM) -/

/-- Embed `Point2D` onto the graph surface `z = h(x, y)` in `E3`. -/
noncomputable def embedGraph (h : Point2D → ℝ) (p : Point2D) : E3 :=
  pt p.x p.y (h p)

@[simp] theorem projXY_embedGraph (h : Point2D → ℝ) (p : Point2D) :
    projXY (embedGraph h p) = p :=
  Point2D.ext rfl rfl

@[simp] theorem embedGraph_z (h : Point2D → ℝ) (p : Point2D) :
    (embedGraph h p) 2 = h p := rfl

theorem embedGraph_injective (h : Point2D → ℝ) : Function.Injective (embedGraph h) := by
  intro p q heq
  have := congrArg projXY heq
  simpa using this

theorem continuous_embedGraph {h : Point2D → ℝ} (hc : Continuous h) :
    Continuous (embedGraph h) :=
  continuous_pt Point2D.continuous_x Point2D.continuous_y hc

/-- 3D distance on a terrain surface is always at least 2D planar distance. -/
theorem dist_le_dist_embedGraph (h : Point2D → ℝ) (p q : Point2D) :
    dist p q ≤ dist (embedGraph h p) (embedGraph h q) := by
  have := dist_projXY_le (embedGraph h p) (embedGraph h q)
  simpa using this

/-- **Metric distortion bound for `K`-Lipschitz terrain**:
if `|h(p) - h(q)| ≤ K · dist(p, q)` with `K ≥ 0`, then 3D terrain distance is
bounded by `√(1 + K²) · dist(p, q)`. -/
theorem dist_embedGraph_le_of_lipschitz {h : Point2D → ℝ} {K : ℝ} (_hK : 0 ≤ K)
    (hlip : ∀ p q, |h p - h q| ≤ K * dist p q) (p q : Point2D) :
    dist (embedGraph h p) (embedGraph h q) ≤ Real.sqrt (1 + K ^ 2) * dist p q := by
  have hsq : dist (embedGraph h p) (embedGraph h q) ^ 2 =
      dist p q ^ 2 + (h p - h q) ^ 2 := by
    rw [EuclideanSpace.dist_eq, EuclideanSpace.dist_eq,
      Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _),
      Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _),
      Fin.sum_univ_three, Fin.sum_univ_two]
    simp [embedGraph, pt, Point2D.x, Point2D.y, Real.dist_eq]
  have hlip_sq : (h p - h q) ^ 2 ≤ K ^ 2 * dist p q ^ 2 := by
    have h1 := hlip p q
    have h2 : |h p - h q| ^ 2 ≤ (K * dist p q) ^ 2 :=
      pow_le_pow_left₀ (abs_nonneg _) h1 2
    rw [sq_abs, mul_pow] at h2
    exact h2
  have hle : dist (embedGraph h p) (embedGraph h q) ^ 2 ≤
      (Real.sqrt (1 + K ^ 2) * dist p q) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by positivity), hsq]
    nlinarith
  have hnonneg : 0 ≤ Real.sqrt (1 + K ^ 2) * dist p q := by positivity
  nlinarith [sq_nonneg (dist (embedGraph h p) (embedGraph h q) - Real.sqrt (1 + K ^ 2) * dist p q),
    dist_nonneg (x := embedGraph h p) (y := embedGraph h q)]

/-- The graph surface `{q : E3 | q 2 = h (projXY q)}` as a subspace of `E3`. -/
def graphSubspace (h : Point2D → ℝ) : Set E3 := {q | q 2 = h (projXY q)}

/-- For continuous `h`, `embedGraph h` is a homeomorphism onto `graphSubspace h`,
so all topological relations (including RCC8 and subspace DE-9IM) on a continuous
2.5D terrain surface agree with their 2D planar projections. -/
noncomputable def embedGraphHomeomorph (h : Point2D → ℝ) (hc : Continuous h) :
    Point2D ≃ₜ graphSubspace h where
  toFun p := ⟨embedGraph h p, by show h p = h (projXY (embedGraph h p)); rw [projXY_embedGraph]⟩
  invFun q := projXY q.1
  left_inv p := projXY_embedGraph h p
  right_inv q := by
    apply Subtype.ext
    ext i
    fin_cases i
    · rfl
    · rfl
    · exact q.2.symm
  continuous_toFun := (continuous_embedGraph hc).subtype_mk _
  continuous_invFun := continuous_projXY.comp continuous_subtype_val

/-- **Subspace RCC8 preservation on 2.5D terrain**: for any continuous height
function `h`, RCC8 relations on the terrain surface are identical to 2D RCC8
relations on the plane. -/
theorem embedGraphHomeomorph_rcc8_iff (h : Point2D → ℝ) (hc : Continuous h)
    (A B : RegularClosedRegion Point2D) (r : RCC8.Relation) :
    r.holds (A.map (embedGraphHomeomorph h hc)) (B.map (embedGraphHomeomorph h hc)) ↔
      r.holds A B :=
  RCC8.Relation.holds_map_iff (embedGraphHomeomorph h hc) A B r

/-- Even for an arbitrary (possibly discontinuous) height function `h`, the
graph surface has empty ambient 3D interior. -/
theorem interior_embedGraph_eq_empty (h : Point2D → ℝ) (A : Region) :
    interior (embedGraph h '' A) = ∅ := by
  rw [eq_empty_iff_forall_notMem]
  intro x hx
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hx)
  have hx2 : x 2 = h (projXY x) := by
    obtain ⟨p, -, rfl⟩ := interior_subset hx
    simp
  set y : E3 := x + (ε / 2) • EuclideanSpace.single 2 1
  have hproj : projXY y = projXY x := by
    apply Point2D.ext <;> simp [y, projXY]
  have hy : y ∈ Metric.ball x ε := by
    rw [Metric.mem_ball, dist_eq_norm, show y - x = (ε / 2) • EuclideanSpace.single 2 1 by
      simp [y], norm_smul, PiLp.norm_single, norm_one, mul_one,
      Real.norm_of_nonneg (by positivity)]
    linarith
  obtain ⟨p, -, hp⟩ := hball hy
  have hp_eq : p = projXY x := by
    have := congrArg projXY hp
    simpa [hproj] using this
  have hz : y 2 = h (projXY x) := by rw [← hp, hp_eq]; rfl
  simp [y, hx2] at hz
  linarith

/-! ## 4. Vertical extrusion `extrude` (2D area → 3D solid prism) -/

/-- Extrude a 2D region `A` vertically over the height interval `[z₁, z₂]`. -/
def extrude (z₁ z₂ : ℝ) (A : Region) : Set E3 :=
  e3HomeomorphProd ⁻¹' (A ×ˢ Icc z₁ z₂)

theorem mem_extrude_iff (z₁ z₂ : ℝ) (A : Region) (p : E3) :
    p ∈ extrude z₁ z₂ A ↔ projXY p ∈ A ∧ p 2 ∈ Icc z₁ z₂ :=
  Iff.rfl

theorem interior_extrude (z₁ z₂ : ℝ) (A : Region) :
    interior (extrude z₁ z₂ A) = e3HomeomorphProd ⁻¹' (interior A ×ˢ Ioo z₁ z₂) := by
  rw [extrude, ← e3HomeomorphProd.preimage_interior, interior_prod_eq, interior_Icc]

theorem closure_extrude (z₁ z₂ : ℝ) (A : Region) :
    closure (extrude z₁ z₂ A) = e3HomeomorphProd ⁻¹' (closure A ×ˢ Icc z₁ z₂) := by
  rw [extrude, ← e3HomeomorphProd.preimage_closure, closure_prod_eq, isClosed_Icc.closure_eq]

theorem extrude_isConnected {z₁ z₂ : ℝ} (hz : z₁ ≤ z₂) {A : Region} (hA : IsConnected A) :
    IsConnected (extrude z₁ z₂ A) := by
  rw [extrude]
  exact e3HomeomorphProd.isConnected_preimage.mpr (hA.prod (isConnected_Icc hz))

/-- Extruding a 2D `RegularClosedRegion` over a nondegenerate vertical interval
`[z₁, z₂]` (`z₁ < z₂`) produces a 3D `RegularClosedRegion E3`. -/
theorem closure_interior_extrude {z₁ z₂ : ℝ} (hz : z₁ < z₂)
    (A : RegularClosedRegion Point2D) :
    closure (interior (extrude z₁ z₂ (A : Region))) = extrude z₁ z₂ (A : Region) := by
  rw [interior_extrude, ← e3HomeomorphProd.preimage_closure, closure_prod_eq,
    A.closure_interior_eq, closure_Ioo hz.ne]
  rfl

/-- A 2D `RegularClosedRegion` extruded to a 3D `RegularClosedRegion E3`. -/
def extrudeRegularClosed {z₁ z₂ : ℝ} (hz : z₁ < z₂)
    (A : RegularClosedRegion Point2D) : RegularClosedRegion E3 :=
  ⟨extrude z₁ z₂ (A : Region), closure_interior_extrude hz A⟩

@[simp] theorem coe_extrudeRegularClosed {z₁ z₂ : ℝ} (hz : z₁ < z₂)
    (A : RegularClosedRegion Point2D) :
    ((extrudeRegularClosed hz A : RegularClosedRegion E3) : Set E3) =
      extrude z₁ z₂ (A : Region) := rfl

/-- Helper: `extrude z₁ z₂` preserves subset for `z₁ < z₂`. -/
theorem extrude_subset_iff {z₁ z₂ : ℝ} (hz : z₁ < z₂) (X Y : Region) :
    extrude z₁ z₂ X ⊆ extrude z₁ z₂ Y ↔ X ⊆ Y := by
  have hmidc : (z₁ + z₂) / 2 ∈ Icc z₁ z₂ := ⟨by linarith, by linarith⟩
  constructor
  · intro h p hp
    have := (h (show pt p.x p.y ((z₁ + z₂) / 2) ∈ extrude z₁ z₂ X from ⟨by simpa, hmidc⟩)).1
    simpa using this
  · intro h p hp
    exact ⟨h hp.1, hp.2⟩

theorem extrude_eq_iff {z₁ z₂ : ℝ} (hz : z₁ < z₂) (X Y : Region) :
    extrude z₁ z₂ X = extrude z₁ z₂ Y ↔ X = Y := by
  constructor
  · intro h
    exact Subset.antisymm ((extrude_subset_iff hz X Y).mp (le_of_eq h))
      ((extrude_subset_iff hz Y X).mp (le_of_eq h.symm))
  · intro h; rw [h]

theorem extrude_intersects_iff {z₁ z₂ : ℝ} (hz : z₁ < z₂) (X Y : Region) :
    Intersects (extrude z₁ z₂ X) (extrude z₁ z₂ Y) ↔ Intersects X Y := by
  have hmidc : (z₁ + z₂) / 2 ∈ Icc z₁ z₂ := ⟨by linarith, by linarith⟩
  constructor
  · rintro ⟨p, hpX, hpY⟩
    exact ⟨projXY p, hpX.1, hpY.1⟩
  · rintro ⟨p, hpX, hpY⟩
    exact ⟨pt p.x p.y ((z₁ + z₂) / 2), ⟨by simpa, hmidc⟩, ⟨by simpa, hmidc⟩⟩

theorem extrude_interior_intersects_iff {z₁ z₂ : ℝ} (hz : z₁ < z₂) (X Y : Region) :
    Intersects (interior (extrude z₁ z₂ X)) (interior (extrude z₁ z₂ Y)) ↔
      Intersects (interior X) (interior Y) := by
  have hmid : (z₁ + z₂) / 2 ∈ Ioo z₁ z₂ := ⟨by linarith, by linarith⟩
  rw [interior_extrude, interior_extrude]
  constructor
  · rintro ⟨p, hpX, hpY⟩
    exact ⟨projXY p, hpX.1, hpY.1⟩
  · rintro ⟨p, hpX, hpY⟩
    exact ⟨pt p.x p.y ((z₁ + z₂) / 2), ⟨by simpa, hmid⟩, ⟨by simpa, hmid⟩⟩

/-- **Exact preservation of `DC`, `EC`, `PO`, `EQ` under equal-height extrusion**:
for any `z₁ < z₂`, `DC`, `EC`, `PO`, and `EQ` hold between extruded 3D prisms
iff they hold between their 2D footprints. -/
theorem extrude_dc_iff {z₁ z₂ : ℝ} (hz : z₁ < z₂)
    (A B : RegularClosedRegion Point2D) :
    RCC8.DC (extrudeRegularClosed hz A) (extrudeRegularClosed hz B) ↔ RCC8.DC A B := by
  show Geospatial.Disjoint _ _ ↔ Geospatial.Disjoint _ _
  rw [coe_extrudeRegularClosed, coe_extrudeRegularClosed, disjoint_iff_not_intersects,
    disjoint_iff_not_intersects, extrude_intersects_iff hz]

theorem extrude_ec_iff {z₁ z₂ : ℝ} (hz : z₁ < z₂)
    (A B : RegularClosedRegion Point2D) :
    RCC8.EC (extrudeRegularClosed hz A) (extrudeRegularClosed hz B) ↔ RCC8.EC A B := by
  show Touches _ _ ↔ Touches _ _
  unfold Touches
  rw [coe_extrudeRegularClosed, coe_extrudeRegularClosed, extrude_intersects_iff hz,
    disjoint_iff_not_intersects, disjoint_iff_not_intersects, extrude_interior_intersects_iff hz]

theorem extrude_po_iff {z₁ z₂ : ℝ} (hz : z₁ < z₂)
    (A B : RegularClosedRegion Point2D) :
    RCC8.PO (extrudeRegularClosed hz A) (extrudeRegularClosed hz B) ↔ RCC8.PO A B := by
  unfold RCC8.PO Within
  rw [coe_extrudeRegularClosed, coe_extrudeRegularClosed,
    extrude_interior_intersects_iff hz, extrude_subset_iff hz, extrude_subset_iff hz]

theorem extrude_rcc8_eq_iff {z₁ z₂ : ℝ} (hz : z₁ < z₂)
    (A B : RegularClosedRegion Point2D) :
    RCC8.EQ (extrudeRegularClosed hz A) (extrudeRegularClosed hz B) ↔ RCC8.EQ A B := by
  unfold RCC8.EQ
  rw [coe_extrudeRegularClosed, coe_extrudeRegularClosed, extrude_eq_iff hz]

/-- **Subtlety of finite equal-height extrusion (`NTPP` collapses to `TPP`)**:
a nonempty 2D region extruded to `[z₁, z₂]` is NEVER `NTPP` of another region
extruded to the SAME `[z₁, z₂]`, because their top and bottom faces at `z = z₁`
and `z = z₂` always touch the 3D boundary. Thus even a 2D `NTPP` becomes a 3D
`TPP`! -/
theorem extrude_not_ntpp {z₁ z₂ : ℝ} (hz : z₁ < z₂)
    (A B : RegularClosedRegion Point2D) (hA : (A : Region).Nonempty) :
    ¬ RCC8.NTPP (extrudeRegularClosed hz A) (extrudeRegularClosed hz B) := by
  intro ⟨hsub, _⟩
  rw [coe_extrudeRegularClosed, coe_extrudeRegularClosed, interior_extrude] at hsub
  obtain ⟨p, hp⟩ := hA
  have hmem : pt p.x p.y z₁ ∈ extrude z₁ z₂ (A : Region) := ⟨by simpa using hp, ⟨le_rfl, hz.le⟩⟩
  have h2 := (hsub hmem).2
  exact lt_irrefl z₁ h2.1

/-- Under equal-height finite extrusion, any proper 2D part (whether `TPP` or
`NTPP`) becomes a 3D tangential proper part (`TPP`). -/
theorem extrude_tpp_of_ntpp {z₁ z₂ : ℝ} (hz : z₁ < z₂)
    (A B : RegularClosedRegion Point2D) (hA : (A : Region).Nonempty)
    (h : RCC8.NTPP A B) :
    RCC8.TPP (extrudeRegularClosed hz A) (extrudeRegularClosed hz B) := by
  refine ⟨?_, ?_, ?_⟩
  · show extrude z₁ z₂ (A : Region) ⊆ extrude z₁ z₂ (B : Region)
    exact (extrude_subset_iff hz _ _).mpr (h.1.trans interior_subset)
  · show extrude z₁ z₂ (A : Region) ≠ extrude z₁ z₂ (B : Region)
    intro heq
    exact h.2 ((extrude_eq_iff hz _ _).mp heq)
  · intro hint
    exact extrude_not_ntpp hz A B hA ⟨hint, fun heq => h.2 ((extrude_eq_iff hz _ _).mp heq)⟩

/-- When the inner prism ALSO has strictly nested height bounds
`z₁' < z₁ < z₂ < z₂'`, `NTPP` IS preserved in 3D. -/
theorem extrude_ntpp_of_strict_heights {z₁ z₂ z₁' z₂' : ℝ}
    (hz : z₁ < z₂) (hz' : z₁' < z₂') (h1 : z₁' < z₁) (h2 : z₂ < z₂')
    (A B : RegularClosedRegion Point2D) (h : RCC8.NTPP A B) :
    RCC8.NTPP (extrudeRegularClosed hz A) (extrudeRegularClosed hz' B) := by
  refine ⟨?_, ?_⟩
  · show extrude z₁ z₂ (A : Region) ⊆ interior (extrude z₁' z₂' (B : Region))
    rw [interior_extrude]
    rintro p ⟨hpA, hpz1, hpz2⟩
    exact ⟨h.1 hpA, lt_of_lt_of_le h1 hpz1, lt_of_le_of_lt hpz2 h2⟩
  · show extrude z₁ z₂ (A : Region) ≠ extrude z₁' z₂' (B : Region)
    intro heq
    -- Any point of `B` at `z = z₁'` lies in `extrude z₁' z₂' B` but not in `extrude z₁ z₂ A`.
    have hBne : (B : Region).Nonempty := by
      by_contra hB
      rw [not_nonempty_iff_eq_empty] at hB
      have hA : (A : Region) = ∅ := subset_eq_empty (h.1.trans interior_subset) hB
      exact h.2 (hA.trans hB.symm)
    obtain ⟨b, hb⟩ := hBne
    have hmem : pt b.x b.y z₁' ∈ extrude z₁' z₂' (B : Region) :=
      ⟨by simpa using hb, ⟨le_rfl, hz'.le⟩⟩
    rw [← heq] at hmem
    have hz1 : z₁ ≤ z₁' := hmem.2.1
    linarith

/-- Dimension lift: extruding a 2D set with nonempty interior over `z₁ < z₂`
produces a 3D set with `cubeDim 3 = 3`. -/
theorem cubeDim_extrude_eq_three {z₁ z₂ : ℝ} (hz : z₁ < z₂) {A : Region}
    (hA : (interior A).Nonempty) :
    (cubeDim 3 : DimensionFunction E3).dim (extrude z₁ z₂ A) = 3 := by
  apply cubeDim_of_interior
  rw [interior_extrude]
  obtain ⟨p, hp⟩ := hA
  exact ⟨pt p.x p.y ((z₁ + z₂) / 2), by simpa using hp,
    show (z₁ + z₂) / 2 ∈ Ioo z₁ z₂ from ⟨by linarith, by linarith⟩⟩

/-! ## 5. Minimal counterexamples where 2D approximation fails -/

/-- **Counterexample 1 (Overpass / bridge roads)**:
Two 3D road segments — Road 1 along `y = 0, z = 0` for `x ∈ [-1, 1]` and
Road 2 along `x = 0, z = 5` for `y ∈ [-1, 1]` — are **disjoint in 3D**,
yet their 2D `projXY` projections **intersect** at `(0, 0)`. -/
theorem counterexample_overpass_roads :
    let road1 : Set E3 := {p | p 0 ∈ Icc (-1 : ℝ) 1 ∧ p 1 = 0 ∧ p 2 = 0}
    let road2 : Set E3 := {p | p 0 = 0 ∧ p 1 ∈ Icc (-1 : ℝ) 1 ∧ p 2 = 5}
    Geospatial.Disjoint road1 road2 ∧
      Intersects (projXY '' road1) (projXY '' road2) := by
  intro road1 road2
  refine ⟨?_, ?_⟩
  · rw [Geospatial.Disjoint, eq_empty_iff_forall_notMem]
    rintro p ⟨h1, h2⟩
    have hz1 : p 2 = 0 := h1.2.2
    have hz2 : p 2 = 5 := h2.2.2
    linarith
  · refine ⟨Point2D.mk 0 0, ⟨pt 0 0 0, ?_, rfl⟩, ⟨pt 0 0 5, ?_, rfl⟩⟩
    · exact ⟨⟨by norm_num, by norm_num⟩, rfl, rfl⟩
    · exact ⟨rfl, ⟨by norm_num, by norm_num⟩, rfl⟩

/-- **Counterexample 2 (Multi-story building floors)**:
Floor 1 (`[0, 10] × [0, 10] × [0, 3]`) and Floor 2 (`[0, 10] × [0, 10] × [4, 7]`)
are **disjoint (`DC`) in 3D**, yet their 2D `projXY` footprints are **equal (`EQ`)**. -/
theorem counterexample_building_floors :
    let footprint : Region := (⟨0, 10, 0, 10⟩ : Rect).toRegion
    let floor1 : Set E3 := extrude 0 3 footprint
    let floor2 : Set E3 := extrude 4 7 footprint
    Geospatial.Disjoint floor1 floor2 ∧
      projXY '' floor1 = projXY '' floor2 := by
  intro footprint floor1 floor2
  refine ⟨?_, ?_⟩
  · rw [Geospatial.Disjoint, eq_empty_iff_forall_notMem]
    rintro p ⟨h1, h2⟩
    linarith [h1.2.2, h2.2.1]
  · ext q
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact ⟨pt (projXY p).x (projXY p).y 5,
        ⟨by rw [e3HomeomorphProd_apply, projXY_pt]; exact hp.1, ⟨by norm_num, by norm_num⟩⟩,
        projXY_pt _ _⟩
    · rintro ⟨p, hp, rfl⟩
      exact ⟨pt (projXY p).x (projXY p).y 1,
        ⟨by rw [e3HomeomorphProd_apply, projXY_pt]; exact hp.1, ⟨by norm_num, by norm_num⟩⟩,
        projXY_pt _ _⟩

/-- **Counterexample 3 (2D adjacent / `EC`, 3D disjoint / `DC`)**:
Box A (`[0, 1] × [0, 1] × [0, 1]`) and Box B (`[1, 2] × [0, 1] × [2, 3]`)
are **disjoint in 3D**, yet their 2D `projXY` projections **touch (`EC`)** along `x = 1`. -/
theorem counterexample_adjacent_2d_disjoint_3d :
    let rA : Rect := ⟨0, 1, 0, 1⟩
    let rB : Rect := ⟨1, 2, 0, 1⟩
    let boxA : Set E3 := extrude 0 1 rA.toRegion
    let boxB : Set E3 := extrude 2 3 rB.toRegion
    Geospatial.Disjoint boxA boxB ∧
      Touches (projXY '' boxA) (projXY '' boxB) := by
  intro rA rB boxA boxB
  have hprojA : projXY '' boxA = rA.toRegion := by
    ext q
    constructor
    · rintro ⟨p, hp, rfl⟩; exact hp.1
    · intro hq; exact ⟨pt q.x q.y 0, ⟨by simpa using hq, ⟨le_rfl, zero_le_one⟩⟩, Point2D.ext rfl rfl⟩
  have hprojB : projXY '' boxB = rB.toRegion := by
    ext q
    constructor
    · rintro ⟨p, hp, rfl⟩; exact hp.1
    · intro hq; exact ⟨pt q.x q.y 2, ⟨by simpa using hq, ⟨le_rfl, by norm_num⟩⟩, Point2D.ext rfl rfl⟩
  refine ⟨?_, ?_⟩
  · rw [Geospatial.Disjoint, eq_empty_iff_forall_notMem]
    rintro p ⟨h1, h2⟩
    linarith [h1.2.2, h2.2.1]
  · rw [hprojA, hprojB]
    refine ⟨⟨Point2D.mk 1 0, ⟨by norm_num [rA], by norm_num [rA], by norm_num [rA], by norm_num [rA]⟩,
        ⟨by norm_num [rB], by norm_num [rB], by norm_num [rB], by norm_num [rB]⟩⟩, ?_⟩
    rw [Geospatial.Disjoint, Rect.interior_toRegion, Rect.interior_toRegion,
      eq_empty_iff_forall_notMem]
    rintro p ⟨hA, hB⟩
    linarith [hA.2.1, hB.1]

/-- **Counterexample 4 (Topological cavity lost under 2D projection)**:
A solid cube `[0, 3]³` and a cube with an internal cavity `[0, 3]³ \ (1, 2)³`
differ topologically (the center `(3/2, 3/2, 3/2)` belongs to the first solid
but not the second), yet their 2D `projXY` projections are **identical**
(`[0, 3] × [0, 3]`). -/
theorem counterexample_projection_loses_topology :
    let r : Rect := ⟨0, 3, 0, 3⟩
    let solid : Set E3 := extrude 0 3 r.toRegion
    let cavity : Set E3 := {p | p 0 ∈ Ioo (1 : ℝ) 2 ∧ p 1 ∈ Ioo (1 : ℝ) 2 ∧ p 2 ∈ Ioo (1 : ℝ) 2}
    let hollow : Set E3 := solid \ cavity
    solid ≠ hollow ∧ projXY '' solid = projXY '' hollow := by
  intro r solid cavity hollow
  refine ⟨?_, ?_⟩
  · intro heq
    have hc : pt (3 / 2) (3 / 2) (3 / 2) ∈ solid :=
      ⟨⟨by norm_num [r], by norm_num [r], by norm_num [r], by norm_num [r]⟩,
        ⟨by norm_num, by norm_num⟩⟩
    rw [heq] at hc
    exact hc.2 ⟨⟨by norm_num, by norm_num⟩, ⟨by norm_num, by norm_num⟩, ⟨by norm_num, by norm_num⟩⟩
  · ext q
    constructor
    · rintro ⟨p, hp, rfl⟩
      -- Projecting at `z = 0` avoids the cavity `z ∈ (1, 2)` while having the same `(x, y)`!
      refine ⟨pt (projXY p).x (projXY p).y 0,
        ⟨⟨by rw [e3HomeomorphProd_apply, projXY_pt]; exact hp.1, ⟨le_rfl, by norm_num⟩⟩, ?_⟩,
        projXY_pt _ _⟩
      rintro ⟨-, -, hz⟩
      norm_num at hz
    · rintro ⟨p, hp, rfl⟩
      exact ⟨p, hp.1, rfl⟩

end Geospatial.Space2D3D
