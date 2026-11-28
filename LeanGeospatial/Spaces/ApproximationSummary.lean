import LeanGeospatial.Spaces.IntrinsicVsAmbient

/-!
# Mathematical Justification of 2D Approximation (`ℝ²`, `S²`, `ℝ³`)

Synthesizes the exact conditions under which 2D planar approximation is
mathematically justified, versus where 3D or spherical modeling is essential,
explicitly separating **topological correctness** from **metric accuracy**
(the latter belonging to geodesy, e.g. spherical/ellipsoidal distance and area
theorems in `LeanGeodesy`).

## Summary of Justified Cases vs Failure Modes

1. **Local map projection (`S² \ {N} ≃ₜ ℝ²`)**:
   - *Topology*: exact — all RCC8 and DE-9IM relations are preserved
     (`stereoHomeomorph_rcc8_iff`, `stereoHomeomorph_de9im_eq`, `liftToS2_rcc8_iff`).
   - *Metric*: NOT preserved (`counterexample_stereo_not_isometry`); metric
     bounds require geodesic/ellipsoidal error analysis rather than topology.
2. **2.5D single-valued terrain (`embedGraph h : ℝ² → ℝ³`)**:
   - *Topology*: exact on the graph subspace (`embedGraphHomeomorph_rcc8_iff`),
     provided elevation `h : ℝ² → ℝ` is single-valued and continuous.
   - *Metric*: Euclidean distance is distorted by at most `√(1 + K²)` when `h`
     is `K`-Lipschitz (`dist_embedGraph_le_of_lipschitz`).
3. **Footprint extrusion (`extrudeRegularClosed`)**:
   - Equal-height extrusion preserves `DC`, `EC`, `PO`, `EQ`, but collapses
     2D `NTPP` to 3D `TPP` (`extrude_tpp_of_ntpp`) because top and bottom faces
     coincide; strict nested height intervals restore `NTPP`
     (`extrude_ntpp_of_strict_heights`).
4. **Essential 3D phenomena where 2D projection fails**:
   - Overpass / grade-separated roads (`counterexample_overpass_roads`).
   - Multi-story buildings (`counterexample_building_floors`).
   - Underground structures (`counterexample_underground_structure`).
   - 2D-adjacent, 3D-disjoint regions (`counterexample_adjacent_2d_disjoint_3d`).
   - 3D cavities / nested shells lost under `projXY`
     (`counterexample_projection_loses_topology`).
-/

namespace Geospatial.Spaces

open Set Topology Geospatial Geospatial.DE9IM Geospatial.DE9IM.Space3 Geospatial.Space2D3D

/-! ## Underground structure counterexample -/

/-- **Underground structure counterexample**:
a surface parcel/road at elevation `[0, 1]` and an underground tunnel directly
beneath it at elevation `[-12, -8]` are **disjoint (`RCC8.DC`)** in `ℝ³`, yet
their 2D planar projections under `projXY` are **identical** (`r.toRegion`). -/
theorem counterexample_underground_structure :
    ∃ (surface tunnel : RegularClosedRegion E3),
      RCC8.DC surface tunnel ∧
      projXY '' (surface : Set E3) = projXY '' (tunnel : Set E3) ∧
      (projXY '' (surface : Set E3)).Nonempty := by
  let r : Rect := ⟨0, 10, 0, 10⟩
  let A : RegularClosedRegion E2 := r.toRegularClosed (by norm_num) (by norm_num)
  let surface : RegularClosedRegion E3 := extrudeRegularClosed (z₁ := 0) (z₂ := 1) (by norm_num) A
  let tunnel : RegularClosedRegion E3 := extrudeRegularClosed (z₁ := -12) (z₂ := -8) (by norm_num) A
  refine ⟨surface, tunnel, ?_, ?_, ?_⟩
  · -- Disjoint in ℝ³ because z ∈ [0, 1] and z ∈ [-12, -8] cannot both hold
    rw [RCC8.dc_iff_disjoint, Geospatial.Disjoint, eq_empty_iff_forall_notMem]
    rintro p ⟨hs, ht⟩
    have hz1 : (0 : ℝ) ≤ p 2 := hs.2.1
    have hz2 : p 2 ≤ -8 := ht.2.2
    linarith
  · -- Identical 2D projection under projXY
    have hsurf : projXY '' (surface : Set E3) = (A : Set E2) := by
      ext q
      constructor
      · rintro ⟨p, hp, rfl⟩; exact hp.1
      · intro hq
        refine ⟨pt q.x q.y 0, ⟨?_, by simp [pt]⟩, ?_⟩
        · simpa [projXY_pt] using hq
        · exact projXY_pt q 0
    have htun : projXY '' (tunnel : Set E3) = (A : Set E2) := by
      ext q
      constructor
      · rintro ⟨p, hp, rfl⟩; exact hp.1
      · intro hq
        refine ⟨pt q.x q.y (-10), ⟨?_, by norm_num [pt]⟩, ?_⟩
        · simpa [projXY_pt] using hq
        · exact projXY_pt q (-10)
    rw [hsurf, htun]
  · refine ⟨Point2D.mk 5 5, pt 5 5 0, ⟨?_, by simp [pt]⟩, ?_⟩
    · show projXY (pt 5 5 0) ∈ r.toRegion
      rw [show pt 5 5 0 = pt (Point2D.mk 5 5).x (Point2D.mk 5 5).y 0 from rfl, projXY_pt]
      norm_num [Rect.toRegion, r]
    · exact projXY_pt (Point2D.mk 5 5) 0

/-! ## Consolidated justification theorems -/

/-- **Topology vs metric separation for local map projections**:
stereographic projection `stereoHomeomorph : PuncturedS2 ≃ₜ ℝ²` preserves every
RCC8 relation, yet fails to preserve distances (distorting `(0,0)`–`(1,0)` from
`1` to `√2` in `ℝ³`). -/
theorem local_projection_topology_vs_metric :
    (∀ (A B : RegularClosedRegion PuncturedS2) (r : RCC8.Relation),
      r.holds (A.map stereoHomeomorph) (B.map stereoHomeomorph) ↔ r.holds A B) ∧
    (∃ p q : PuncturedS2, dist (stereoHomeomorph p) (stereoHomeomorph q) ≠ dist p q) := by
  refine ⟨stereoHomeomorph_rcc8_iff, ?_⟩
  have ⟨_, _, hne⟩ := counterexample_stereo_not_isometry
  refine ⟨stereoInv (Point2D.mk 0 0), stereoInv (Point2D.mk 1 0), ?_⟩
  change dist (stereoHomeomorph (stereoHomeomorph.symm (Point2D.mk 0 0)))
      (stereoHomeomorph (stereoHomeomorph.symm (Point2D.mk 1 0))) ≠ _
  rw [Homeomorph.apply_symm_apply, Homeomorph.apply_symm_apply]
  exact hne

/-- **2.5D terrain justification**:
a continuous single-valued height function `h : ℝ² → ℝ` preserves all RCC8
relations on the embedded terrain surface, and when `K`-Lipschitz (`K ≥ 0`)
bounds 3D distance by `√(1 + K²)` times the 2D planar distance. -/
theorem terrain25D_justification {h : E2 → ℝ} (hc : Continuous h) {K : ℝ} (hK : 0 ≤ K)
    (hlip : ∀ p q, |h p - h q| ≤ K * dist p q) :
    (∀ (A B : RegularClosedRegion E2) (r : RCC8.Relation),
      r.holds (A.map (embedGraphHomeomorph h hc))
              (B.map (embedGraphHomeomorph h hc)) ↔ r.holds A B) ∧
    (∀ p q : E2,
      dist p q ≤ dist (embedGraph h p) (embedGraph h q) ∧
      dist (embedGraph h p) (embedGraph h q) ≤ Real.sqrt (1 + K ^ 2) * dist p q) :=
  ⟨fun A B r => embedGraphHomeomorph_rcc8_iff h hc A B r,
   fun p q => ⟨dist_le_dist_embedGraph h p q, dist_embedGraph_le_of_lipschitz hK hlip p q⟩⟩

end Geospatial.Spaces
