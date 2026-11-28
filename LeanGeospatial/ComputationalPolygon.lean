import LeanComputationalGeometry.Polygon.Jordan
import LeanComputationalGeometry.Polygon.EarClip
import LeanComputationalGeometry.ExactPolygon
import LeanGeospatial.Prover.DE9IMClaim
import LeanGeospatial.RCC8

/-!
# Connecting LeanComputationalGeometry to LeanGeospatial

`LeanComputationalGeometry` and `LeanGeospatial` share the same plane
(`Geospatial.Point2D = ComputationalGeometry.Point2D` by `rfl`). This module
bridges computational geometry objects and exact integer predicates directly to
LeanGeospatial's topological regions, `RegularClosedRegion`, RCC8, Simple
Features, and DE-9IM semantics — shrinking the trust boundary so that spatial
relations for simple polygons, segments, and integer rectangles are computed
and verified inside Lean without relying on an external GIS engine.

## Main results

1. **Simple polygon topology (both CCW and CW)**:
   For every `P : ComputationalGeometry.SimplePolygon`:
   - `SimplePolygon.interior_toRegion`: `interior P.toRegion = P.toOpenRegion`
   - `SimplePolygon.closure_toOpenRegion`: `closure P.toOpenRegion = P.toRegion`
   - `SimplePolygon.closure_interior_toRegion`: `closure (interior P.toRegion) = P.toRegion`
   - `SimplePolygon.toRegularClosedRegion`: `RegularClosedRegion Point2D`
   - `SimplePolygon.boundary_toRegion`: `boundary P.toRegion = P.boundary`
   - `SimplePolygon.exterior_toRegion`: `exterior P.toRegion = P.toRegionᶜ`

2. **`Geospatial.Polygon` point-set semantics**:
   - `Polygon.toRawPolygon`, `Polygon.IsSimple`, `Polygon.toRegion`,
     `Polygon.toOpenRegion`, `Polygon.toBoundary`, `Polygon.toExterior`, and
     `Polygon.toRegularClosedRegion` for simple polygons.

3. **Exact computable algorithms ↔ spatial relation semantics**:
   - Point-in-simple-polygon (`IPoint` vs `List IPoint` with `IsSimple`):
     `pointPolygonMatrixI` computes the full 9-cell DE-9IM matrix (`0FFFFF212`,
     `F0FFFF212`, or `FF0FFF212`), proved exact by `pointPolygonMatrixI_eq`,
     and `pointPolygonClaimI_iff` decides all eight Simple Features relations.
   - Segment-segment intersection (`ISegment` vs `ISegment`):
     `intersectTestI_iff_intersects` connects `intersectTestI` to
     `Geospatial.Intersects`.
   - Integer rectangle-rectangle (`IRect` vs `IRect`):
     `rectRectRCC8` decides the exact RCC8 relation (`rectRectRCC8_holds`), and
     `rectRectMatrixI` computes the full 9-cell DE-9IM matrix
     (`rectRectMatrixI_eq`), distinguishing corner contact (`FF2F01212`) from
     edge contact (`FF2F11212`).

## Trust boundary

No unproven lemmas from `LeanComputationalGeometry` are assumed: all topology
and regular-closed theorems follow unconditionally from `RawPolygon.IsSimple`
using the winding-number Jordan theorems already proved in
`LeanComputationalGeometry`. For integer polygons `ps : List IPoint`, the sole
remaining hypothesis when invoking `pointPolygonMatrixI_eq` is
`(ComputationalGeometry.toRawPolygon ps).IsSimple`.
-/

namespace Geospatial

open Set Filter Topology ComputationalGeometry

/-- The two libraries share the exact same plane type by definitional equality. -/
theorem point2D_eq_compGeom : Geospatial.Point2D = ComputationalGeometry.Point2D := rfl

/-! ## Topology of every simple polygon (CCW and CW) -/

namespace ComputationalPolygon

open RawPolygon

/-- Every simple polygon winds `0` or `1` times around off-boundary points,
either in its given orientation or when reversed. -/
theorem isSimple_windsZeroOrOne_or_reverse {P : RawPolygon} (hP : P.IsSimple) :
    P.WindsZeroOrOne ∨ P.reverse.WindsZeroOrOne := by
  rcases hP.windingNumber_cases with h | h
  · exact Or.inl h
  · right
    intro p hp
    have hp' : ¬ P.OnBoundary p := (onBoundary_reverse P p).not.mp hp
    rw [windingNumber_reverse]
    rcases h p hp' with e | e <;> omega

/-- For a simple polygon with `WindsZeroOrOne`, the reversed ring has left-side
winding value `0`. -/
private theorem reverse_left_value_zero {P : RawPolygon} (hP : P.IsSimple)
    (hJ : P.WindsZeroOrOne) :
    ∀ e : Fin P.reverse.n, ∀ᶠ r in 𝓝[>] (0 : ℝ),
      ∀ q ∈ P.reverse.leftSector e r, P.reverse.windingNumber q = 0 := by
  obtain ⟨L', hL'01, hL'iff, -, hsec', -⟩ := hP.reverse.exists_side_values
  have hL'0 : L' = 0 := by
    rcases hL'01 with rfl | rfl
    · rfl
    · exfalso
      have hrevJ : P.reverse.WindsZeroOrOne := hL'iff.mpr rfl
      -- Both `P` and `P.reverse` winding in `{0, 1}` forces every off-boundary winding number to be `0`,
      -- contradicting `exists_sides₂` across a non-horizontal edge.
      obtain ⟨L, hL01, hLiff, -, -, hedge⟩ := hP.exists_side_values
      have hL1 : L = 1 := hLiff.mp hJ
      have h0 : 0 < P.n := by have := hP.three_le; omega
      set f : Fin P.n := ⟨0, h0⟩
      have hm : (1 / 2 : ℝ) • P.vertex f + (1 / 2 : ℝ) • P.vertex (P.next f) ∈
          openSegment ℝ (P.vertex f) (P.vertex (P.next f)) :=
        ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, rfl⟩
      have hvv : P.vertex f ≠ P.vertex (P.next f) := hP.edge_nondegenerate f
      obtain ⟨h, hh, hpos⟩ := ((hP.eventually_thinLeft_not_onBoundary f).and self_mem_nhdsWithin).exists
      have hF := (hedge f _ hm).and (P.eventually_mem_thinLeft f hpos hvv hm)
      obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hF
      set d := P.vertex (P.next f) - P.vertex f
      set n : Point2D := Point2D.mk (-d.y) d.x
      set δ := ε / (2 * (‖n‖ + 1))
      have hδ : 0 < δ := by positivity
      set q := ((1 / 2 : ℝ) • P.vertex f + (1 / 2 : ℝ) • P.vertex (P.next f)) + δ • n
      have hqd : dist q ((1 / 2 : ℝ) • P.vertex f + (1 / 2 : ℝ) • P.vertex (P.next f)) < ε := by
        rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hδ.le]
        have : δ * ‖n‖ ≤ ε / 2 := by
          simp only [δ]
          rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) two_pos]
          nlinarith [norm_nonneg n]
        linarith
      have hor : 0 < orient (P.vertex f) (P.vertex (P.next f)) q := by
        have hd : d ≠ 0 := sub_ne_zero.mpr hvv.symm
        have hD : 0 < ComputationalGeometry.dot d d := dot_self_pos hd
        have heq : orient (P.vertex f) (P.vertex (P.next f)) q =
            δ * ComputationalGeometry.dot d d := by
          simp only [q, n, d, orient_def, ComputationalGeometry.dot,
            ComputationalGeometry.Point2D.x, ComputationalGeometry.Point2D.y,
            Geospatial.Point2D.mk, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply,
            smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one]
          ring
        rw [heq]
        exact mul_pos hδ hD
      have ⟨hside, hthin⟩ := hball hqd
      have hnb : ¬ P.OnBoundary q := hh q (hthin hor)
      have hw1 : P.windingNumber q = 1 := by rw [hside.1 hor, hL1]
      have hrev := hrevJ q ((onBoundary_reverse P q).not.mpr hnb)
      rw [windingNumber_reverse, hw1] at hrev
      omega
  intro e
  filter_upwards [hsec' e] with r hr q hq
  rw [hr q hq, hL'0]

/-- No boundary point of a simple polygon lies in the topological interior of its region. -/
theorem isSimple_not_mem_interior_of_onBoundary {P : RawPolygon} (hP : P.IsSimple)
    (hJ : P.WindsZeroOrOne) {p : Point2D} (hp : P.OnBoundary p) :
    p ∉ interior P.region := by
  intro hint
  obtain ⟨e, he⟩ := hp
  rw [edge_toSet] at he
  by_cases hv : p = P.vertex e ∨ p = P.vertex (P.next e)
  · -- Vertex case: a small sector on the right (left of `P.reverse`) avoids the boundary
    -- and has winding number `0`, while staying inside any ball around `p`.
    obtain ⟨i, rfl⟩ : ∃ i : Fin P.n, p = P.vertex i := by
      rcases hv with rfl | rfl
      · exact ⟨e, rfl⟩
      · exact ⟨P.next e, rfl⟩
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hint)
    set j : Fin P.reverse.n := Fin.rev i
    have hvj : P.reverse.vertex j = P.vertex i :=
      congrArg P.vertex (Fin.rev_rev i)
    have hne : ∀ r, 0 < r → (P.reverse.leftSector j r).Nonempty := by
      obtain ⟨-, -, -, -, hne'⟩ := hP.reverse.exists_edge_value (P.reverse.prev j)
      simpa [RawPolygon.next_prev] using hne'
    have hF := ((hP.reverse.eventually_leftSector_not_onBoundary j).and
      (reverse_left_value_zero hP hJ j)).and (Ioo_mem_nhdsGT hε)
    obtain ⟨r, ⟨hnb, hw0⟩, hr0, hrε⟩ := hF.exists
    obtain ⟨q, hq⟩ := hne r hr0
    have hqd : dist q (P.vertex i) < ε := by
      rw [← hvj]
      exact hq.1.trans hrε
    have hqR : q ∈ P.region := hball (Metric.mem_ball.mpr hqd)
    have hqnb : ¬ P.OnBoundary q := (onBoundary_reverse P q).not.mp (hnb q hq)
    have hqw : P.windingNumber q = 0 := by
      have := hw0 q hq
      rw [windingNumber_reverse] at this
      omega
    rcases hqR with h | h
    · exact hqnb h
    · exact h hqw
  · -- Edge interior case: points just on the right of edge `e` avoid the boundary
    -- and have winding number `0`.
    push Not at hv
    have hpopen : p ∈ openSegment ℝ (P.vertex e) (P.vertex (P.next e)) :=
      mem_openSegment_of_ne_left_right hv.1.symm hv.2.symm he
    have hvv : P.vertex e ≠ P.vertex (P.next e) := hP.edge_nondegenerate e
    obtain ⟨L, -, hLiff, -, -, hedge⟩ := hP.exists_side_values
    have hL1 : L = 1 := hLiff.mp hJ
    set e' : Fin P.reverse.n := Fin.rev (P.next e)
    obtain ⟨h, hh, hpos⟩ :=
      ((hP.reverse.eventually_thinLeft_not_onBoundary e').and self_mem_nhdsWithin).exists
    have hF := ((hedge e p hpopen).and
      (eventually_mem_thinLeft_reverse e hpos hvv hpopen)).and
      (mem_interior_iff_mem_nhds.mp hint)
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hF
    set d := P.vertex (P.next e) - P.vertex e
    set n : Point2D := Point2D.mk d.y (-d.x)
    set δ := ε / (2 * (‖n‖ + 1))
    have hδ : 0 < δ := by positivity
    set q := p + δ • n
    have hqd : dist q p < ε := by
      rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hδ.le]
      have : δ * ‖n‖ ≤ ε / 2 := by
        simp only [δ]
        rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) two_pos]
        nlinarith [norm_nonneg n]
      linarith
    have hor0 : orient (P.vertex e) (P.vertex (P.next e)) p = 0 :=
      Segment.orient_eq_zero_of_mem ⟨_, _⟩ he
    have hor : orient (P.vertex e) (P.vertex (P.next e)) q < 0 := by
      have hd : d ≠ 0 := sub_ne_zero.mpr hvv.symm
      have hD : 0 < ComputationalGeometry.dot d d := dot_self_pos hd
      have heq : orient (P.vertex e) (P.vertex (P.next e)) q =
          orient (P.vertex e) (P.vertex (P.next e)) p - δ * ComputationalGeometry.dot d d := by
        simp only [q, n, d, orient_def, ComputationalGeometry.dot,
          ComputationalGeometry.Point2D.x, ComputationalGeometry.Point2D.y,
          Geospatial.Point2D.mk, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply,
          smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one]
        ring
      rw [heq, hor0, zero_sub]
      linarith [mul_pos hδ hD]
    obtain ⟨⟨hside, hthin⟩, hqR⟩ := hball hqd
    have hqnb : ¬ P.OnBoundary q := (onBoundary_reverse P q).not.mp (hh q (hthin hor))
    have hqw : P.windingNumber q = 0 := by rw [hside.2 hor, hL1]; norm_num
    rcases hqR with h | h
    · exact hqnb h
    · exact h hqw

/-- The topological interior of a simple polygon's closed region is its open
region (points off the boundary with nonzero winding number). -/
theorem interior_region_of_isSimple {P : RawPolygon} (hP : P.IsSimple) :
    interior P.region = P.openRegion := by
  apply Subset.antisymm
  · intro p hp
    have hreg : p ∈ P.region := interior_subset hp
    have hnb : ¬ P.OnBoundary p := by
      rcases isSimple_windsZeroOrOne_or_reverse hP with hJ | hJ
      · exact fun hb => isSimple_not_mem_interior_of_onBoundary hP hJ hb hp
      · intro hb
        have hp' : p ∈ interior P.reverse.region := by rwa [region_reverse]
        exact isSimple_not_mem_interior_of_onBoundary hP.reverse hJ
          ((onBoundary_reverse P p).mpr hb) hp'
    rcases hreg with hb | hw
    · exact absurd hb hnb
    · exact ⟨hnb, hw⟩
  · exact interior_maximal P.openRegion_subset_region P.isOpen_openRegion

/-- The closed region of any simple polygon (CCW or CW) is the closure of its
open region. -/
theorem closure_openRegion_of_isSimple {P : RawPolygon} (hP : P.IsSimple) :
    closure P.openRegion = P.region := by
  rcases isSimple_windsZeroOrOne_or_reverse hP with hJ | hJ
  · exact hP.closure_openRegion hJ
  · rw [← openRegion_reverse, ← region_reverse]
    exact hP.reverse.closure_openRegion hJ

/-- Every simple polygon's closed region is regular closed: the closure of its
topological interior. -/
theorem closure_interior_region_of_isSimple {P : RawPolygon} (hP : P.IsSimple) :
    closure (interior P.region) = P.region := by
  rw [interior_region_of_isSimple hP, closure_openRegion_of_isSimple hP]

/-- The topological boundary (`frontier`) of a simple polygon's closed region
is the union of its edges (`OnBoundary`). -/
theorem boundary_region_of_isSimple {P : RawPolygon} (hP : P.IsSimple) :
    Geospatial.boundary P.region = {p | P.OnBoundary p} := by
  rw [Geospatial.boundary_eq, P.isClosed_region.closure_eq, interior_region_of_isSimple hP]
  ext p
  simp only [Set.mem_sdiff, RawPolygon.region, RawPolygon.openRegion, mem_ofPred_eq]
  tauto

/-- The topological exterior of a simple polygon's closed region is its
complement. -/
theorem exterior_region_of_isSimple {P : RawPolygon} (_hP : P.IsSimple) :
    Geospatial.exterior P.region = P.regionᶜ :=
  exterior_eq_of_isClosed P.isClosed_region

/-- Every simple polygon has a nonempty open region. -/
theorem openRegion_nonempty_of_isSimple {P : RawPolygon} (hP : P.IsSimple) :
    P.openRegion.Nonempty := by
  have h0 : 0 < P.n := by have := hP.three_le; omega
  have hne : P.region.Nonempty := ⟨P.vertex ⟨0, h0⟩, Or.inl (P.onBoundary_vertex ⟨0, h0⟩)⟩
  rw [← closure_openRegion_of_isSimple hP] at hne
  exact closure_nonempty_iff.mp hne

end ComputationalPolygon

/-! ## Connecting `SimplePolygon` to `RegularClosedRegion` and `Geometry` -/

namespace SimplePolygonBridge

/-- View a `ComputationalGeometry.SimplePolygon` as a `Geospatial.Region`. -/
def toGeospatialRegion (P : SimplePolygon) : Region := P.toRegion

theorem interior_toRegion (P : SimplePolygon) :
    interior P.toRegion = P.toOpenRegion :=
  ComputationalPolygon.interior_region_of_isSimple P.2

theorem closure_toOpenRegion (P : SimplePolygon) :
    closure P.toOpenRegion = P.toRegion :=
  ComputationalPolygon.closure_openRegion_of_isSimple P.2

theorem closure_interior_toRegion (P : SimplePolygon) :
    closure (interior P.toRegion) = P.toRegion :=
  ComputationalPolygon.closure_interior_region_of_isSimple P.2

theorem boundary_toRegion (P : SimplePolygon) :
    Geospatial.boundary P.toRegion = P.boundary :=
  ComputationalPolygon.boundary_region_of_isSimple P.2

theorem exterior_toRegion (P : SimplePolygon) :
    Geospatial.exterior P.toRegion = P.toRegionᶜ :=
  ComputationalPolygon.exterior_region_of_isSimple P.2

/-- Every simple polygon is a `RegularClosedRegion Point2D`. -/
def toRegularClosedRegion (P : SimplePolygon) : RegularClosedRegion Point2D :=
  ⟨P.toRegion, closure_interior_toRegion P⟩

@[simp] theorem coe_toRegularClosedRegion (P : SimplePolygon) :
    ((toRegularClosedRegion P : RegularClosedRegion Point2D) : Region) = P.toRegion := rfl

/-- Every simple polygon as an OGC Simple Features area geometry. -/
def toGeometry (P : SimplePolygon) : Geometry :=
  .area (toRegularClosedRegion P)

theorem toGeometry_stratum_I (P : SimplePolygon) :
    (toGeometry P).stratum .I = P.toOpenRegion :=
  interior_toRegion P

theorem toGeometry_stratum_B (P : SimplePolygon) :
    (toGeometry P).stratum .B = P.boundary :=
  boundary_toRegion P

theorem toGeometry_stratum_E (P : SimplePolygon) :
    (toGeometry P).stratum .E = P.toRegionᶜ :=
  exterior_toRegion P

end SimplePolygonBridge

/-! ## Point-set semantics for `Geospatial.Polygon` -/

namespace Polygon

/-- Interpret a `Geospatial.Polygon` (vertex list) as a `ComputationalGeometry.RawPolygon`. -/
def toRawPolygon (poly : Polygon) : RawPolygon :=
  RawPolygon.ofList poly.vertices

/-- A `Geospatial.Polygon` is simple when its ring is simple. -/
def IsSimple (poly : Polygon) : Prop :=
  poly.toRawPolygon.IsSimple

/-- The closed point set bounded by a polygon (under the nonzero winding rule). -/
def toRegion (poly : Polygon) : Region :=
  poly.toRawPolygon.region

/-- The open point set bounded by a polygon. -/
def toOpenRegion (poly : Polygon) : Region :=
  poly.toRawPolygon.openRegion

/-- The boundary point set (union of edges) of a polygon. -/
def toBoundary (poly : Polygon) : Region :=
  {p | poly.toRawPolygon.OnBoundary p}

/-- The exterior point set of a polygon. -/
def toExterior (poly : Polygon) : Region :=
  poly.toRegionᶜ

/-- A simple `Geospatial.Polygon` as a `RegularClosedRegion Point2D`. -/
def toRegularClosedRegion (poly : Polygon) (h : poly.IsSimple) :
    RegularClosedRegion Point2D :=
  ⟨poly.toRegion, ComputationalPolygon.closure_interior_region_of_isSimple h⟩

theorem interior_toRegion (poly : Polygon) (h : poly.IsSimple) :
    interior poly.toRegion = poly.toOpenRegion :=
  ComputationalPolygon.interior_region_of_isSimple h

theorem boundary_toRegion (poly : Polygon) (h : poly.IsSimple) :
    Geospatial.boundary poly.toRegion = poly.toBoundary :=
  ComputationalPolygon.boundary_region_of_isSimple h

theorem exterior_toRegion (poly : Polygon) (h : poly.IsSimple) :
    Geospatial.exterior poly.toRegion = poly.toExterior :=
  ComputationalPolygon.exterior_region_of_isSimple h

end Polygon

/-! ## Exact computational predicates ↔ Geospatial spatial relations -/

/-- Exact integer segment intersection decides `Geospatial.Intersects`. -/
theorem intersectTestI_iff_intersects (s t : ISegment) :
    Geospatial.Intersects s.toSegment.toSet t.toSegment.toSet ↔ intersectTestI s t = true := by
  rw [← intersects_iff_intersectTestI]
  rfl

/-- Exact integer point-in-polygon (`inRegionI`) decides membership in a simple
polygon's region. -/
theorem inRegionI_iff_mem_toRegion (ps : List IPoint) (p : IPoint) :
    p.toPoint2D ∈ (ComputationalGeometry.toRawPolygon ps).region ↔ inRegionI ps p = true :=
  region_toRawPolygon ps p

/-- Exact integer boundary test (`onBoundaryI`) decides membership in a simple
polygon's topological boundary. -/
theorem onBoundaryI_iff_mem_boundary (ps : List IPoint)
    (h : (ComputationalGeometry.toRawPolygon ps).IsSimple) (p : IPoint) :
    p.toPoint2D ∈ Geospatial.boundary (ComputationalGeometry.toRawPolygon ps).region ↔
      onBoundaryI ps p = true := by
  rw [ComputationalPolygon.boundary_region_of_isSimple h]
  exact onBoundary_toRawPolygon ps p

/-- Exact integer open-region test (`!onBoundaryI && windingNumberI != 0`)
decides membership in a simple polygon's topological interior. -/
def inOpenRegionI (ps : List IPoint) (p : IPoint) : Bool :=
  !onBoundaryI ps p && (windingNumberI ps p != 0)

theorem inOpenRegionI_iff_mem_interior (ps : List IPoint)
    (h : (ComputationalGeometry.toRawPolygon ps).IsSimple) (p : IPoint) :
    p.toPoint2D ∈ interior (ComputationalGeometry.toRawPolygon ps).region ↔
      inOpenRegionI ps p = true := by
  rw [ComputationalPolygon.interior_region_of_isSimple h]
  simp only [RawPolygon.openRegion, mem_ofPred_eq, inOpenRegionI, Bool.and_eq_true,
    Bool.not_eq_true', bne_iff_ne, ne_eq, onBoundary_toRawPolygon, windingNumber_toRawPolygon]
  rw [Bool.eq_false_iff]

/-! ## Verified, GIS-free DE-9IM computation: integer point vs simple polygon -/

/-- Computable DE-9IM matrix of an integer point `p` against an integer simple
polygon `ps`, without calling an external GIS engine. -/
def pointPolygonMatrixI (p : IPoint) (ps : List IPoint) : Prover.Matrix9 :=
  if onBoundaryI ps p then
    ⟨.F, .d0, .F, .F, .F, .F, .d2, .d1, .d2⟩
  else if windingNumberI ps p != 0 then
    ⟨.d0, .F, .F, .F, .F, .F, .d2, .d1, .d2⟩
  else
    ⟨.F, .F, .d0, .F, .F, .F, .d2, .d1, .d2⟩

private theorem dimValue_open_diff_singleton {U : Region} (hU : IsOpen U) (hne : U.Nonempty)
    (p : Point2D) : DE9IM.DimValue.of ({p}ᶜ ∩ U) = .d2 := by
  have hopen : IsOpen ({p}ᶜ ∩ U) := isClosed_singleton.isOpen_compl.inter hU
  apply DE9IM.DimValue.of_eq
  show (interior ({p}ᶜ ∩ U)).Nonempty
  rw [hopen.interior_eq]
  obtain ⟨q, hq⟩ := hne
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU q hq
  by_cases hqp : q = p
  · subst hqp
    refine ⟨q + Point2D.mk (ε / 2) 0, ?_, hball ?_⟩
    · intro heq
      have := congrArg Geospatial.Point2D.x heq
      simp only [Geospatial.Point2D.x, Geospatial.Point2D.mk, PiLp.add_apply,
        Matrix.cons_val_zero] at this
      linarith
    · rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left]
      have hn : ‖Point2D.mk (ε / 2) 0‖ = ε / 2 := by
        rw [EuclideanSpace.norm_eq, Fin.sum_univ_two]
        change √(‖ε / 2‖ ^ 2 + ‖(0 : ℝ)‖ ^ 2) = ε / 2
        rw [Real.norm_of_nonneg (by positivity), norm_zero, zero_pow two_ne_zero, add_zero,
          Real.sqrt_sq (by positivity)]
      rw [hn]
      linarith
  · exact ⟨q, hqp, hq⟩

private theorem dimValue_compl_inter_boundary {P : SimplePolygon} (p : Point2D) :
    DE9IM.DimValue.of ({p}ᶜ ∩ P.boundary) = .d1 := by
  apply DE9IM.DimValue.of_eq
  refine ⟨?_, ?_⟩
  · -- `interior ({p}ᶜ ∩ P.boundary) = ∅` because `P.boundary = frontier P.toRegion` has empty interior.
    have hfront : interior P.boundary = ∅ := by
      rw [← SimplePolygonBridge.boundary_toRegion P]
      rw [eq_empty_iff_forall_notMem]
      intro q hq
      have hqb : q ∈ Geospatial.boundary P.toRegion := interior_subset hq
      have hsub : Geospatial.boundary P.toRegion ⊆ P.toRegion := by
        rw [Geospatial.boundary_eq, P.isClosed_toRegion.closure_eq]
        exact sdiff_subset
      exact hqb.2 (interior_mono hsub hq)
    exact eq_empty_of_subset_empty ((interior_mono inter_subset_right).trans hfront.subset)
  · -- `P.boundary` contains a nondegenerate edge `[a, b]`; at least one half-segment avoids `p`.
    have h0 : 0 < P.1.n := by have := P.2.three_le; omega
    set e : Fin P.1.n := ⟨0, h0⟩
    set a := P.1.vertex e
    set b := P.1.vertex (P.1.next e)
    have hab : a ≠ b := P.2.edge_nondegenerate e
    have hsub_seg : ∀ t ∈ Icc (0 : ℝ) 1, (1 - t) • a + t • b ∈ P.boundary := fun t ht =>
      ⟨e, ⟨1 - t, t, by linarith [ht.2], ht.1, by ring, rfl⟩⟩
    -- Map `s ∈ [0, 1]` to either `[0, 1/3]` or `[2/3, 1]` on `[a, b]`, whichever avoids `p`.
    have hinj_ab : Function.Injective (fun t : ℝ => (1 - t) • a + t • b) := by
      intro t₁ t₂ heq
      dsimp only at heq
      have hdiff : (t₁ - t₂) • (b - a) = 0 := by
        have : ((1 - t₁) • a + t₁ • b) - ((1 - t₂) • a + t₂ • b) = (t₁ - t₂) • (b - a) := by
          module
        rw [heq, sub_self] at this
        exact this.symm
      rcases smul_eq_zero.mp hdiff with h1 | h2
      · linarith
      · exact absurd (sub_eq_zero.mp h2).symm hab
    by_cases hp1 : ∃ t ∈ Icc (0 : ℝ) (1 / 3), (1 - t) • a + t • b = p
    · -- `p` is in `[0, 1/3]`, so `[2/3, 1]` avoids `p`.
      obtain ⟨t₀, ht₀, hpt₀⟩ := hp1
      refine ⟨fun s => (1 - (2 / 3 + s / 3)) • a + (2 / 3 + s / 3) • b, by fun_prop,
        fun s₁ _ s₂ _ h => by
          have := hinj_ab h
          linarith, ?_⟩
      rintro _ ⟨s, hs, rfl⟩
      refine ⟨?_, hsub_seg (2 / 3 + s / 3) ⟨by linarith [hs.1], by linarith [hs.2]⟩⟩
      intro heq
      have := hinj_ab (heq.trans hpt₀.symm)
      linarith [hs.1, ht₀.2]
    · -- `[0, 1/3]` avoids `p`.
      refine ⟨fun s => (1 - s / 3) • a + (s / 3) • b, by fun_prop,
        fun s₁ _ s₂ _ h => by
          have := hinj_ab h
          linarith, ?_⟩
      rintro _ ⟨s, hs, rfl⟩
      refine ⟨?_, hsub_seg (s / 3) ⟨by linarith [hs.1], by linarith [hs.2]⟩⟩
      intro heq
      exact hp1 ⟨s / 3, ⟨by linarith [hs.1], by linarith [hs.2]⟩, heq⟩

private theorem compl_region_nonempty (P : SimplePolygon) : P.toRegionᶜ.Nonempty := by
  set X := 1 + ∑ i : Fin P.1.n, |(P.1.vertex i).x|
  have hX : ∀ i : Fin P.1.n, (P.1.vertex i).x < X := fun i => by
    have := Finset.single_le_sum (f := fun i => |(P.1.vertex i).x|) (fun _ _ => abs_nonneg _)
      (Finset.mem_univ i)
    linarith [le_abs_self (P.1.vertex i).x]
  exact ⟨Point2D.mk X 0, P.1.not_mem_region_of_right (fun i => by
    change (P.1.vertex i).x < X; exact hX i)⟩

/-- **Verified GIS-free DE-9IM matrix for point vs simple polygon.**
The computable `pointPolygonMatrixI p ps` equals the exact topological DE-9IM
matrix `Prover.Matrix9.of (.point p.toPoint2D) P.toGeometry`. -/
theorem pointPolygonMatrixI_eq (p : IPoint) (ps : List IPoint)
    (hS : (ComputationalGeometry.toRawPolygon ps).IsSimple) :
    Prover.Matrix9.of (.point p.toPoint2D)
      (SimplePolygonBridge.toGeometry ⟨ComputationalGeometry.toRawPolygon ps, hS⟩) =
      pointPolygonMatrixI p ps := by
  set P : SimplePolygon := ⟨ComputationalGeometry.toRawPolygon ps, hS⟩
  have hBI : DE9IM.matrix (.point p.toPoint2D) (SimplePolygonBridge.toGeometry P) .B .I = .F :=
    (DE9IM.DimValue.of_eq_F_iff _).mpr (by simp [Geometry.cell, Geometry.stratum])
  have hBB : DE9IM.matrix (.point p.toPoint2D) (SimplePolygonBridge.toGeometry P) .B .B = .F :=
    (DE9IM.DimValue.of_eq_F_iff _).mpr (by simp [Geometry.cell, Geometry.stratum])
  have hBE : DE9IM.matrix (.point p.toPoint2D) (SimplePolygonBridge.toGeometry P) .B .E = .F :=
    (DE9IM.DimValue.of_eq_F_iff _).mpr (by simp [Geometry.cell, Geometry.stratum])
  have hEI : DE9IM.matrix (.point p.toPoint2D) (SimplePolygonBridge.toGeometry P) .E .I = .d2 := by
    show DE9IM.DimValue.of ({p.toPoint2D}ᶜ ∩ (SimplePolygonBridge.toGeometry P).stratum .I) = .d2
    rw [SimplePolygonBridge.toGeometry_stratum_I]
    exact dimValue_open_diff_singleton P.isOpen_toOpenRegion
      (ComputationalPolygon.openRegion_nonempty_of_isSimple hS) p.toPoint2D
  have hEB : DE9IM.matrix (.point p.toPoint2D) (SimplePolygonBridge.toGeometry P) .E .B = .d1 := by
    show DE9IM.DimValue.of ({p.toPoint2D}ᶜ ∩ (SimplePolygonBridge.toGeometry P).stratum .B) = .d1
    rw [SimplePolygonBridge.toGeometry_stratum_B]
    exact dimValue_compl_inter_boundary p.toPoint2D
  have hEE : DE9IM.matrix (.point p.toPoint2D) (SimplePolygonBridge.toGeometry P) .E .E = .d2 := by
    show DE9IM.DimValue.of ({p.toPoint2D}ᶜ ∩ (SimplePolygonBridge.toGeometry P).stratum .E) = .d2
    rw [SimplePolygonBridge.toGeometry_stratum_E]
    exact dimValue_open_diff_singleton P.isClosed_toRegion.isOpen_compl
      (compl_region_nonempty P) p.toPoint2D
  have hpt : ∀ (t : Stratum),
      (p.toPoint2D ∈ (SimplePolygonBridge.toGeometry P).stratum t →
        DE9IM.matrix (.point p.toPoint2D) (SimplePolygonBridge.toGeometry P) .I t = .d0) ∧
      (p.toPoint2D ∉ (SimplePolygonBridge.toGeometry P).stratum t →
        DE9IM.matrix (.point p.toPoint2D) (SimplePolygonBridge.toGeometry P) .I t = .F) := by
    intro t
    constructor
    · intro ht
      apply DE9IM.DimValue.of_eq
      exact DE9IM.describes_d0_of_subset_singleton ⟨rfl, ht⟩ inter_subset_left
    · intro ht
      exact (DE9IM.DimValue.of_eq_F_iff _).mpr (by
        rw [eq_empty_iff_forall_notMem]
        rintro q ⟨rfl, hq⟩
        exact ht hq)
  unfold pointPolygonMatrixI Prover.Matrix9.of
  by_cases hb : onBoundaryI ps p = true
  · have hpB : p.toPoint2D ∈ (SimplePolygonBridge.toGeometry P).stratum .B := by
      rw [SimplePolygonBridge.toGeometry_stratum_B]
      exact (onBoundary_toRawPolygon ps p).mpr hb
    have hpI : p.toPoint2D ∉ (SimplePolygonBridge.toGeometry P).stratum .I := fun hI => by
      have : p.toPoint2D ∈ (SimplePolygonBridge.toGeometry P).stratum .I ∩
          (SimplePolygonBridge.toGeometry P).stratum .B := ⟨hI, hpB⟩
      rw [Geometry.stratum_I_inter_B] at this
      exact this
    have hpE : p.toPoint2D ∉ (SimplePolygonBridge.toGeometry P).stratum .E := fun hE => by
      rw [Geometry.stratum_E, ← Geometry.stratum_I_union_B] at hE
      exact hE (Or.inr hpB)
    simp only [hb, ↓reduceIte, (hpt .I).2 hpI, (hpt .B).1 hpB, (hpt .E).2 hpE,
      hBI, hBB, hBE, hEI, hEB, hEE]
  · have hnb : ¬ P.1.OnBoundary p.toPoint2D := by
      rw [onBoundary_toRawPolygon]
      exact hb
    have hpB : p.toPoint2D ∉ (SimplePolygonBridge.toGeometry P).stratum .B := by
      rw [SimplePolygonBridge.toGeometry_stratum_B]
      exact hnb
    by_cases hw : (windingNumberI ps p != 0) = true
    · have hpI : p.toPoint2D ∈ (SimplePolygonBridge.toGeometry P).stratum .I := by
        rw [SimplePolygonBridge.toGeometry_stratum_I]
        exact ⟨hnb, by rw [windingNumber_toRawPolygon]; simpa using hw⟩
      have hpE : p.toPoint2D ∉ (SimplePolygonBridge.toGeometry P).stratum .E := fun hE => by
        rw [Geometry.stratum_E, ← Geometry.stratum_I_union_B] at hE
        exact hE (Or.inl hpI)
      simp only [hb, hw, Bool.false_eq_true, ↓reduceIte, (hpt .I).1 hpI, (hpt .B).2 hpB,
        (hpt .E).2 hpE, hBI, hBB, hBE, hEI, hEB, hEE]
    · have hw0 : P.1.windingNumber p.toPoint2D = 0 := by
        rw [windingNumber_toRawPolygon]
        simpa using hw
      have hpI : p.toPoint2D ∉ (SimplePolygonBridge.toGeometry P).stratum .I := by
        rw [SimplePolygonBridge.toGeometry_stratum_I]
        exact fun h => h.2 hw0
      have hpE : p.toPoint2D ∈ (SimplePolygonBridge.toGeometry P).stratum .E := by
        rw [SimplePolygonBridge.toGeometry_stratum_E]
        rintro (h | h)
        · exact hnb h
        · exact h hw0
      simp only [hb, hw, Bool.false_eq_true, ↓reduceIte, (hpt .I).2 hpI, (hpt .B).2 hpB,
        (hpt .E).1 hpE, hBI, hBB, hBE, hEI, hEB, hEE]

/-- **Verified GIS-free Simple Features decision for point vs simple polygon.**
Decides all eight Simple Features relations (`equals`, `disjoint`, `intersects`,
`touches`, `within`, `contains`, `overlaps`, `crosses`) directly from integer
coordinates and proves exactness against the point-set definitions. -/
theorem pointPolygonClaimI_iff (c : Prover.Claim) (p : IPoint) (ps : List IPoint)
    (hS : (ComputationalGeometry.toRawPolygon ps).IsSimple) :
    c.decide .P .A (pointPolygonMatrixI p ps) = true ↔
      c.holds (.point p.toPoint2D)
        (SimplePolygonBridge.toGeometry ⟨ComputationalGeometry.toRawPolygon ps, hS⟩) := by
  rw [← pointPolygonMatrixI_eq p ps hS]
  exact c.decide_iff rfl rfl rfl

/-! ## Verified, GIS-free RCC8 and DE-9IM for integer rectangles -/

/-- An axis-aligned rectangle with integer coordinates. -/
structure IRect where
  xmin : Int
  xmax : Int
  ymin : Int
  ymax : Int
  deriving DecidableEq, Repr

namespace IRect

/-- Convert an integer rectangle to a real `Geospatial.Rect`. -/
def toRect (r : IRect) : Rect :=
  ⟨r.xmin, r.xmax, r.ymin, r.ymax⟩

/-- Non-degeneracy predicate: positive width and height. -/
def IsProper (r : IRect) : Prop :=
  r.xmin < r.xmax ∧ r.ymin < r.ymax

/-- A proper integer rectangle as a `RegularClosedRegion Point2D`. -/
def toRegularClosed (r : IRect) (h : r.IsProper) : RegularClosedRegion Point2D :=
  r.toRect.toRegularClosed (Int.cast_lt.mpr h.1) (Int.cast_lt.mpr h.2)

/-- Computable RCC8 classifier for two proper integer rectangles. -/
def rcc8 (r s : IRect) : RCC8.Relation :=
  if r == s then .eq
  else if r.xmax < s.xmin || s.xmax < r.xmin || r.ymax < s.ymin || s.ymax < r.ymin then .dc
  else if r.xmax == s.xmin || s.xmax == r.xmin || r.ymax == s.ymin || s.ymax == r.ymin then .ec
  else if s.xmin < r.xmin && r.xmax < s.xmax && s.ymin < r.ymin && r.ymax < s.ymax then .ntpp
  else if s.xmin ≤ r.xmin && r.xmax ≤ s.xmax && s.ymin ≤ r.ymin && r.ymax ≤ s.ymax then .tpp
  else if r.xmin < s.xmin && s.xmax < r.xmax && r.ymin < s.ymin && s.ymax < r.ymax then .ntppi
  else if r.xmin ≤ s.xmin && s.xmax ≤ r.xmax && r.ymin ≤ s.ymin && s.ymax ≤ r.ymax then .tppi
  else .po

/-- Exactness of `IRect.rcc8`: the computed RCC8 relation holds between the
two `RegularClosedRegion`s (and by `RCC8.pairwise_disjoint`, no other does). -/
theorem rcc8_holds (r s : IRect) (hr : r.IsProper) (hs : s.IsProper) :
    (r.rcc8 s).holds (r.toRegularClosed hr) (s.toRegularClosed hs) := by
  have hrx : (r.xmin : ℝ) < r.xmax := Int.cast_lt.mpr hr.1
  have hry : (r.ymin : ℝ) < r.ymax := Int.cast_lt.mpr hr.2
  have hsx : (s.xmin : ℝ) < s.xmax := Int.cast_lt.mpr hs.1
  have hsy : (s.ymin : ℝ) < s.ymax := Int.cast_lt.mpr hs.2
  have hSub : ∀ a b : IRect, a.IsProper → b.IsProper →
      ((a.toRect.toRegion ⊆ b.toRect.toRegion) ↔
        (b.xmin ≤ a.xmin ∧ a.xmax ≤ b.xmax ∧ b.ymin ≤ a.ymin ∧ a.ymax ≤ b.ymax)) := by
    intro a b ha hb
    constructor
    · intro hsub
      have h1 := hsub (show Point2D.mk a.xmin a.ymin ∈ a.toRect.toRegion by
        simp [Rect.toRegion, toRect]; exact ⟨Int.cast_le.mpr ha.1.le, Int.cast_le.mpr ha.2.le⟩)
      have h2 := hsub (show Point2D.mk a.xmax a.ymax ∈ a.toRect.toRegion by
        simp [Rect.toRegion, toRect]; exact ⟨Int.cast_le.mpr ha.1.le, Int.cast_le.mpr ha.2.le⟩)
      simp only [Rect.toRegion, toRect, mem_ofPred_eq, Point2D.x_mk, Point2D.y_mk] at h1 h2
      exact ⟨Int.cast_le.mp h1.1, Int.cast_le.mp h2.2.1, Int.cast_le.mp h1.2.2.1,
        Int.cast_le.mp h2.2.2.2⟩
    · intro ⟨h1, h2, h3, h4⟩
      exact Rect.within_of_bounds (Int.cast_le.mpr h1) (Int.cast_le.mpr h2)
        (Int.cast_le.mpr h3) (Int.cast_le.mpr h4)
  have hInter : ((r.toRect.toRegion ∩ s.toRect.toRegion).Nonempty) ↔
      (max r.xmin s.xmin ≤ min r.xmax s.xmax ∧ max r.ymin s.ymin ≤ min r.ymax s.ymax) := by
    constructor
    · rintro ⟨p, hpR, hpS⟩
      simp only [Rect.toRegion, toRect, mem_ofPred_eq] at hpR hpS
      have hx : (max r.xmin s.xmin : ℝ) ≤ (min r.xmax s.xmax : ℝ) :=
        max_le (hpR.1.trans (le_min hpR.2.1 hpS.2.1)) (hpS.1.trans (le_min hpR.2.1 hpS.2.1))
      have hy : (max r.ymin s.ymin : ℝ) ≤ (min r.ymax s.ymax : ℝ) :=
        max_le (hpR.2.2.1.trans (le_min hpR.2.2.2 hpS.2.2.2))
          (hpS.2.2.1.trans (le_min hpR.2.2.2 hpS.2.2.2))
      exact ⟨Int.cast_le.mp (by exact_mod_cast hx), Int.cast_le.mp (by exact_mod_cast hy)⟩
    · rintro ⟨hx, hy⟩
      refine ⟨Point2D.mk (max r.xmin s.xmin : Int) (max r.ymin s.ymin : Int), ?_, ?_⟩
      · simp only [Rect.toRegion, toRect, mem_ofPred_eq, Point2D.x_mk, Point2D.y_mk]
        exact ⟨by exact_mod_cast le_max_left r.xmin s.xmin,
          by exact_mod_cast hx.trans (min_le_left r.xmax s.xmax),
          by exact_mod_cast le_max_left r.ymin s.ymin,
          by exact_mod_cast hy.trans (min_le_left r.ymax s.ymax)⟩
      · simp only [Rect.toRegion, toRect, mem_ofPred_eq, Point2D.x_mk, Point2D.y_mk]
        exact ⟨by exact_mod_cast le_max_right r.xmin s.xmin,
          by exact_mod_cast hx.trans (min_le_right r.xmax s.xmax),
          by exact_mod_cast le_max_right r.ymin s.ymin,
          by exact_mod_cast hy.trans (min_le_right r.ymax s.ymax)⟩
  have hIntInter : ((interior r.toRect.toRegion ∩ interior s.toRect.toRegion).Nonempty) ↔
      (max r.xmin s.xmin < min r.xmax s.xmax ∧ max r.ymin s.ymin < min r.ymax s.ymax) := by
    rw [Rect.interior_toRegion, Rect.interior_toRegion]
    constructor
    · rintro ⟨p, hpR, hpS⟩
      simp only [Rect.openRegion, toRect, mem_ofPred_eq] at hpR hpS
      have hx : (max r.xmin s.xmin : ℝ) < (min r.xmax s.xmax : ℝ) :=
        max_lt (hpR.1.trans (lt_min hpR.2.1 hpS.2.1)) (hpS.1.trans (lt_min hpR.2.1 hpS.2.1))
      have hy : (max r.ymin s.ymin : ℝ) < (min r.ymax s.ymax : ℝ) := by
        exact max_lt (hpR.2.2.1.trans (lt_min hpR.2.2.2 hpS.2.2.2))
          (hpS.2.2.1.trans (lt_min hpR.2.2.2 hpS.2.2.2))
      exact ⟨Int.cast_lt.mp (by exact_mod_cast hx), Int.cast_lt.mp (by exact_mod_cast hy)⟩
    · rintro ⟨hx, hy⟩
      set x := ((max r.xmin s.xmin : ℝ) + (min r.xmax s.xmax : ℝ)) / 2
      set y := ((max r.ymin s.ymin : ℝ) + (min r.ymax s.ymax : ℝ)) / 2
      have hx' : (max r.xmin s.xmin : ℝ) < (min r.xmax s.xmax : ℝ) := by exact_mod_cast hx
      have hy' : (max r.ymin s.ymin : ℝ) < (min r.ymax s.ymax : ℝ) := by exact_mod_cast hy
      have hx1 : (r.xmin : ℝ) < x := by
        have : (r.xmin : ℝ) ≤ (max r.xmin s.xmin : ℝ) := by exact_mod_cast le_max_left r.xmin s.xmin
        simp only [x]; linarith
      have hx2 : x < (r.xmax : ℝ) := by
        have : (min r.xmax s.xmax : ℝ) ≤ (r.xmax : ℝ) := by exact_mod_cast min_le_left r.xmax s.xmax
        simp only [x]; linarith
      have hx3 : (s.xmin : ℝ) < x := by
        have : (s.xmin : ℝ) ≤ (max r.xmin s.xmin : ℝ) := by exact_mod_cast le_max_right r.xmin s.xmin
        simp only [x]; linarith
      have hx4 : x < (s.xmax : ℝ) := by
        have : (min r.xmax s.xmax : ℝ) ≤ (s.xmax : ℝ) := by exact_mod_cast min_le_right r.xmax s.xmax
        simp only [x]; linarith
      have hy1 : (r.ymin : ℝ) < y := by
        have : (r.ymin : ℝ) ≤ (max r.ymin s.ymin : ℝ) := by exact_mod_cast le_max_left r.ymin s.ymin
        simp only [y]; linarith
      have hy2 : y < (r.ymax : ℝ) := by
        have : (min r.ymax s.ymax : ℝ) ≤ (r.ymax : ℝ) := by exact_mod_cast min_le_left r.ymax s.ymax
        simp only [y]; linarith
      have hy3 : (s.ymin : ℝ) < y := by
        have : (s.ymin : ℝ) ≤ (max r.ymin s.ymin : ℝ) := by exact_mod_cast le_max_right r.ymin s.ymin
        simp only [y]; linarith
      have hy4 : y < (s.ymax : ℝ) := by
        have : (min r.ymax s.ymax : ℝ) ≤ (s.ymax : ℝ) := by exact_mod_cast min_le_right r.ymax s.ymax
        simp only [y]; linarith
      exact ⟨Point2D.mk x y, ⟨hx1, hx2, hy1, hy2⟩, ⟨hx3, hx4, hy3, hy4⟩⟩
  have hSubInt : ∀ a b : IRect, a.IsProper → b.IsProper →
      ((a.toRect.toRegion ⊆ interior b.toRect.toRegion) ↔
        (b.xmin < a.xmin ∧ a.xmax < b.xmax ∧ b.ymin < a.ymin ∧ a.ymax < b.ymax)) := by
    intro a b ha hb
    rw [Rect.interior_toRegion]
    constructor
    · intro hsub
      have h1 := hsub (show Point2D.mk a.xmin a.ymin ∈ a.toRect.toRegion by
        simp [Rect.toRegion, toRect]; exact ⟨Int.cast_le.mpr ha.1.le, Int.cast_le.mpr ha.2.le⟩)
      have h2 := hsub (show Point2D.mk a.xmax a.ymax ∈ a.toRect.toRegion by
        simp [Rect.toRegion, toRect]; exact ⟨Int.cast_le.mpr ha.1.le, Int.cast_le.mpr ha.2.le⟩)
      simp only [Rect.openRegion, toRect, mem_ofPred_eq, Point2D.x_mk, Point2D.y_mk] at h1 h2
      exact ⟨Int.cast_lt.mp h1.1, Int.cast_lt.mp h2.2.1, Int.cast_lt.mp h1.2.2.1,
        Int.cast_lt.mp h2.2.2.2⟩
    · intro ⟨h1, h2, h3, h4⟩
      rw [← Rect.interior_toRegion]
      exact Rect.within_interior_of_bounds (Int.cast_lt.mpr h1) (Int.cast_lt.mpr h2)
        (Int.cast_lt.mpr h3) (Int.cast_lt.mpr h4)
  rcases hr with ⟨hr1, hr2⟩
  rcases hs with ⟨hs1, hs2⟩
  unfold rcc8
  split_ifs with hEQ hDC hEC hNTPP hTPP hNTPPi hTPPi
  · -- EQ
    have heq : r = s := beq_iff_eq.mp hEQ
    subst heq
    exact rfl
  · -- DC
    show Geospatial.Disjoint r.toRect.toRegion s.toRect.toRegion
    rw [disjoint_iff_not_intersects, Geospatial.Intersects, hInter]
    simp only [Bool.or_eq_true, decide_eq_true_eq, max_le_iff, le_min_iff] at hDC ⊢
    omega
  · -- EC
    show Geospatial.Touches r.toRect.toRegion s.toRect.toRegion
    refine ⟨hInter.mpr ?_, disjoint_iff_not_intersects.mpr fun h => ?_⟩
    · simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, not_lt, max_le_iff, le_min_iff] at hDC ⊢
      omega
    · have := hIntInter.mp h
      simp only [Bool.or_eq_true, beq_iff_eq, max_lt_iff, lt_min_iff] at hEC this
      omega
  · -- NTPP
    show RCC8.NTPP (r.toRegularClosed ⟨hr1, hr2⟩) (s.toRegularClosed ⟨hs1, hs2⟩)
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hEQ hNTPP
    refine ⟨(hSubInt r s ⟨hr1, hr2⟩ ⟨hs1, hs2⟩).mpr ⟨hNTPP.1.1.1, hNTPP.1.1.2, hNTPP.1.2, hNTPP.2⟩,
      fun heq => hEQ ?_⟩
    change r.toRect.toRegion = s.toRect.toRegion at heq
    have hsr := (hSub s r ⟨hs1, hs2⟩ ⟨hr1, hr2⟩).mp (show s.toRect.toRegion ⊆ r.toRect.toRegion by rw [heq])
    cases r; cases s; simp only [IRect.mk.injEq]; omega
  · -- TPP
    show RCC8.TPP (r.toRegularClosed ⟨hr1, hr2⟩) (s.toRegularClosed ⟨hs1, hs2⟩)
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hEQ hNTPP hTPP
    refine ⟨(hSub r s ⟨hr1, hr2⟩ ⟨hs1, hs2⟩).mpr ⟨hTPP.1.1.1, hTPP.1.1.2, hTPP.1.2, hTPP.2⟩,
      fun heq => hEQ ?_, fun hint => hNTPP ?_⟩
    · change r.toRect.toRegion = s.toRect.toRegion at heq
      have ⟨h1, h2, h3, h4⟩ := (hSub s r ⟨hs1, hs2⟩ ⟨hr1, hr2⟩).mp (show s.toRect.toRegion ⊆ r.toRect.toRegion by rw [heq])
      cases r; cases s; simp only [IRect.mk.injEq] at *; omega
    · have := (hSubInt r s ⟨hr1, hr2⟩ ⟨hs1, hs2⟩).mp hint
      exact ⟨⟨⟨this.1, this.2.1⟩, this.2.2.1⟩, this.2.2.2⟩
  · -- NTPPi
    show RCC8.NTPPi (r.toRegularClosed ⟨hr1, hr2⟩) (s.toRegularClosed ⟨hs1, hs2⟩)
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hEQ hNTPPi
    refine ⟨(hSubInt s r ⟨hs1, hs2⟩ ⟨hr1, hr2⟩).mpr ⟨hNTPPi.1.1.1, hNTPPi.1.1.2, hNTPPi.1.2, hNTPPi.2⟩,
      fun heq => hEQ ?_⟩
    change s.toRect.toRegion = r.toRect.toRegion at heq
    have hrs := (hSub r s ⟨hr1, hr2⟩ ⟨hs1, hs2⟩).mp (show r.toRect.toRegion ⊆ s.toRect.toRegion by rw [heq])
    cases r; cases s; simp only [IRect.mk.injEq]; omega
  · -- TPPi
    show RCC8.TPPi (r.toRegularClosed ⟨hr1, hr2⟩) (s.toRegularClosed ⟨hs1, hs2⟩)
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hEQ hNTPPi hTPPi
    refine ⟨(hSub s r ⟨hs1, hs2⟩ ⟨hr1, hr2⟩).mpr ⟨hTPPi.1.1.1, hTPPi.1.1.2, hTPPi.1.2, hTPPi.2⟩,
      fun heq => hEQ ?_, fun hint => hNTPPi ?_⟩
    · change s.toRect.toRegion = r.toRect.toRegion at heq
      have ⟨h1, h2, h3, h4⟩ := (hSub r s ⟨hr1, hr2⟩ ⟨hs1, hs2⟩).mp (show r.toRect.toRegion ⊆ s.toRect.toRegion by rw [heq])
      cases r; cases s; simp only [IRect.mk.injEq] at *; omega
    · have := (hSubInt s r ⟨hs1, hs2⟩ ⟨hr1, hr2⟩).mp hint
      exact ⟨⟨⟨this.1, this.2.1⟩, this.2.2.1⟩, this.2.2.2⟩
  · -- PO
    show RCC8.PO (r.toRegularClosed ⟨hr1, hr2⟩) (s.toRegularClosed ⟨hs1, hs2⟩)
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, not_or, not_lt] at hDC hEC hTPP hTPPi
    refine ⟨hIntInter.mpr (by simp only [max_lt_iff, lt_min_iff]; omega), fun h => hTPP ?_, fun h => hTPPi ?_⟩
    · have := (hSub r s ⟨hr1, hr2⟩ ⟨hs1, hs2⟩).mp h
      exact ⟨⟨⟨this.1, this.2.1⟩, this.2.2.1⟩, this.2.2.2⟩
    · have := (hSub s r ⟨hs1, hs2⟩ ⟨hr1, hr2⟩).mp h
      exact ⟨⟨⟨this.1, this.2.1⟩, this.2.2.1⟩, this.2.2.2⟩

end IRect

end Geospatial
