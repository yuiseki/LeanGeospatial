import LeanGeospatial.GeoSPARQL.Table2.Kinds
import LeanGeospatial.Connected

/-!
# Table 2's `equals` pattern `TFFFTFFFT` against `Equals`

The pattern implies `Equals` for every pair (`equals_of_holds`), and across
kinds both are false (`equals_iff_of_kind_ne`). Within a kind the converse
fails:

| Kinds | Result |
| --- | --- |
| P/P | the pattern never matches two points, since points have no boundary (`not_holds_equals_point_point`), though every point equals itself |
| L/L | matches a line with itself exactly when the line is not closed (`holds_equals_line_self_iff`); a closed ring equals itself but does not match (`ring_counterexample`); and two open lines with the same points can fail to match (`backtrack_counterexample`) |
| A/A | agrees for areas other than the whole plane (`equals_area_area_iff`); the whole plane equals itself but does not match (`univ_counterexample`) |

The root is `holds_equals_self_iff`: a geometry matches the pattern with
itself exactly when its interior, boundary and exterior are all nonempty.
-/

namespace Geospatial.GeoSPARQL.Table2

open Geospatial DE9IM Geometry

theorem holds_equals_self_iff (g : Geometry) :
    Holds .equals g g ↔
      (g.stratum .I).Nonempty ∧ (g.stratum .B).Nonempty ∧ (g.stratum .E).Nonempty := by
  have hIB := g.stratum_I_inter_B
  have hIE : g.stratum .I ∩ g.stratum .E = ∅ := by
    rw [Set.eq_empty_iff_forall_not_mem]
    rintro p ⟨hI, hE⟩
    rw [g.stratum_E] at hE
    exact hE (g.stratum_I_subset hI)
  have hBE : g.stratum .B ∩ g.stratum .E = ∅ := by
    rw [Set.eq_empty_iff_forall_not_mem]
    rintro p ⟨hB, hE⟩
    rw [g.stratum_E] at hE
    exact hE (g.stratum_B_subset hB)
  rw [holds_equals_iff]
  simp only [equalsPattern, DimPattern.Matches, DimPatternChar.matches_T,
    DimPatternChar.matches_F, Geometry.cell, Set.inter_self]
  rw [Set.inter_comm (g.stratum .B) (g.stratum .I), Set.inter_comm (g.stratum .E) (g.stratum .I),
    Set.inter_comm (g.stratum .E) (g.stratum .B)]
  simp only [hIB, hIE, hBE, and_true, true_and]

/-! ## P/P -/

theorem not_holds_equals_point_point (p q : Point2D) : ¬ Holds .equals (point p) (point q) := by
  rw [holds_equals_iff]
  simp only [equalsPattern, DimPattern.Matches, DimPatternChar.matches_T]
  rintro ⟨-, -, -, -, ⟨x, hx, -⟩, -⟩
  exact hx

theorem point_counterexample (p : Point2D) :
    SF.Equals (point p) (point p) ∧ ¬ Holds .equals (point p) (point p) :=
  ⟨rfl, not_holds_equals_point_point p p⟩

/-! ## L/L -/

theorem line_carrier_ne_univ (l : LineString) : l.carrier ≠ Set.univ := by
  intro h
  have := l.interior_carrier
  rw [h, interior_univ] at this
  exact Set.univ_nonempty.ne_empty this

theorem holds_equals_line_self_iff (l : LineString) :
    Holds .equals (line l) (line l) ↔ ¬ l.IsRing := by
  rw [holds_equals_self_iff]
  have hI : ((line l).stratum .I).Nonempty := l.hasArc_interior.nonempty
  have hE : ((line l).stratum .E).Nonempty := by
    rw [(line l).stratum_E]
    exact Set.nonempty_compl.mpr (line_carrier_ne_univ l)
  simp only [hI, hE, true_and, and_true]
  show l.boundary.Nonempty ↔ _
  unfold LineString.boundary
  split_ifs with hr
  · simp [hr]
  · simp [hr]

/-- The unit square as a closed line string. -/
def square : LineString :=
  ⟨3, ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], by
    intro i
    fin_cases i <;> simp [Point2D.ext_iff]⟩

theorem square_isRing : square.IsRing := rfl

theorem ring_counterexample :
    SF.Equals (line square) (line square) ∧ ¬ Holds .equals (line square) (line square) :=
  ⟨rfl, fun h => (holds_equals_line_self_iff square).mp h square_isRing⟩

/-- `(0,0)–(2,0)`. -/
def straight : LineString := LineString.seg ⟨0, 0⟩ ⟨2, 0⟩ (by simp [Point2D.ext_iff])

/-- `(0,0)–(2,0)–(1,0)`: the same points, but ending at `(1,0)`. -/
def backtrack : LineString :=
  ⟨1, ![⟨0, 0⟩, ⟨2, 0⟩, ⟨1, 0⟩], by
    intro i
    fin_cases i <;> simp [Point2D.ext_iff]⟩

theorem backtrack_carrier : backtrack.carrier = segment ⟨0, 0⟩ ⟨2, 0⟩ := by
  apply Set.Subset.antisymm
  · intro p hp
    simp only [LineString.carrier, Set.mem_iUnion] at hp
    obtain ⟨i, hi⟩ := hp
    fin_cases i
    · exact hi
    · obtain ⟨t, ⟨h₀, h₁⟩, rfl⟩ := hi
      refine ⟨(2 - t) / 2, ⟨by linarith, by linarith⟩, ?_⟩
      simp [backtrack, Point2D.lerp]
      ring
  · intro p hp
    exact backtrack.segment_subset_carrier 0 hp

theorem backtrack_counterexample :
    SF.Equals (line straight) (line backtrack) ∧
      ¬ Holds .equals (line straight) (line backtrack) := by
  refine ⟨?_, fun h => ?_⟩
  · show straight.carrier = backtrack.carrier
    rw [backtrack_carrier, straight, LineString.seg_carrier]
  · rw [holds_equals_iff] at h
    simp only [equalsPattern, DimPattern.Matches, DimPatternChar.matches_F] at h
    obtain ⟨-, hIB, -⟩ := h
    -- (1,0) is inside the straight line and an end point of the backtracking one.
    have hmem : (⟨1, 0⟩ : Point2D) ∈ Geometry.cell .I .B (line straight) (line backtrack) := by
      refine ⟨?_, ?_⟩
      · show _ ∈ straight.interior
        rw [straight, LineString.seg_interior]
        refine ⟨⟨1 / 2, ⟨by norm_num, by norm_num⟩, by norm_num [Point2D.lerp]⟩, ?_⟩
        simp [Point2D.ext_iff]
      · show _ ∈ backtrack.boundary
        have hnr : ¬ backtrack.IsRing := by
          simp [LineString.IsRing, LineString.start, LineString.finish, backtrack,
            Point2D.ext_iff]
        simp only [LineString.boundary, hnr, if_false]
        right
        rfl
    rw [hIB] at hmem
    exact hmem

/-! ## A/A -/

theorem holds_equals_area_self_iff (A : RegularClosedRegion) (hA : (A : Region).Nonempty) :
    Holds .equals (area A) (area A) ↔ (A : Region) ≠ Set.univ := by
  rw [holds_equals_self_iff]
  have hI : ((area A).stratum .I).Nonempty := (A.nonempty_iff_interior_nonempty).mp hA
  simp only [hI, true_and]
  constructor
  · rintro ⟨-, hE⟩ hU
    rw [(area A).stratum_E] at hE
    obtain ⟨x, hx⟩ := hE
    exact hx (show x ∈ (A : Region) by rw [hU]; trivial)
  · intro hU
    refine ⟨boundary_nonempty A.isClosed hA hU, ?_⟩
    rw [(area A).stratum_E]
    exact Set.nonempty_compl.mpr hU

theorem equals_area_area_iff (A B : RegularClosedRegion) (hA : (A : Region).Nonempty)
    (hU : (A : Region) ≠ Set.univ) :
    SF.Equals (area A) (area B) ↔ Holds .equals (area A) (area B) := by
  constructor
  · intro he
    have : A = B := SetLike.coe_injective he
    subst this
    exact (holds_equals_area_self_iff A hA).mpr hU
  · exact equals_of_holds _ _

/-- The whole plane as an area. -/
def planeArea : RegularClosedRegion := ⟨Set.univ, by simp⟩

theorem univ_counterexample :
    SF.Equals (area planeArea) (area planeArea) ∧
      ¬ Holds .equals (area planeArea) (area planeArea) :=
  ⟨rfl, fun h => (holds_equals_area_self_iff planeArea ⟨⟨0, 0⟩, trivial⟩).mp h rfl⟩

end Geospatial.GeoSPARQL.Table2
