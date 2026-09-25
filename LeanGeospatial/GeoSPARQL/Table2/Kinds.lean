import LeanGeospatial.GeoSPARQL.Table2.Generic

/-!
# Table 2 against the definitions: overlaps, crosses, and equals across kinds

| Relation | Kinds | Result |
| --- | --- | --- |
| overlaps | A/A | matches (`overlaps_area_area`) |
| overlaps | L/L | matches, with `II = 1` (`overlaps_line_line`) |
| overlaps | P/P | neither ever holds for single points (`overlaps_point_point`) |
| crosses | L/L | matches, with `II = 0` (`crosses_line_line`); Table 6's longer row too (`crosses_line_line_table6`) |
| crosses | L/A | matches (`crosses_line_area`) |
| crosses | P/L, P/A | neither ever holds for single points (`crosses_point`) |
| equals | different kinds | neither ever holds, so they agree (`equals_iff_of_kind_ne`) |

L/L overlaps and L/L crosses are told apart by the value of `II` alone: `1`
when the lines share a stretch, `0` when they only meet in points
(`line_line_II_cases`).
-/

namespace Geospatial.GeoSPARQL.Table2

open Geospatial DE9IM Geometry

theorem line_carrier_nonempty (l : LineString) : l.carrier.Nonempty := ⟨_, l.start_mem⟩

theorem of_I_point (p : Point2D) : DimValue.of ((point p).stratum .I) = .d0 :=
  of_stratum_I (point p) ⟨p, rfl⟩

theorem of_I_line (l : LineString) : DimValue.of ((line l).stratum .I) = .d1 :=
  of_stratum_I (line l) (line_carrier_nonempty l)

theorem of_I_area (A : RegularClosedRegion) (hA : (A : Region).Nonempty) :
    DimValue.of ((area A).stratum .I) = .d2 :=
  of_stratum_I (area A) hA

def patternTTT : DimPattern := ⟨.T, .any, .T, .any, .any, .any, .T, .any, .any⟩

theorem parse_TTT : parseRows ["T*T***T**"] = some [patternTTT] := by decide

/-! ## A point's interior cannot meet both the interior and the exterior -/

theorem not_II_and_IE_point (p : Point2D) (g : Geometry) :
    ¬ ((Geometry.cell .I .I (point p) g).Nonempty ∧ (Geometry.cell .I .E (point p) g).Nonempty) := by
  rintro ⟨⟨x, hxp, hxI⟩, ⟨y, hyp, hyE⟩⟩
  have hx : x = p := hxp
  have hy : y = p := hyp
  subst hx hy
  rw [g.stratum_E] at hyE
  exact hyE (g.stratum_I_subset hxI)

theorem subset_of_II_point (p : Point2D) (g : Geometry) (h : (Geometry.cell .I .I (point p) g).Nonempty) :
    (point p).carrier ⊆ g.carrier := by
  obtain ⟨x, hxp, hxI⟩ := h
  have hx : x = p := hxp
  subst hx
  intro y hy
  have : y = x := hy
  subst this
  exact g.stratum_I_subset hxI

/-! ## overlaps -/

theorem area_II_d2_iff (A B : RegularClosedRegion) :
    DimValue.of (Geometry.cell .I .I (area A) (area B)) = .d2 ↔ (Geometry.cell .I .I (area A) (area B)).Nonempty := by
  constructor
  · intro h2
    refine Set.nonempty_iff_ne_empty.mpr fun he => ?_
    rw [(DimValue.of_eq_F_iff _).mpr he] at h2
    cases h2
  · intro hne
    exact (area_II_value A B).resolve_left fun hF => hne.ne_empty ((DimValue.of_eq_F_iff _).mp hF)

theorem overlaps_area_area (A B : RegularClosedRegion) (hA : (A : Region).Nonempty)
    (hB : (B : Region).Nonempty) :
    SF.Overlaps (area A) (area B) ↔ Holds .overlaps (area A) (area B) := by
  rw [holds_iff rfl parse_TTT, anyOf_singleton]
  simp only [patternTTT, DimPattern.Matches, DimPatternChar.matches_T, DimPatternChar.matches_any,
    and_true, true_and, SF.Overlaps, SF.II, of_I_area A hA, of_I_area B hB, area_II_d2_iff,
    not_subset_iff, Geometry.cell_swap (area B) (area A)]

def patternOverlapsLL : DimPattern := ⟨.d1, .any, .T, .any, .any, .any, .T, .any, .any⟩

theorem parse_overlapsLL : parseRows ["1*T***T**"] = some [patternOverlapsLL] := by decide

theorem overlaps_line_line (l m : LineString) :
    SF.Overlaps (line l) (line m) ↔ Holds .overlaps (line l) (line m) := by
  rw [holds_iff rfl parse_overlapsLL, anyOf_singleton]
  simp only [patternOverlapsLL, DimPattern.Matches, DimPatternChar.matches_T,
    DimPatternChar.matches_d1, DimPatternChar.matches_any, and_true, true_and, SF.Overlaps,
    SF.II, of_I_line, not_subset_iff, Geometry.cell_swap (line m) (line l)]

theorem overlaps_point_point (p q : Point2D) :
    ¬ SF.Overlaps (point p) (point q) ∧ ¬ Holds .overlaps (point p) (point q) := by
  constructor
  · rintro ⟨-, hII, hns, -⟩
    rw [of_I_point] at hII
    have hne : (Geometry.cell .I .I (point p) (point q)).Nonempty := by
      refine Set.nonempty_iff_ne_empty.mpr fun he => ?_
      rw [SF.II, (DimValue.of_eq_F_iff _).mpr he] at hII
      cases hII
    exact hns (subset_of_II_point p (point q) hne)
  · rw [holds_iff rfl parse_TTT, anyOf_singleton]
    simp only [patternTTT, DimPattern.Matches, DimPatternChar.matches_T,
      DimPatternChar.matches_any, and_true, true_and]
    rintro ⟨hII, hIE, -⟩
    exact not_II_and_IE_point p _ ⟨hII, hIE⟩

/-! ## crosses -/

/-- If one line lies in another, their interiors share an arc. -/
theorem hasArc_II_of_subset (l m : LineString) (hs : l.carrier ⊆ m.carrier) :
    HasArc (Geometry.cell .I .I (line l) (line m)) := by
  apply (l.hasArc_interior_diff m.boundary_finite).mono
  rintro p ⟨hpI, hpB⟩
  refine ⟨hpI, ?_⟩
  have hpm : p ∈ (line m).carrier := hs ((line l).stratum_I_subset hpI)
  rw [← (line m).stratum_I_union_B] at hpm
  exact hpm.resolve_right hpB

def patternCrossesLL : DimPattern := ⟨.d0, .any, .any, .any, .any, .any, .any, .any, .any⟩

theorem parse_crossesLL : parseRows ["0********"] = some [patternCrossesLL] := by decide

private theorem rank_lt_one {v : DimValue} (h : SF.rank v < 1) (hne : v ≠ .F) : v = .d0 := by
  cases v <;> simp_all [SF.rank]

theorem crosses_line_line (l m : LineString) :
    SF.Crosses (line l) (line m) ↔ Holds .crosses (line l) (line m) := by
  rw [holds_iff rfl parse_crossesLL, anyOf_singleton]
  simp only [patternCrossesLL, DimPattern.Matches, DimPatternChar.matches_d0,
    DimPatternChar.matches_any, and_true, SF.Crosses, SF.II, of_I_line]
  constructor
  · rintro ⟨hne, hrank, -, -⟩
    exact rank_lt_one (by simpa [SF.rank] using hrank)
      (fun hF => hne.ne_empty ((DimValue.of_eq_F_iff _).mp hF))
  · intro h0
    have hd := DimValue.of_describes (Geometry.cell .I .I (line l) (line m))
    rw [h0] at hd
    refine ⟨hd.1, by rw [h0]; simp [SF.rank], fun hs => hd.2.2 (hasArc_II_of_subset l m hs),
      fun hs => hd.2.2 ?_⟩
    have := hasArc_II_of_subset m l hs
    rwa [Geometry.cell, Set.inter_comm] at this

def patternCrossesLL6 : DimPattern := ⟨.d0, .any, .T, .any, .any, .any, .T, .any, .any⟩

theorem parse_crossesLL6 : DimPattern.ofString? table6CrossesLL = some patternCrossesLL6 := by
  decide

/-- Table 6's L/L row `0*T***T**` describes the same relation. -/
theorem crosses_line_line_table6 (l m : LineString) :
    SF.Crosses (line l) (line m) ↔ patternCrossesLL6.Matches (line l) (line m) := by
  have key := crosses_line_line l m
  rw [holds_iff rfl parse_crossesLL, anyOf_singleton] at key
  simp only [patternCrossesLL, DimPattern.Matches, DimPatternChar.matches_d0,
    DimPatternChar.matches_any, and_true] at key
  simp only [patternCrossesLL6, DimPattern.Matches, DimPatternChar.matches_d0,
    DimPatternChar.matches_T, DimPatternChar.matches_any, and_true, true_and]
  rw [← not_subset_iff, Geometry.cell_swap (line l) (line m) .E .I, ← not_subset_iff]
  constructor
  · intro h
    exact ⟨key.mp h, h.2.2.1, h.2.2.2⟩
  · rintro ⟨h0, -⟩
    exact key.mpr h0

theorem crosses_line_area (l : LineString) (A : RegularClosedRegion) (hA : (A : Region).Nonempty) :
    SF.Crosses (line l) (area A) ↔ Holds .crosses (line l) (area A) := by
  rw [holds_iff rfl parse_TTT, anyOf_singleton]
  have hAnot : ¬ (area A).carrier ⊆ (line l).carrier := by
    intro hs
    obtain ⟨p, hp⟩ := (A.nonempty_iff_interior_nonempty).mp hA
    have := interior_mono hs hp
    rw [show (line l).carrier = l.carrier from rfl, l.interior_carrier] at this
    exact this
  have hEI : (Geometry.cell .I .E (area A) (line l)).Nonempty := (not_subset_iff _ _).mp hAnot
  have hrank : SF.rank (DimValue.of (Geometry.cell .I .I (line l) (area A))) < 2 := by
    have := line_value_left_ne_d2 l .I (by decide) (area A) .I
    unfold matrix at this
    revert this
    cases DimValue.of (Geometry.cell .I .I (line l) (area A)) <;> simp [SF.rank]
  simp only [patternTTT, DimPattern.Matches, DimPatternChar.matches_T,
    DimPatternChar.matches_any, and_true, true_and, SF.Crosses, SF.II, of_I_line,
    of_I_area A hA, not_subset_iff, Geometry.cell_swap (area A) (line l) .I .E]
  simp only [Geometry.cell_swap (area A) (line l) .I .E] at hEI
  constructor
  · rintro ⟨hII, -, hIE, -⟩
    exact ⟨hII, hIE, hEI⟩
  · rintro ⟨hII, hIE, -⟩
    exact ⟨hII, by simpa [SF.rank] using hrank, hIE, hEI⟩

/-- A single point never crosses anything, and never matches `T*T***T**`. -/
theorem crosses_point (p : Point2D) (g : Geometry) :
    ¬ SF.Crosses (point p) g ∧ ¬ patternTTT.Matches (point p) g := by
  constructor
  · rintro ⟨hII, -, hns, -⟩
    exact hns (subset_of_II_point p g hII)
  · simp only [patternTTT, DimPattern.Matches, DimPatternChar.matches_T,
      DimPatternChar.matches_any, and_true, true_and]
    rintro ⟨hII, hIE, -⟩
    exact not_II_and_IE_point p g ⟨hII, hIE⟩

theorem crosses_point_line (p : Point2D) (l : LineString) :
    ¬ SF.Crosses (point p) (line l) ∧ ¬ Holds .crosses (point p) (line l) := by
  rw [holds_iff rfl parse_TTT, anyOf_singleton]
  exact crosses_point p (line l)

theorem crosses_point_area (p : Point2D) (A : RegularClosedRegion) :
    ¬ SF.Crosses (point p) (area A) ∧ ¬ Holds .crosses (point p) (area A) := by
  rw [holds_iff rfl parse_TTT, anyOf_singleton]
  exact crosses_point p (area A)

/-! ## equals across kinds -/

theorem not_equals_of_kind_ne {g h : Geometry} (hk : g.kind ≠ h.kind) (hg : g.carrier.Nonempty)
    (hh : h.carrier.Nonempty) : ¬ SF.Equals g h := by
  have lineArc : ∀ l : LineString, HasArc l.carrier := fun l =>
    l.hasArc_interior.mono Set.diff_subset
  have areaInt : ∀ A : RegularClosedRegion, (A : Region).Nonempty →
      (interior (A : Region)).Nonempty := fun A hA => (A.nonempty_iff_interior_nonempty).mp hA
  intro he
  cases g with
  | point p =>
    cases h with
    | point q => exact hk rfl
    | line m => exact not_hasArc_of_subset_singleton (le_of_eq he.symm) (lineArc m)
    | area B =>
      obtain ⟨x, hx⟩ := areaInt B hh
      have : x ∈ interior ({p} : Region) := by
        have h' : ((area B).carrier) = {p} := he.symm
        rw [show (B : Region) = {p} from h'] at hx
        exact hx
      rw [interior_singleton_eq_empty] at this
      exact this
  | line l =>
    cases h with
    | point q => exact not_hasArc_of_subset_singleton (le_of_eq he) (lineArc l)
    | line m => exact hk rfl
    | area B =>
      obtain ⟨x, hx⟩ := areaInt B hh
      have h' : (B : Region) = l.carrier := he.symm
      rw [h', l.interior_carrier] at hx
      exact hx
  | area A =>
    cases h with
    | point q =>
      obtain ⟨x, hx⟩ := areaInt A hg
      have h' : (A : Region) = {q} := he
      rw [h', interior_singleton_eq_empty] at hx
      exact hx
    | line m =>
      obtain ⟨x, hx⟩ := areaInt A hg
      have h' : (A : Region) = m.carrier := he
      rw [h', m.interior_carrier] at hx
      exact hx
    | area B => exact hk rfl

/-- Across kinds, `Equals` and the equals pattern agree: neither holds. -/
theorem equals_iff_of_kind_ne {g h : Geometry} (hk : g.kind ≠ h.kind) (hg : g.carrier.Nonempty)
    (hh : h.carrier.Nonempty) : SF.Equals g h ↔ Holds .equals g h :=
  ⟨fun he => absurd he (not_equals_of_kind_ne hk hg hh),
    fun hm => absurd (equals_of_holds g h hm) (not_equals_of_kind_ne hk hg hh)⟩

end Geospatial.GeoSPARQL.Table2
