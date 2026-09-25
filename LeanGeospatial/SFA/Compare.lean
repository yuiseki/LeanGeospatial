import LeanGeospatial.SFA.Spec
import LeanGeospatial.GeoSPARQL.Table2.Counterexamples
import LeanGeospatial.RCC8Witnesses

/-!
# SFA 1.2.1 against LeanGeospatial and against GeoSPARQL Table 2

Three things are kept apart: SFA's text (`SFA/Spec.lean`), LeanGeospatial's
definitions (`SimpleFeatures.lean`), and GeoSPARQL Table 2
(`GeoSPARQL/Table2/Spec.lean`).

## A. Strata (SFA 6.1.15.1)

`Geometry.lean` follows the text: `interior_eq_carrier_diff_boundary`,
`exterior_eq_compl`, `point_boundary`, `line_boundary`.

## B. SFA's point-set statements against LeanGeospatial

| Relation | Result |
| --- | --- |
| Equals, Disjoint, Intersects, Touches, Overlaps | same (`equals_iff` … `overlaps_iff`) |
| Within, Contains | LeanGeospatial is stronger: it asks for a shared interior point, SFA's statement does not. A point on a square's edge is SFA-within but not LeanGeospatial-within (`within_counterexample`) |
| Crosses | LeanGeospatial is stronger: it keeps the dimension condition SFA 1.2.1 dropped. Two collinear overlapping segments are SFA-crossing but not LeanGeospatial-crossing (`crosses_counterexample`); for P/L, P/A, L/A they agree (`crosses_line_area_iff`) |

## C. SFA's statements against SFA's own patterns

In each disagreement of B, LeanGeospatial agrees with SFA's pattern, and the
counterexample shows SFA's statement and pattern disagree:

| Relation | Statement | Pattern | Counterexample |
| --- | --- | --- | --- |
| Equals | `a ⊆ b ∧ b ⊆ a` | `TFFFTFFFT` | a point and itself (`sfa_equals_inconsistent`) |
| Within | `a ∩ b = a ∧ I(a) ∩ E(b) = ∅` | `T*F**F***` | a point on a square's edge (`sfa_within_inconsistent`) |
| Crosses L/L | `II ≠ ∅`, neither inside the other | `0********` | collinear overlapping segments (`sfa_crosses_inconsistent`) |

The note in SFA 1.2.1 that the dropped dimension condition "was always true"
holds for P/L, P/A and L/A but not for L/L.

## D. SFA's patterns against GeoSPARQL Table 2

Same strings for equals, touches, within, overlaps and L/L crosses
(`pattern_eq_table2`). Differences, all on the GeoSPARQL side:

- disjoint: SFA `FF*FF****`, Table 2 prints ten characters.
- crosses P/L, P/A, L/A: SFA `T*T******`, Table 2 `T*T***T**`. For single
  geometries they agree (`crosses_line_area_patterns`, and neither can hold
  for a point).

## Equals: `TFFFTFFFT` versus `T*F**FFF*`

`T*F**FFF*` (the pattern JTS uses) is `a ⊆ b ∧ b ⊆ a ∧ II ≠ ∅`
(`jtsEquals_iff`), and for nonempty geometries it is exactly `Equals`
(`equals_iff_jtsEquals`). `TFFFTFFFT` is `T*F**FFF*` plus
`IB = ∅ ∧ BI = ∅ ∧ BB ≠ ∅ ∧ EE ≠ ∅` (`sfaEquals_iff_jtsEquals_and`). Those
extra cells are what fail for points, closed rings, lines that double back,
and the whole plane.
-/

namespace Geospatial.SFA

open Geospatial DE9IM Geometry GeoSPARQL.Table2

/-! ## A. Strata -/

theorem interior_eq_carrier_diff_boundary (g : Geometry) :
    g.stratum .I = g.carrier \ g.stratum .B := by
  rw [← g.stratum_I_union_B]
  ext p
  constructor
  · intro hp
    refine ⟨Or.inl hp, fun hB => ?_⟩
    have : p ∈ g.stratum .I ∩ g.stratum .B := ⟨hp, hB⟩
    rw [g.stratum_I_inter_B] at this
    exact this
  · rintro ⟨hp | hp, hnB⟩
    · exact hp
    · exact absurd hp hnB

theorem exterior_eq_compl (g : Geometry) :
    g.stratum .E = (g.stratum .I ∪ g.stratum .B)ᶜ := by
  rw [g.stratum_E, g.stratum_I_union_B]

theorem point_boundary (p : Point2D) : (point p).stratum .B = ∅ := rfl

open Classical in
theorem line_boundary (l : LineString) :
    (line l).stratum .B = if l.IsRing then ∅ else {l.start, l.finish} := rfl

/-! ## B. SFA's statements against LeanGeospatial -/

section SetDefs

variable (a b : Geometry)

theorem inter_ne_left_iff : a.carrier ∩ b.carrier ≠ a.carrier ↔ ¬ a.carrier ⊆ b.carrier := by
  rw [Ne, Set.inter_eq_left]

theorem inter_ne_right_iff : a.carrier ∩ b.carrier ≠ b.carrier ↔ ¬ b.carrier ⊆ a.carrier := by
  rw [Ne, Set.inter_eq_right]

theorem equals_iff : SF.Equals a b ↔ SFA.Equals a b := Set.Subset.antisymm_iff

theorem disjoint_iff : SF.Disjoint a b ↔ SFA.Disjoint a b := Iff.rfl

theorem intersects_iff : SF.Intersects a b ↔ SFA.Intersects a b := by
  unfold SF.Intersects SFA.Intersects SFA.Disjoint
  exact Set.nonempty_iff_ne_empty

theorem touches_iff : SF.Touches a b ↔ SFA.Touches a b := by
  unfold SF.Touches SF.Intersects SFA.Touches
  rw [Set.nonempty_iff_ne_empty]
  exact and_comm

theorem overlaps_iff : SF.Overlaps a b ↔ SFA.Overlaps a b := by
  unfold SF.Overlaps SFA.Overlaps
  rw [inter_ne_left_iff, inter_ne_right_iff]
  constructor
  · rintro ⟨h₁, h₂, h₃, h₄⟩
    exact ⟨h₁, h₁.symm.trans h₂.symm, h₃, h₄⟩
  · rintro ⟨h₁, h₂, h₃, h₄⟩
    exact ⟨h₁, (h₁.trans h₂).symm, h₃, h₄⟩

theorem within_of_sf (h : SF.Within a b) : SFA.Within a b :=
  ⟨Set.inter_eq_left.mpr h.1, ((subset_iff_cells a b).mp h.1).1⟩

theorem contains_of_sf (h : SF.Contains a b) : SFA.Contains a b := within_of_sf b a h

theorem crosses_of_sf (h : SF.Crosses a b) : SFA.Crosses a b :=
  ⟨h.1.ne_empty, (inter_ne_left_iff a b).mpr h.2.2.1, (inter_ne_right_iff a b).mpr h.2.2.2⟩

end SetDefs

/-- For a line and a nonempty area, SFA's `Crosses` and LeanGeospatial's agree:
the dimension condition is automatic. -/
theorem crosses_line_area_iff (l : LineString) (A : RegularClosedRegion)
    (hA : (A : Region).Nonempty) : SF.Crosses (line l) (area A) ↔ SFA.Crosses (line l) (area A) := by
  refine ⟨crosses_of_sf _ _, fun ⟨hII, h₁, h₂⟩ => ?_⟩
  have hII' : (SF.II (line l) (area A)).Nonempty := Set.nonempty_iff_ne_empty.mpr hII
  have hrank : SF.rank (DimValue.of (Geometry.cell .I .I (line l) (area A))) < 2 := by
    have := line_value_left_ne_d2 l .I (by decide) (area A) .I
    unfold matrix at this
    revert this
    cases DimValue.of (Geometry.cell .I .I (line l) (area A)) <;> simp [SF.rank]
  refine ⟨hII', ?_, (inter_ne_left_iff _ _).mp h₁, (inter_ne_right_iff _ _).mp h₂⟩
  rw [of_I_line, of_I_area A hA]
  simpa [SF.rank] using hrank

/-! ## Counterexamples -/

/-- A point at the corner of the square `[0,2]²`. -/
noncomputable def cornerPoint : Geometry := .point ⟨0, 0⟩
noncomputable def square2 : RegularClosedRegion := Rect.area ⟨0, 2, 0, 2⟩ (by norm_num)

theorem within_counterexample :
    SFA.Within cornerPoint (.area square2) ∧ ¬ SF.Within cornerPoint (.area square2) := by
  have hmem : (⟨0, 0⟩ : Point2D) ∈ (square2 : Region) := by
    rw [square2, Rect.mem_area]; norm_num
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · show {(⟨0, 0⟩ : Point2D)} ∩ (square2 : Region) = {⟨0, 0⟩}
    exact Set.inter_eq_left.mpr (Set.singleton_subset_iff.mpr hmem)
  · rw [Set.eq_empty_iff_forall_not_mem]
    rintro p ⟨hp, hpE⟩
    have hp' : p = ⟨0, 0⟩ := hp
    subst hp'
    rw [(area square2).stratum_E] at hpE
    exact hpE hmem
  · rintro ⟨-, ⟨p, hp, hpI⟩⟩
    have hp' : p = ⟨0, 0⟩ := hp
    subst hp'
    change _ ∈ interior (square2 : Region) at hpI
    rw [square2, Rect.interior_area] at hpI
    obtain ⟨h, -⟩ := hpI
    norm_num at h

/-- `(0,0)–(2,0)` and `(1,0)–(3,0)`, overlapping between `x = 1` and `x = 2`. -/
noncomputable def segA : LineString := LineString.seg ⟨0, 0⟩ ⟨2, 0⟩ (by simp [Point2D.ext_iff])
noncomputable def segB : LineString := LineString.seg ⟨1, 0⟩ ⟨3, 0⟩ (by simp [Point2D.ext_iff])

theorem mem_segA_interior {p : Point2D} (t : ℝ) (ht₀ : 0 < t) (ht₁ : t < 2) (hp : p = ⟨t, 0⟩) :
    p ∈ (line segA).stratum .I := by
  subst hp
  show _ ∈ segA.interior
  rw [segA, LineString.seg_interior]
  refine ⟨⟨t / 2, ⟨by linarith, by linarith⟩, ?_⟩, ?_⟩
  · simp only [Point2D.lerp, Point2D.mk.injEq]
    constructor <;> ring
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Point2D.mk.injEq, and_true, not_or]
  exact ⟨by linarith, by linarith⟩

theorem mem_segB_interior {p : Point2D} (t : ℝ) (ht₀ : 1 < t) (ht₁ : t < 3) (hp : p = ⟨t, 0⟩) :
    p ∈ (line segB).stratum .I := by
  subst hp
  show _ ∈ segB.interior
  rw [segB, LineString.seg_interior]
  refine ⟨⟨(t - 1) / 2, ⟨by linarith, by linarith⟩, ?_⟩, ?_⟩
  · simp only [Point2D.lerp, Point2D.mk.injEq]
    constructor <;> ring
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Point2D.mk.injEq, and_true, not_or]
  exact ⟨by linarith, by linarith⟩

theorem segA_segB_hasArc : HasArc (Geometry.cell .I .I (line segA) (line segB)) := by
  have hne : (⟨5 / 4, 0⟩ : Point2D) ≠ ⟨7 / 4, 0⟩ := by simp [Point2D.ext_iff]; norm_num
  apply (hasArc_segment_diff hne Set.finite_empty).mono
  rintro p ⟨⟨t, ⟨h₀, h₁⟩, rfl⟩, -⟩
  have hp : (⟨5 / 4, 0⟩ : Point2D).lerp ⟨7 / 4, 0⟩ t = ⟨5 / 4 + t / 2, 0⟩ := by
    simp only [Point2D.lerp, Point2D.mk.injEq]
    constructor <;> ring
  exact ⟨mem_segA_interior (5 / 4 + t / 2) (by linarith) (by linarith) hp,
    mem_segB_interior (5 / 4 + t / 2) (by linarith) (by linarith) hp⟩

theorem crosses_counterexample :
    SFA.Crosses (line segA) (line segB) ∧ ¬ SF.Crosses (line segA) (line segB) := by
  have hAB : ¬ (line segA).carrier ⊆ (line segB).carrier := by
    intro h
    have : (⟨0, 0⟩ : Point2D) ∈ (line segB).carrier := h (segA.start_mem)
    change _ ∈ segB.carrier at this
    rw [segB, LineString.seg_carrier] at this
    obtain ⟨t, ⟨h₀, -⟩, ht⟩ := this
    simp only [Point2D.lerp, Point2D.mk.injEq] at ht
    linarith [ht.1]
  have hBA : ¬ (line segB).carrier ⊆ (line segA).carrier := by
    intro h
    have : (⟨3, 0⟩ : Point2D) ∈ (line segA).carrier := h (segB.finish_mem)
    change _ ∈ segA.carrier at this
    rw [segA, LineString.seg_carrier] at this
    obtain ⟨t, ⟨-, h₁⟩, ht⟩ := this
    simp only [Point2D.lerp, Point2D.mk.injEq] at ht
    linarith [ht.1]
  refine ⟨⟨segA_segB_hasArc.nonempty.ne_empty, (inter_ne_left_iff _ _).mpr hAB,
    (inter_ne_right_iff _ _).mpr hBA⟩, fun h => ?_⟩
  rw [crosses_line_line, holds_iff rfl parse_crossesLL, anyOf_singleton] at h
  simp only [patternCrossesLL, DimPattern.Matches, DimPatternChar.matches_d0,
    DimPatternChar.matches_any, and_true] at h
  have hd := DimValue.of_describes (Geometry.cell .I .I (line segA) (line segB))
  rw [h] at hd
  exact hd.2.2 segA_segB_hasArc

/-! ## C. SFA's statements against its own patterns -/

/-- SFA's pattern holds, read like `GeoSPARQL.Table2.Holds`. -/
def Holds (rel : Rel) (a b : Geometry) : Prop :=
  ∃ ss ps, pattern rel a.kind b.kind = some ss ∧ parseRows ss = some ps ∧ AnyOf ps a b

/-- Where SFA and Table 2 print the same rows, their `Holds` agree. -/
theorem holds_eq_of_pattern_eq {rel : Rel} {a b : Geometry}
    (h : pattern rel a.kind b.kind = table2 rel a.kind b.kind) :
    Holds rel a b ↔ GeoSPARQL.Table2.Holds rel a b := by
  unfold Holds GeoSPARQL.Table2.Holds
  rw [h]

/-- The same strings for equals, touches, within and overlaps, and for L/L
crosses. -/
theorem pattern_eq_table2 (k k' : Kind) :
    pattern .equals k k' = table2 .equals k k' ∧ pattern .touches k k' = table2 .touches k k' ∧
    pattern .within k k' = table2 .within k k' ∧ pattern .overlaps k k' = table2 .overlaps k k' ∧
    pattern .crosses .L .L = table2 .crosses .L .L := by
  cases k <;> cases k' <;> exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem sfa_equals_inconsistent (p : Point2D) :
    SFA.Equals (point p) (point p) ∧ ¬ Holds .equals (point p) (point p) := by
  refine ⟨⟨subset_rfl, subset_rfl⟩, fun h => ?_⟩
  rw [holds_eq_of_pattern_eq (pattern_eq_table2 .P .P).1] at h
  exact not_holds_equals_point_point p p h

theorem sfa_within_inconsistent :
    SFA.Within cornerPoint (.area square2) ∧ ¬ Holds .within cornerPoint (.area square2) := by
  refine ⟨within_counterexample.1, fun h => within_counterexample.2 ?_⟩
  rw [holds_eq_of_pattern_eq (pattern_eq_table2 .P .A).2.2.1] at h
  exact (within_iff _ _).mpr h

theorem sfa_crosses_inconsistent :
    SFA.Crosses (line segA) (line segB) ∧ ¬ Holds .crosses (line segA) (line segB) := by
  refine ⟨crosses_counterexample.1, fun h => crosses_counterexample.2 ?_⟩
  rw [holds_eq_of_pattern_eq (pattern_eq_table2 .L .L).2.2.2.2] at h
  exact (crosses_line_line segA segB).mpr h

/-! ## D. Crosses P/L, P/A, L/A: `T*T******` against `T*T***T**` -/

def sfaCrossesPattern : DimPattern := ⟨.T, .any, .T, .any, .any, .any, .any, .any, .any⟩

theorem parse_sfaCrosses : parseRows ["T*T******"] = some [sfaCrossesPattern] := by decide

/-- For a line and a nonempty area the extra `EI = T` of Table 2 is automatic. -/
theorem crosses_line_area_patterns (l : LineString) (A : RegularClosedRegion)
    (hA : (A : Region).Nonempty) :
    Holds .crosses (line l) (area A) ↔ GeoSPARQL.Table2.Holds .crosses (line l) (area A) := by
  rw [holds_iff rfl parse_TTT, anyOf_singleton]
  unfold Holds
  constructor
  · rintro ⟨ss, ps, h₁, h₂, hm⟩
    cases h₁
    rw [parse_sfaCrosses] at h₂
    cases h₂
    rw [anyOf_singleton] at hm
    simp only [sfaCrossesPattern, patternTTT, DimPattern.Matches, DimPatternChar.matches_T,
      DimPatternChar.matches_any, and_true, true_and] at hm ⊢
    have hAnot : ¬ (area A).carrier ⊆ (line l).carrier := by
      intro hs
      obtain ⟨p, hp⟩ := (A.nonempty_iff_interior_nonempty).mp hA
      have := interior_mono hs hp
      rw [show (line l).carrier = l.carrier from rfl, l.interior_carrier] at this
      exact this
    have hEI := (not_subset_iff _ _).mp hAnot
    rw [Geometry.cell_swap] at hEI
    exact ⟨hm.1, hm.2, hEI⟩
  · intro hm
    refine ⟨_, _, rfl, parse_sfaCrosses, ?_⟩
    rw [anyOf_singleton]
    simp only [sfaCrossesPattern, patternTTT, DimPattern.Matches, DimPatternChar.matches_T,
      DimPatternChar.matches_any, and_true, true_and] at hm ⊢
    exact ⟨hm.1, hm.2.1⟩

/-! ## Equals: `TFFFTFFFT` versus `T*F**FFF*` -/

/-- `T*F**FFF*`, the equality test JTS uses in place of SFA's pattern. -/
def jtsEquals : DimPattern := ⟨.T, .any, .F, .any, .any, .F, .F, .F, .any⟩

theorem parse_jtsEquals : DimPattern.ofString? "T*F**FFF*" = some jtsEquals := by decide

theorem jtsEquals_iff (a b : Geometry) :
    jtsEquals.Matches a b ↔
      a.carrier ⊆ b.carrier ∧ b.carrier ⊆ a.carrier ∧ (SF.II a b).Nonempty := by
  simp only [jtsEquals, DimPattern.Matches, DimPatternChar.matches_T, DimPatternChar.matches_F,
    DimPatternChar.matches_any, and_true, true_and, subset_iff_cells a b,
    subset_iff_cells b a, Geometry.cell_swap b a, SF.II]
  tauto

/-- Equal nonempty geometries share interior points. -/
theorem II_nonempty_of_equals {a b : Geometry} (ha : a.carrier.Nonempty) (hb : b.carrier.Nonempty)
    (h : SF.Equals a b) : (SF.II a b).Nonempty := by
  by_cases hk : a.kind = b.kind
  swap
  · exact absurd h (not_equals_of_kind_ne hk ha hb)
  cases a with
  | point p =>
    cases b with
    | point q =>
      have : ({p} : Region) = {q} := h
      have hpq : p = q := Set.singleton_eq_singleton_iff.mp this
      subst hpq
      exact ⟨p, rfl, rfl⟩
    | line _ => cases hk
    | area _ => cases hk
  | line l =>
    cases b with
    | point _ => cases hk
    | line m => exact (hasArc_II_of_subset l m (le_of_eq h)).nonempty
    | area _ => cases hk
  | area A =>
    cases b with
    | point _ => cases hk
    | line _ => cases hk
    | area B =>
      have hAB : A = B := SetLike.coe_injective h
      subst hAB
      obtain ⟨p, hp⟩ := (A.nonempty_iff_interior_nonempty).mp ha
      exact ⟨p, hp, hp⟩

/-- For nonempty geometries, `T*F**FFF*` is exactly `Equals`. -/
theorem equals_iff_jtsEquals {a b : Geometry} (ha : a.carrier.Nonempty)
    (hb : b.carrier.Nonempty) : SF.Equals a b ↔ jtsEquals.Matches a b := by
  rw [jtsEquals_iff]
  constructor
  · intro h
    exact ⟨le_of_eq h, le_of_eq h.symm, II_nonempty_of_equals ha hb h⟩
  · rintro ⟨h₁, h₂, -⟩
    exact Set.Subset.antisymm h₁ h₂

/-- `TFFFTFFFT` is `T*F**FFF*` with four more cells fixed. -/
theorem sfaEquals_iff_jtsEquals_and (a b : Geometry) :
    equalsPattern.Matches a b ↔
      jtsEquals.Matches a b ∧ Geometry.cell .I .B a b = ∅ ∧ Geometry.cell .B .I a b = ∅ ∧
        (Geometry.cell .B .B a b).Nonempty ∧ (Geometry.cell .E .E a b).Nonempty := by
  simp only [equalsPattern, jtsEquals, DimPattern.Matches, DimPatternChar.matches_T,
    DimPatternChar.matches_F, DimPatternChar.matches_any, and_true, true_and]
  tauto

end Geospatial.SFA
