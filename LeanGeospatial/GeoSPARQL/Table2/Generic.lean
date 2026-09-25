import LeanGeospatial.GeoSPARQL.Table2.Spec

/-!
# Table 2 against the definitions: the relations settled for all kinds

Each theorem holds for every pair of geometries, so it covers all nine
combinations of P, L, A at once (for `touches`, all but P/P, as Table 2
says). The proofs use only the strata: `g ∩ h` is `II ∪ IB ∪ BI ∪ BB`, and
`g ⊆ h` is `IE = BE = ∅`.

| Relation | Result |
| --- | --- |
| disjoint | Table 2's entry is malformed (`not_holds_disjoint`); the 9-character version `FF*FF****` of Tables 3 and 6 matches (`disjoint_iff`) |
| intersects | matches (`intersects_iff`) |
| touches | matches for all kinds but P/P (`touches_iff`); for P/P it never holds (`not_touches_point_point`) |
| within | matches (`within_iff`) |
| contains | matches (`contains_iff`) |
| equals | the pattern implies `Equals` (`equals_of_holds`); the converse is settled per kind in `Kinds.lean` and `Counterexamples.lean` |
-/

namespace Geospatial.GeoSPARQL.Table2

open Geospatial DE9IM

variable (g h : Geometry)

/-! ## disjoint -/

/-- `FF*FF****`, the disjoint pattern of Tables 3 and 6. -/
def disjointPattern : DimPattern := ⟨.F, .F, .any, .F, .F, .any, .any, .any, .any⟩

theorem disjointPattern_parse : DimPattern.ofString? "FF*FF****" = some disjointPattern := by
  decide

theorem disjoint_iff : SF.Disjoint g h ↔ disjointPattern.Matches g h := by
  simp only [SF.Disjoint, Geometry.inter_eq_cells, Set.union_empty_iff, disjointPattern,
    DimPattern.Matches, DimPatternChar.matches_F, DimPatternChar.matches_any, and_true,
    true_and]
  tauto

/-! ## intersects -/

theorem rows_intersects (k k' : Kind) :
    table2 .intersects k k' = some ["T********", "*T*******", "***T*****", "****T****"] := by
  cases k <;> cases k' <;> rfl

theorem parse_intersects :
    parseRows ["T********", "*T*******", "***T*****", "****T****"] =
      some [⟨.T, .any, .any, .any, .any, .any, .any, .any, .any⟩,
        ⟨.any, .T, .any, .any, .any, .any, .any, .any, .any⟩,
        ⟨.any, .any, .any, .T, .any, .any, .any, .any, .any⟩,
        ⟨.any, .any, .any, .any, .T, .any, .any, .any, .any⟩] := by decide

theorem intersects_iff : SF.Intersects g h ↔ Holds .intersects g h := by
  rw [holds_iff (rows_intersects _ _) parse_intersects]
  simp only [AnyOf, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false,
    exists_eq_or_imp, exists_eq_left, DimPattern.Matches, DimPatternChar.matches_T,
    DimPatternChar.matches_any, and_true, true_and, SF.Intersects, Geometry.inter_eq_cells,
    Set.union_nonempty]
  tauto

/-! ## touches -/

theorem rows_touches {k k' : Kind} (hk : ¬ (k = .P ∧ k' = .P)) :
    table2 .touches k k' = some ["FT*******", "F**T*****", "F***T****"] := by
  cases k <;> cases k' <;> first | rfl | exact absurd ⟨rfl, rfl⟩ hk

theorem parse_touches :
    parseRows ["FT*******", "F**T*****", "F***T****"] =
      some [⟨.F, .T, .any, .any, .any, .any, .any, .any, .any⟩,
        ⟨.F, .any, .any, .T, .any, .any, .any, .any, .any⟩,
        ⟨.F, .any, .any, .any, .T, .any, .any, .any, .any⟩] := by decide

theorem touches_iff (hk : ¬ (g.kind = .P ∧ h.kind = .P)) :
    SF.Touches g h ↔ Holds .touches g h := by
  rw [holds_iff (rows_touches hk) parse_touches]
  simp only [AnyOf, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false,
    exists_eq_or_imp, exists_eq_left, DimPattern.Matches, DimPatternChar.matches_T,
    DimPatternChar.matches_F, DimPatternChar.matches_any, and_true, true_and, SF.Touches,
    SF.Intersects, SF.II, Geometry.inter_eq_cells, Set.union_nonempty]
  constructor
  · rintro ⟨((hII | hIB) | hBI) | hBB, h0⟩
    · exact absurd h0 hII.ne_empty
    · exact Or.inl ⟨h0, hIB⟩
    · exact Or.inr (Or.inl ⟨h0, hBI⟩)
    · exact Or.inr (Or.inr ⟨h0, hBB⟩)
  · rintro (⟨h0, h'⟩ | ⟨h0, h'⟩ | ⟨h0, h'⟩)
    · exact ⟨Or.inl (Or.inl (Or.inr h')), h0⟩
    · exact ⟨Or.inl (Or.inr h'), h0⟩
    · exact ⟨Or.inr h', h0⟩

/-- Two points never touch: sharing a point means sharing their interiors. -/
theorem not_touches_point_point (p q : Point2D) : ¬ SF.Touches (.point p) (.point q) := by
  rintro ⟨⟨x, hxp, hxq⟩, h0⟩
  have : x ∈ SF.II (.point p) (.point q) := ⟨hxp, hxq⟩
  rw [h0] at this
  exact this

theorem not_holds_touches_point_point (p q : Point2D) : ¬ Holds .touches (.point p) (.point q) := by
  rintro ⟨ss, ps, h₁, -⟩
  cases h₁

/-! ## within and contains -/

theorem rows_within (k k' : Kind) : table2 .within k k' = some ["T*F**F***"] := by
  cases k <;> cases k' <;> rfl

theorem parse_within :
    parseRows ["T*F**F***"] = some [⟨.T, .any, .F, .any, .any, .F, .any, .any, .any⟩] := by
  decide

theorem within_iff : SF.Within g h ↔ Holds .within g h := by
  rw [holds_iff (rows_within _ _) parse_within, anyOf_singleton]
  simp only [DimPattern.Matches, DimPatternChar.matches_T, DimPatternChar.matches_F,
    DimPatternChar.matches_any, and_true, true_and, SF.Within, SF.II,
    Geometry.subset_iff_cells]
  tauto

theorem rows_contains (k k' : Kind) : table2 .contains k k' = some ["T*****FF*"] := by
  cases k <;> cases k' <;> rfl

theorem parse_contains :
    parseRows ["T*****FF*"] = some [⟨.T, .any, .any, .any, .any, .any, .F, .F, .any⟩] := by
  decide

theorem contains_iff : SF.Contains g h ↔ Holds .contains g h := by
  rw [holds_iff (rows_contains _ _) parse_contains, anyOf_singleton]
  simp only [DimPattern.Matches, DimPatternChar.matches_T, DimPatternChar.matches_F,
    DimPatternChar.matches_any, and_true, true_and, SF.Contains, SF.Within, SF.II,
    Geometry.subset_iff_cells, Geometry.cell_swap h g]
  tauto

/-! ## equals: the pattern implies the relation -/

theorem rows_equals (k k' : Kind) : table2 .equals k k' = some ["TFFFTFFFT"] := by
  cases k <;> cases k' <;> rfl

def equalsPattern : DimPattern := ⟨.T, .F, .F, .F, .T, .F, .F, .F, .T⟩

theorem parse_equals : parseRows ["TFFFTFFFT"] = some [equalsPattern] := by decide

theorem holds_equals_iff : Holds .equals g h ↔ equalsPattern.Matches g h := by
  rw [holds_iff (rows_equals _ _) parse_equals, anyOf_singleton]

theorem equals_of_holds (hm : Holds .equals g h) : SF.Equals g h := by
  rw [holds_equals_iff] at hm
  simp only [equalsPattern, DimPattern.Matches, DimPatternChar.matches_T,
    DimPatternChar.matches_F] at hm
  obtain ⟨-, -, hIE, -, -, hBE, hEI, hEB, -⟩ := hm
  apply Set.Subset.antisymm
  · exact (Geometry.subset_iff_cells g h).mpr ⟨hIE, hBE⟩
  · rw [Geometry.cell_swap] at hEI hEB
    exact (Geometry.subset_iff_cells h g).mpr ⟨hEI, hEB⟩

end Geospatial.GeoSPARQL.Table2
