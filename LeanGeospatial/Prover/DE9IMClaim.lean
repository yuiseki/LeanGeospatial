import LeanGeospatial.GeoSPARQL.Table2.Generic

/-!
# Deciding Simple Features claims from a stated DE-9IM matrix

An external tool reports the DE-9IM matrix of two geometries. Taking that
report as a premise, `Claim.decide` reads off whether a Simple Features
relation holds, and `Claim.decide_iff` proves the reading exact: for any
points, lines or areas `g`, `h` whose matrix is the stated one, `decide`
returns `true` exactly when the relation holds between them.

Only the five relations whose pattern characterisation is proved for every
kind of geometry are offered: disjoint, intersects, touches, within,
contains. Equals is left out because its pattern is not equivalent to it
(`GeoSPARQL/Table2/Counterexamples.lean`); overlaps and crosses depend on
the kinds.

Whether the stated matrix is actually the matrix of the geometries is not
something Lean checks; that is the premise.
-/

namespace Geospatial.Prover

open Geospatial DE9IM GeoSPARQL.Table2

/-- A DE-9IM matrix of values, one per cell. -/
structure Matrix9 where
  ii : DimValue
  ib : DimValue
  ie : DimValue
  bi : DimValue
  bb : DimValue
  be : DimValue
  ei : DimValue
  eb : DimValue
  ee : DimValue
  deriving DecidableEq

/-- The matrix of two geometries. -/
noncomputable def Matrix9.of (g h : Geometry) : Matrix9 :=
  ⟨matrix g h .I .I, matrix g h .I .B, matrix g h .I .E, matrix g h .B .I, matrix g h .B .B,
    matrix g h .B .E, matrix g h .E .I, matrix g h .E .B, matrix g h .E .E⟩

def DimValue.ofChar? : Char → Option DimValue
  | 'F' => some .F
  | '0' => some .d0
  | '1' => some .d1
  | '2' => some .d2
  | _ => none

/-- Read a 9-character matrix over `F 0 1 2`, as GEOS or JTS print it. -/
def Matrix9.ofString? (s : String) : Option Matrix9 :=
  match s.toList.map DimValue.ofChar? with
  | [some a, some b, some c, some d, some e, some f, some g, some h, some i] =>
    some ⟨a, b, c, d, e, f, g, h, i⟩
  | _ => none

/-- Whether a pattern character accepts a value, as a boolean. -/
def _root_.Geospatial.DE9IM.DimPatternChar.acceptsB : DimPatternChar → DimValue → Bool
  | .T, v => v != .F
  | .F, v => v == .F
  | .any, _ => true
  | .d0, v => v == .d0
  | .d1, v => v == .d1
  | .d2, v => v == .d2

theorem _root_.Geospatial.DE9IM.DimPatternChar.acceptsB_iff (c : DimPatternChar) (v : DimValue) :
    c.acceptsB v = true ↔ c.Accepts v := by
  cases c <;> cases v <;> simp [DimPatternChar.acceptsB, DimPatternChar.Accepts]

/-- Whether a pattern accepts a matrix. -/
def _root_.Geospatial.DE9IM.DimPattern.acceptsB (p : DimPattern) (m : Matrix9) : Bool :=
  p.ii.acceptsB m.ii && p.ib.acceptsB m.ib && p.ie.acceptsB m.ie &&
  p.bi.acceptsB m.bi && p.bb.acceptsB m.bb && p.be.acceptsB m.be &&
  p.ei.acceptsB m.ei && p.eb.acceptsB m.eb && p.ee.acceptsB m.ee

/-- Accepting the geometries' matrix is matching the geometries. -/
theorem _root_.Geospatial.DE9IM.DimPattern.acceptsB_of_iff (p : DimPattern) (g h : Geometry) :
    p.acceptsB (Matrix9.of g h) = true ↔ p.Matches g h := by
  simp only [DimPattern.acceptsB, Matrix9.of, Bool.and_eq_true, DimPatternChar.acceptsB_iff,
    DimPattern.Matches, DimPatternChar.Matches, matrix]
  tauto

/-! ## Claims -/

/-- The Simple Features relations that can be decided from a matrix alone. -/
inductive Claim where
  | disjoint | intersects | touches | within | contains
  deriving DecidableEq

/-- What the claim says about two geometries, in LeanGeospatial's terms. -/
def Claim.holds : Claim → Geometry → Geometry → Prop
  | .disjoint => SF.Disjoint
  | .intersects => SF.Intersects
  | .touches => SF.Touches
  | .within => SF.Within
  | .contains => SF.Contains

/-- The rows each claim is read from; each list is the one the Table 2
theorems prove equivalent to the claim. -/
def Claim.rows : Claim → List DimPattern
  | .disjoint => [disjointPattern]
  | .intersects =>
    [⟨.T, .any, .any, .any, .any, .any, .any, .any, .any⟩,
     ⟨.any, .T, .any, .any, .any, .any, .any, .any, .any⟩,
     ⟨.any, .any, .any, .T, .any, .any, .any, .any, .any⟩,
     ⟨.any, .any, .any, .any, .T, .any, .any, .any, .any⟩]
  | .touches =>
    [⟨.F, .T, .any, .any, .any, .any, .any, .any, .any⟩,
     ⟨.F, .any, .any, .T, .any, .any, .any, .any, .any⟩,
     ⟨.F, .any, .any, .any, .T, .any, .any, .any, .any⟩]
  | .within => [⟨.T, .any, .F, .any, .any, .F, .any, .any, .any⟩]
  | .contains => [⟨.T, .any, .any, .any, .any, .any, .F, .F, .any⟩]

/-- Two points never match the touches rows: points have no boundary. -/
theorem not_anyOf_touches_point_point (p q : Point2D) :
    ¬ AnyOf (Claim.rows .touches) (.point p) (.point q) := by
  simp only [GeoSPARQL.Table2.AnyOf, Claim.rows, List.mem_cons, List.mem_singleton,
    List.not_mem_nil, or_false, exists_eq_or_imp, exists_eq_left, DimPattern.Matches, DimPatternChar.matches_T,
    DimPatternChar.matches_F, DimPatternChar.matches_any, and_true, true_and]
  intro h
  rcases h with h | h | h
  · obtain ⟨x, -, hx⟩ := h.2; exact hx
  · obtain ⟨x, hx, -⟩ := h.2; exact hx
  · obtain ⟨x, hx, -⟩ := h.2; exact hx

theorem Claim.holds_iff_rows (c : Claim) (g h : Geometry) :
    c.holds g h ↔ AnyOf c.rows g h := by
  cases c <;> simp only [Claim.holds, Claim.rows]
  · rw [anyOf_singleton]; exact disjoint_iff g h
  · rw [intersects_iff, holds_iff (rows_intersects _ _) parse_intersects]
  · by_cases hk : g.kind = .P ∧ h.kind = .P
    · -- Two points: neither side holds.
      obtain ⟨hg, hh⟩ := hk
      cases g with
      | point p =>
        cases h with
        | point q =>
          exact ⟨fun h' => absurd h' (not_touches_point_point p q),
            fun h' => absurd h' (not_anyOf_touches_point_point p q)⟩
        | line _ => cases hh
        | area _ => cases hh
      | line _ => cases hg
      | area _ => cases hg
    · rw [touches_iff g h hk, holds_iff (rows_touches hk) parse_touches]
  · rw [within_iff, holds_iff (rows_within _ _) parse_within]
  · rw [contains_iff, holds_iff (rows_contains _ _) parse_contains]

/-- Read the claim off a matrix. -/
def Claim.decide (c : Claim) (m : Matrix9) : Bool := c.rows.any (·.acceptsB m)

/-- The reading is exact: for any geometries with the stated matrix, `decide`
is `true` exactly when the claim holds between them. -/
theorem Claim.decide_iff (c : Claim) {g h : Geometry} {m : Matrix9}
    (hm : Matrix9.of g h = m) : c.decide m = true ↔ c.holds g h := by
  rw [c.holds_iff_rows, ← hm]
  simp only [Claim.decide, List.any_eq_true, DimPattern.acceptsB_of_iff, GeoSPARQL.Table2.AnyOf]

end Geospatial.Prover
