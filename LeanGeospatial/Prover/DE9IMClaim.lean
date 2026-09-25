import LeanGeospatial.GeoSPARQL.Table2.Generic
import LeanGeospatial.SFA.Compare

/-!
# Deciding Simple Features claims from a stated DE-9IM matrix

An external tool reports the DE-9IM matrix of two geometries, and for
overlaps and crosses also their kinds (point, line, area). Taking that report
as a premise, `Claim.decide` reads off whether a Simple Features relation
holds, and `Claim.decide_iff` proves the reading exact: for any points, lines
or areas `g`, `h` with the stated matrix and kinds, `decide` returns `true`
exactly when the relation holds between them.

All eight relations are offered:

| Claim | Read from | Premises |
| --- | --- | --- |
| disjoint, intersects, touches, within, contains | the rows the Table 2 theorems prove equivalent | matrix |
| equals | `T*F**FFF*`, or `FFFFFFFF*` for two empty geometries | matrix |
| overlaps, crosses | the SFA definitions, with each interior's dimension given by its kind | matrix and kinds |

Equals does not use Table 2's `TFFFTFFFT`, which is not equivalent to it
(`GeoSPARQL/Table2/Counterexamples.lean`). Whether a geometry is empty can be
read off the matrix: its points are the six cells of its interior and
boundary rows.

Whether the stated matrix and kinds are actually those of the geometries is
not something Lean checks; that is the premise.
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

/-- The eight Simple Features relations. -/
inductive Claim where
  | equals | disjoint | intersects | touches | within | contains | overlaps | crosses
  deriving DecidableEq

/-- What the claim says about two geometries, in LeanGeospatial's terms. -/
def Claim.holds : Claim → Geometry → Geometry → Prop
  | .equals => SF.Equals
  | .disjoint => SF.Disjoint
  | .intersects => SF.Intersects
  | .touches => SF.Touches
  | .within => SF.Within
  | .contains => SF.Contains
  | .overlaps => SF.Overlaps
  | .crosses => SF.Crosses

/-- Whether the claim needs the geometries' kinds as well as the matrix. -/
def Claim.needsKinds : Claim → Bool
  | .overlaps | .crosses => true
  | _ => false

/-- `FFFFFFFF*`: both geometries are empty. -/
def allF : DimPattern := ⟨.F, .F, .F, .F, .F, .F, .F, .F, .any⟩

/-- The rows each matrix-only claim is read from. For the five relations
other than equals, each list is the one the Table 2 theorems prove equivalent
to the claim. -/
def Claim.rows : Claim → List DimPattern
  | .equals => [SFA.jtsEquals, allF]
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
  | .overlaps | .crosses => []

/-- Two points never match the touches rows: points have no boundary. -/
theorem not_anyOf_touches_point_point (p q : Point2D) :
    ¬ AnyOf (Claim.rows .touches) (.point p) (.point q) := by
  simp only [GeoSPARQL.Table2.AnyOf, Claim.rows, List.mem_cons, List.mem_singleton,
    List.not_mem_nil, or_false, exists_eq_or_imp, exists_eq_left, DimPattern.Matches,
    DimPatternChar.matches_T, DimPatternChar.matches_F, DimPatternChar.matches_any, and_true,
    true_and]
  intro h
  rcases h with h | h | h
  · obtain ⟨x, -, hx⟩ := h.2; exact hx
  · obtain ⟨x, hx, -⟩ := h.2; exact hx
  · obtain ⟨x, hx, -⟩ := h.2; exact hx

/-! ## Emptiness, read off the matrix -/

theorem stratum_eq_cells_left (g h : Geometry) (s : Stratum) :
    g.stratum s = Geometry.cell s .I g h ∪ Geometry.cell s .B g h ∪ Geometry.cell s .E g h := by
  have hU : h.stratum .I ∪ h.stratum .B ∪ h.stratum .E = Set.univ := by
    rw [h.stratum_I_union_B, h.stratum_E, Set.union_compl_self]
  ext p
  have hp : p ∈ h.stratum .I ∪ h.stratum .B ∪ h.stratum .E := hU ▸ trivial
  simp only [Geometry.cell, Set.mem_union, Set.mem_inter_iff] at hp ⊢
  tauto

theorem stratum_eq_cells_right (g h : Geometry) (t : Stratum) :
    h.stratum t = Geometry.cell .I t g h ∪ Geometry.cell .B t g h ∪ Geometry.cell .E t g h := by
  rw [stratum_eq_cells_left h g t, Geometry.cell_swap h g, Geometry.cell_swap h g,
    Geometry.cell_swap h g]

theorem carrier_eq_empty_iff_left (g h : Geometry) :
    g.carrier = ∅ ↔
      Geometry.cell .I .I g h = ∅ ∧ Geometry.cell .I .B g h = ∅ ∧ Geometry.cell .I .E g h = ∅ ∧
      Geometry.cell .B .I g h = ∅ ∧ Geometry.cell .B .B g h = ∅ ∧ Geometry.cell .B .E g h = ∅ := by
  rw [← g.stratum_I_union_B, stratum_eq_cells_left g h .I, stratum_eq_cells_left g h .B]
  simp only [Set.union_empty_iff]
  tauto

theorem carrier_eq_empty_iff_right (g h : Geometry) :
    h.carrier = ∅ ↔
      Geometry.cell .I .I g h = ∅ ∧ Geometry.cell .B .I g h = ∅ ∧ Geometry.cell .E .I g h = ∅ ∧
      Geometry.cell .I .B g h = ∅ ∧ Geometry.cell .B .B g h = ∅ ∧ Geometry.cell .E .B g h = ∅ := by
  rw [← h.stratum_I_union_B, stratum_eq_cells_right g h .I, stratum_eq_cells_right g h .B]
  simp only [Set.union_empty_iff]
  tauto

theorem allF_matches_iff (g h : Geometry) :
    allF.Matches g h ↔ g.carrier = ∅ ∧ h.carrier = ∅ := by
  rw [carrier_eq_empty_iff_left g h, carrier_eq_empty_iff_right g h]
  simp only [allF, DimPattern.Matches, DimPatternChar.matches_F, DimPatternChar.matches_any,
    and_true]
  tauto

/-- `Equals` is `T*F**FFF*`, or both geometries empty. -/
theorem equals_iff_rows (g h : Geometry) : SF.Equals g h ↔ AnyOf (Claim.rows .equals) g h := by
  simp only [GeoSPARQL.Table2.AnyOf, Claim.rows, List.mem_cons, List.mem_singleton,
    List.not_mem_nil, or_false, exists_eq_or_imp, exists_eq_left]
  rw [allF_matches_iff]
  unfold SF.Equals
  constructor
  · intro he
    by_cases hg : g.carrier.Nonempty
    · exact Or.inl ((SFA.equals_iff_jtsEquals hg (he ▸ hg)).mp he)
    · have hg' := Set.not_nonempty_iff_eq_empty.mp hg
      exact Or.inr ⟨hg', he ▸ hg'⟩
  · rintro (hj | ⟨hg, hh⟩)
    · obtain ⟨h₁, h₂, -⟩ := (SFA.jtsEquals_iff g h).mp hj
      exact Set.Subset.antisymm h₁ h₂
    · exact hg.trans hh.symm

theorem Claim.holds_iff_rows (c : Claim) (hc : c.needsKinds = false) (g h : Geometry) :
    c.holds g h ↔ AnyOf c.rows g h := by
  cases c <;> (try simp [Claim.needsKinds] at hc) <;> simp only [Claim.holds]
  · exact equals_iff_rows g h
  · simp only [Claim.rows]; rw [anyOf_singleton]; exact disjoint_iff g h
  · simp only [Claim.rows]; rw [intersects_iff, holds_iff (rows_intersects _ _) parse_intersects]
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
    · simp only [Claim.rows]; rw [touches_iff g h hk, holds_iff (rows_touches hk) parse_touches]
  · simp only [Claim.rows]; rw [within_iff, holds_iff (rows_within _ _) parse_within]
  · simp only [Claim.rows]; rw [contains_iff, holds_iff (rows_contains _ _) parse_contains]

/-! ## Interiors, from the kinds -/

/-- The dimension of a kind of geometry. -/
def _root_.Geospatial.GeoSPARQL.Table2.Kind.dimValue : Kind → DimValue
  | .P => .d0
  | .L => .d1
  | .A => .d2

/-- The first geometry is empty. -/
def Matrix9.aEmpty (m : Matrix9) : Bool :=
  m.ii == .F && m.ib == .F && m.ie == .F && m.bi == .F && m.bb == .F && m.be == .F

/-- The second geometry is empty. -/
def Matrix9.bEmpty (m : Matrix9) : Bool :=
  m.ii == .F && m.bi == .F && m.ei == .F && m.ib == .F && m.bb == .F && m.eb == .F

/-- The dimension of a geometry's interior: its kind's, or `F` if empty. -/
def interiorValue (k : Kind) (empty : Bool) : DimValue := if empty then .F else k.dimValue

theorem aEmpty_of_iff (g h : Geometry) : (Matrix9.of g h).aEmpty = true ↔ g.carrier = ∅ := by
  rw [carrier_eq_empty_iff_left g h]
  simp only [Matrix9.aEmpty, Matrix9.of, matrix, Bool.and_eq_true, beq_iff_eq,
    DimValue.of_eq_F_iff, and_assoc]

theorem bEmpty_of_iff (g h : Geometry) : (Matrix9.of g h).bEmpty = true ↔ h.carrier = ∅ := by
  rw [carrier_eq_empty_iff_right g h]
  simp only [Matrix9.bEmpty, Matrix9.of, matrix, Bool.and_eq_true, beq_iff_eq,
    DimValue.of_eq_F_iff, and_assoc]

theorem kind_dimValue (g : Geometry) : g.kind.dimValue = g.dimValue := by
  cases g <;> rfl

theorem of_interior_eq (g : Geometry) {e : Bool} (he : e = true ↔ g.carrier = ∅) :
    DimValue.of (g.stratum .I) = interiorValue g.kind e := by
  unfold interiorValue
  by_cases hg : g.carrier = ∅
  · rw [if_pos (he.mpr hg)]
    exact (DimValue.of_eq_F_iff _).mpr
      (Set.eq_empty_of_subset_empty (hg ▸ g.stratum_I_subset))
  · have : e ≠ true := fun h' => hg (he.mp h')
    rw [if_neg this, kind_dimValue]
    exact Geometry.of_stratum_I g (Set.nonempty_iff_ne_empty.mpr hg)

theorem DimValue.of_ne_F_iff (S : Region) : DimValue.of S ≠ .F ↔ S.Nonempty := by
  rw [Ne, DimValue.of_eq_F_iff, Set.nonempty_iff_ne_empty]

/-! ## Deciding a claim -/

/-- Read the claim off a matrix, using the kinds for overlaps and crosses. -/
def Claim.decide (c : Claim) (k k' : Kind) (m : Matrix9) : Bool :=
  match c with
  | .overlaps =>
    let da := interiorValue k m.aEmpty
    let db := interiorValue k' m.bEmpty
    da == db && m.ii == da && m.ie != .F && m.ei != .F
  | .crosses =>
    let da := interiorValue k m.aEmpty
    let db := interiorValue k' m.bEmpty
    m.ii != .F && Decidable.decide (SF.rank m.ii < max (SF.rank da) (SF.rank db)) &&
      m.ie != .F && m.ei != .F
  | c => c.rows.any (·.acceptsB m)

/-- The reading is exact: for any geometries with the stated matrix and
kinds, `decide` is `true` exactly when the claim holds between them. -/
theorem Claim.decide_iff (c : Claim) {g h : Geometry} {k k' : Kind} {m : Matrix9}
    (hk : g.kind = k) (hk' : h.kind = k') (hm : Matrix9.of g h = m) :
    c.decide k k' m = true ↔ c.holds g h := by
  subst hk hk' hm
  have hIa := of_interior_eq g (aEmpty_of_iff g h)
  have hIb := of_interior_eq h (bEmpty_of_iff g h)
  have hIE := Geometry.not_subset_iff g h
  have hEI := Geometry.not_subset_iff h g
  rw [Geometry.cell_swap h g] at hEI
  cases c
  case overlaps =>
    simp only [Claim.decide]
    rw [← hIa, ← hIb]
    simp only [Claim.holds, SF.Overlaps, SF.II, Bool.and_eq_true, beq_iff_eq, bne_iff_ne,
      Matrix9.of, matrix, DimValue.of_ne_F_iff, hIE, hEI]
    tauto
  case crosses =>
    simp only [Claim.decide]
    rw [← hIa, ← hIb]
    simp only [Claim.holds, SF.Crosses, SF.II, Bool.and_eq_true, bne_iff_ne, decide_eq_true_eq,
      Matrix9.of, matrix, DimValue.of_ne_F_iff, hIE, hEI]
    tauto
  all_goals
    rw [Claim.holds_iff_rows _ rfl]
    simp only [Claim.decide, List.any_eq_true, DimPattern.acceptsB_of_iff, GeoSPARQL.Table2.AnyOf]

/-- For claims that do not need them, the kinds make no difference. -/
theorem Claim.decide_kinds_irrel (c : Claim) (hc : c.needsKinds = false) (k k' j j' : Kind)
    (m : Matrix9) : c.decide k k' m = c.decide j j' m := by
  cases c <;> first | rfl | simp [Claim.needsKinds] at hc

/-- So for those claims any kinds may be passed. -/
theorem Claim.decide_iff_of_kindFree (c : Claim) (hc : c.needsKinds = false) (k k' : Kind)
    {g h : Geometry} {m : Matrix9} (hm : Matrix9.of g h = m) :
    c.decide k k' m = true ↔ c.holds g h := by
  rw [c.decide_kinds_irrel hc k k' g.kind h.kind m]
  exact c.decide_iff rfl rfl hm

end Geospatial.Prover
