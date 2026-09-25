import LeanGeospatial.NineIntersection

/-!
# DE-9IM patterns, without dimensions

A pattern has one character per cell, in the order `II IB IE BI BB BE EI EB
EE`. For now only three characters are used, and their meaning comes from
the cells of `NineIntersection.lean`:

| Character | The cell must be |
| --- | --- |
| `T` | nonempty |
| `F` | empty |
| `*` | anything |

The dimension characters `0`, `1`, `2` are not supported yet; strings using
them do not parse. A pattern is a record with one field per cell, so a cell
cannot be skipped or swapped; `Pattern.ofString?` reads the usual 9-character
notation and rejects any other length or character.
-/

namespace Geospatial.DE9IM

open Geospatial

/-- A pattern character, without dimensions. -/
inductive PatternChar where
  /-- `T`: nonempty. -/
  | T
  /-- `F`: empty. -/
  | F
  /-- `*`: no constraint. -/
  | any
  deriving DecidableEq

/-- What a pattern character asks of a cell. -/
def PatternChar.Matches : PatternChar → Region → Prop
  | .T, S => S.Nonempty
  | .F, S => S = ∅
  | .any, _ => True

@[simp] theorem PatternChar.matches_T (S : Region) : PatternChar.T.Matches S ↔ S.Nonempty :=
  Iff.rfl
@[simp] theorem PatternChar.matches_F (S : Region) : PatternChar.F.Matches S ↔ S = ∅ := Iff.rfl
@[simp] theorem PatternChar.matches_any (S : Region) : PatternChar.any.Matches S ↔ True :=
  Iff.rfl

/-- A 9-cell pattern, one field per cell. -/
structure Pattern where
  ii : PatternChar
  ib : PatternChar
  ie : PatternChar
  bi : PatternChar
  bb : PatternChar
  be : PatternChar
  ei : PatternChar
  eb : PatternChar
  ee : PatternChar
  deriving DecidableEq

/-- `A` and `B` match the pattern when each cell meets its character. -/
def Pattern.Matches (p : Pattern) (A B : Region) : Prop :=
  p.ii.Matches (II A B) ∧ p.ib.Matches (IB A B) ∧ p.ie.Matches (IE A B) ∧
  p.bi.Matches (BI A B) ∧ p.bb.Matches (BB A B) ∧ p.be.Matches (BE A B) ∧
  p.ei.Matches (EI A B) ∧ p.eb.Matches (EB A B) ∧ p.ee.Matches (EE A B)

/-- The pattern for the regions the other way round. -/
def Pattern.transpose (p : Pattern) : Pattern :=
  ⟨p.ii, p.bi, p.ei, p.ib, p.bb, p.eb, p.ie, p.be, p.ee⟩

theorem Pattern.matches_transpose (p : Pattern) (A B : Region) :
    p.transpose.Matches A B ↔ p.Matches B A := by
  simp only [Pattern.Matches, Pattern.transpose, II, IB, IE, BI, BB, BE, EI, EB, EE,
    cell_swap _ _ A B]
  tauto

/-- Several patterns, read as "any of them" (a multi-row pattern). -/
def AnyOf (ps : List Pattern) (A B : Region) : Prop := ∃ p ∈ ps, p.Matches A B

/-! ## The 9-character notation -/

def PatternChar.ofChar? : Char → Option PatternChar
  | 'T' => some .T
  | 'F' => some .F
  | '*' => some .any
  | _ => none

def PatternChar.toChar : PatternChar → Char
  | .T => 'T'
  | .F => 'F'
  | .any => '*'

/-- Read a 9-character pattern. Any other length, or any character besides
`T`, `F`, `*`, gives `none`. -/
def Pattern.ofString? (s : String) : Option Pattern :=
  match s.toList.map PatternChar.ofChar? with
  | [some a, some b, some c, some d, some e, some f, some g, some h, some i] =>
    some ⟨a, b, c, d, e, f, g, h, i⟩
  | _ => none

def Pattern.toString (p : Pattern) : String :=
  String.mk ([p.ii, p.ib, p.ie, p.bi, p.bb, p.be, p.ei, p.eb, p.ee].map PatternChar.toChar)

/-- A pattern from a string known to be well formed; an ill-formed literal is a
compile-time error. -/
def Pattern.parse (s : String) (h : (Pattern.ofString? s).isSome = true := by decide) :
    Pattern :=
  (Pattern.ofString? s).get h

end Geospatial.DE9IM
