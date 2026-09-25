import LeanGeospatial.SimpleFeatures

/-!
# GeoSPARQL 1.1 Table 2, with geometry types and dimensions

Source: OGC GeoSPARQL 1.1 (OGC 22-047r1), Table 2 "Simple Features
Topological Relations", fetched 2026-09-25. Transcribed as data, for
comparison only.

`table2 rel k k'` is the list of pattern rows Table 2 gives for `rel` between
a geometry of kind `k` and one of kind `k'`, or `none` where Table 2 says the
relation does not apply. Rows are read as "any of them".

Also transcribed for comparison: Table 6's `sfCrosses` L/L row
`(0*T***T**)`, which differs from Table 2's `(0********)`.
-/

namespace Geospatial.GeoSPARQL.Table2

open Geospatial DE9IM

/-- The geometry kinds of Table 2: P, L, A. -/
inductive Kind where
  | P | L | A
  deriving DecidableEq

def _root_.Geospatial.Geometry.kind : Geometry → Kind
  | .point _ => .P
  | .line _ => .L
  | .area _ => .A

/-- The Simple Features relations of Table 2. -/
inductive Rel where
  | equals | disjoint | intersects | touches | within | contains | overlaps | crosses
  deriving DecidableEq

/-- Table 2, per relation and pair of kinds. -/
def table2 : Rel → Kind → Kind → Option (List String)
  | .equals, _, _ => some ["TFFFTFFFT"]
  | .disjoint, _, _ => some ["FF**FF****"]
  | .intersects, _, _ => some ["T********", "*T*******", "***T*****", "****T****"]
  | .touches, .P, .P => none
  | .touches, _, _ => some ["FT*******", "F**T*****", "F***T****"]
  | .within, _, _ => some ["T*F**F***"]
  | .contains, _, _ => some ["T*****FF*"]
  | .overlaps, .A, .A => some ["T*T***T**"]
  | .overlaps, .P, .P => some ["T*T***T**"]
  | .overlaps, .L, .L => some ["1*T***T**"]
  | .overlaps, _, _ => none
  | .crosses, .P, .L => some ["T*T***T**"]
  | .crosses, .P, .A => some ["T*T***T**"]
  | .crosses, .L, .A => some ["T*T***T**"]
  | .crosses, .L, .L => some ["0********"]
  | .crosses, _, _ => none

/-- Table 6's `sfCrosses` row for L/L. -/
def table6CrossesLL : String := "0*T***T**"

/-- Read every row; `none` if any row is not a 9-character pattern. -/
def parseRows (ss : List String) : Option (List DimPattern) := ss.mapM DimPattern.ofString?

/-- Some row matches. -/
def AnyOf (ps : List DimPattern) (g h : Geometry) : Prop := ∃ p ∈ ps, p.Matches g h

/-- `g` and `h` satisfy the Table 2 entry for `rel`: it applies to their
kinds, every row is well formed, and some row matches. -/
def Holds (rel : Rel) (g h : Geometry) : Prop :=
  ∃ ss ps, table2 rel g.kind h.kind = some ss ∧ parseRows ss = some ps ∧ AnyOf ps g h

theorem holds_iff {rel : Rel} {g h : Geometry} {ss : List String} {ps : List DimPattern}
    (h₁ : table2 rel g.kind h.kind = some ss) (h₂ : parseRows ss = some ps) :
    Holds rel g h ↔ AnyOf ps g h := by
  constructor
  · rintro ⟨ss', ps', e₁, e₂, hm⟩
    rw [h₁] at e₁
    cases e₁
    rw [h₂] at e₂
    cases e₂
    exact hm
  · exact fun hm => ⟨ss, ps, h₁, h₂, hm⟩

theorem anyOf_singleton {p : DimPattern} {g h : Geometry} : AnyOf [p] g h ↔ p.Matches g h := by
  simp [AnyOf]

/-- Table 2's `disjoint` entry is ten characters long, so it never holds. -/
theorem disjoint_row_malformed (k k' : Kind) : parseRows (table2 .disjoint k k' |>.getD []) = none := by
  cases k <;> cases k' <;> decide

theorem not_holds_disjoint (g h : Geometry) : ¬ Holds .disjoint g h := by
  rintro ⟨ss, ps, h₁, h₂, -⟩
  have := disjoint_row_malformed g.kind h.kind
  rw [h₁] at this
  simp only [Option.getD_some] at this
  rw [h₂] at this
  cases this

end Geospatial.GeoSPARQL.Table2
