import LeanGeospatial.DE9IM
import LeanGeospatial.RCC8

/-!
# GeoSPARQL 1.1 tables, transcribed for comparison

Source: OGC GeoSPARQL 1.1, OGC 22-047r1,
<https://docs.ogc.org/is/22-047r1/22-047r1.html>, fetched 2026-09-25.

These strings and sets are copied from the specification as data. Nothing in
LeanGeospatial is defined from them; `GeoSPARQL/AreaArea.lean` compares them
with the relations defined from sets and topology. Transcription choices:

- Table 2 and Table 6 list `overlaps` for several geometry pairs; only the
  A/A pattern is transcribed. `crosses` is not transcribed.
- Multi-row patterns are lists, read as "any of them".
- Table 2 prints the `disjoint` pattern as `(FF**FF****)`, ten characters.
  It is kept as printed; `table2_disjoint_malformed` records that it is not
  a DE-9IM pattern.
-/

namespace Geospatial.GeoSPARQL

open Geospatial Geospatial.RCC8 Geospatial.DE9IM

/-- Table 4, "RCC8 Topological Relations" (geometry types A/A). -/
def table4 : Relation → String
  | .eq => "TFFFTFFFT"
  | .dc => "FFTFFTTTT"
  | .ec => "FFTFTTTTT"
  | .po => "TTTTTTTTT"
  | .tppi => "TTTFTTFFT"
  | .tpp => "TFFTTFTTT"
  | .ntpp => "TFFTFFTTT"
  | .ntppi => "TTTFFTFFT"

/-- Table 8, "RCC8 Query Functions". -/
def table8 : Relation → String
  | .eq => "TFFFTFFFT"
  | .dc => "FFTFFTTTT"
  | .ec => "FFTFTTTTT"
  | .po => "TTTTTTTTT"
  | .tppi => "TTTFTTFFT"
  | .tpp => "TFFTTFTTT"
  | .ntpp => "TFFTFFTTT"
  | .ntppi => "TTTFFTFFT"

/-- The relation names of the Simple Features family used here. -/
inductive SF where
  | equals | disjoint | intersects | touches | within | contains | overlaps
  deriving DecidableEq

/-- Table 2, "Simple Features Topological Relations" (`overlaps`: the A/A row). -/
def table2 : SF → List String
  | .equals => ["TFFFTFFFT"]
  | .disjoint => ["FF**FF****"]
  | .intersects => ["T********", "*T*******", "***T*****", "****T****"]
  | .touches => ["FT*******", "F**T*****", "F***T****"]
  | .within => ["T*F**F***"]
  | .contains => ["T*****FF*"]
  | .overlaps => ["T*T***T**"]

/-- Table 6, "Simple Features Query Functions" (`overlaps`: the A/A row). -/
def table6 : SF → List String
  | .equals => ["TFFFTFFFT"]
  | .disjoint => ["FF*FF****"]
  | .intersects => ["FT*******", "F**T*****", "F***T****"]
  | .touches => ["FT*******", "F**T*****", "F***T****"]
  | .within => ["T*F**F***"]
  | .contains => ["T*****FF*"]
  | .overlaps => ["T*T***T**"]

/-- Table 5, "Equivalent Simple Features, RCC8 and Egenhofer relations", the
Simple Features and RCC8 columns, stated there for closed, non-empty regions.
`intersects` is printed as "¬ disconnected". -/
def table5 : SF → Finset Relation
  | .equals => {.eq}
  | .disjoint => {.dc}
  | .intersects => {.ec, .po, .eq, .tpp, .ntpp, .tppi, .ntppi}
  | .touches => {.ec}
  | .within => {.ntpp, .tpp}
  | .contains => {.ntppi, .tppi}
  | .overlaps => {.po}

/-- Read every row of a multi-row pattern; `none` if any row is ill-formed. -/
def parseAll (ss : List String) : Option (List Pattern) := ss.mapM Pattern.ofString?

/-! ## Consistency of the tables with each other -/

/-- Tables 4 and 8 give the same RCC8 patterns. -/
theorem table4_eq_table8 (r : Relation) : table4 r = table8 r := by
  cases r <;> rfl

/-- Every RCC8 pattern is a well-formed 9-character pattern. -/
theorem table8_wellFormed (r : Relation) : (Pattern.ofString? (table8 r)).isSome = true := by
  cases r <;> decide

/-- The RCC8 pattern of Table 8 as a `Pattern`. -/
def rcc8Pattern (r : Relation) : Pattern := (Pattern.ofString? (table8 r)).get (table8_wellFormed r)

/-- The inverse relations' patterns are the transposes, as they should be. -/
theorem rcc8Pattern_tppi : rcc8Pattern .tppi = (rcc8Pattern .tpp).transpose := by decide
theorem rcc8Pattern_ntppi : rcc8Pattern .ntppi = (rcc8Pattern .ntpp).transpose := by decide

/-- Table 2's `disjoint` pattern, as printed, is not a DE-9IM pattern. -/
theorem table2_disjoint_malformed : parseAll (table2 .disjoint) = none := by decide

/-- Table 6's `sfIntersects` pattern is the `sfTouches` pattern. -/
theorem table6_intersects_eq_touches : table6 .intersects = table6 .touches := rfl

/-- Table 2 and Table 6 disagree on `intersects`. -/
theorem table2_intersects_ne_table6 : table2 .intersects ≠ table6 .intersects := by decide

/-- On every other relation, Tables 2 and 6 agree. -/
theorem table2_eq_table6 :
    table2 .equals = table6 .equals ∧ table2 .touches = table6 .touches ∧
    table2 .within = table6 .within ∧ table2 .contains = table6 .contains ∧
    table2 .overlaps = table6 .overlaps :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

end Geospatial.GeoSPARQL
