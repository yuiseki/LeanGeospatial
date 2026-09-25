import LeanGeospatial.Validator

/-!
# A plain-text format for the validator

One item per line:

```
# a comment
DistrictA NTPP CityB      -- a fact: feature, relation, feature
? DistrictA ProvinceC     -- a query: check this pair
```

Relation names are `DC EC PO EQ TPP NTPP TPPi NTPPi`, in any letter case.
Parsing only builds a `Graph` and a list of queries; every verdict still
comes from `Graph.check` and its theorems.
-/

namespace Geospatial.RCC8

/-- Read a relation name, ignoring letter case. -/
def Relation.ofString? (s : String) : Option Relation :=
  match s.toLower with
  | "dc" => some .dc
  | "ec" => some .ec
  | "po" => some .po
  | "eq" => some .eq
  | "tpp" => some .tpp
  | "ntpp" => some .ntpp
  | "tppi" => some .tppi
  | "ntppi" => some .ntppi
  | _ => none

/-- The relation's usual name. -/
def Relation.name : Relation → String
  | .dc => "DC" | .ec => "EC" | .po => "PO" | .eq => "EQ"
  | .tpp => "TPP" | .ntpp => "NTPP" | .tppi => "TPPi" | .ntppi => "NTPPi"

/-- A parsed input file. -/
structure Input where
  graph : Graph
  queries : List (FeatureId × FeatureId)

/-- Parse the text format. Returns the first bad line on failure. -/
def Input.parse (text : String) : Except String Input := do
  let mut facts : Array Fact := #[]
  let mut queries : Array (FeatureId × FeatureId) := #[]
  for line in text.splitOn "\n" do
    let words := (line.splitOn " ").filter (· ≠ "")
    match words with
    | [] => pure ()
    | w :: _ =>
      if w.startsWith "#" then pure ()
      else match words with
        | ["?", a, c] => queries := queries.push (a, c)
        | [a, r, b] =>
          match Relation.ofString? r with
          | some rel => facts := facts.push ⟨a, rel, b⟩
          | none => throw s!"unknown relation: {line}"
        | _ => throw s!"cannot read line: {line}"
  return ⟨⟨facts.toList⟩, queries.toList⟩

/-- A verdict as text. -/
def Verdict.render : Verdict → String
  | .entailed t => s!"entailed {t.name}"
  | .possible S =>
    s!"possible \{{", ".intercalate ((Relation.list.filter (· ∈ S)).map Relation.name)}}"
  | .contradictory => "contradictory"

end Geospatial.RCC8
