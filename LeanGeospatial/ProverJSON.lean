import Lean.Data.Json
import LeanGeospatial.ValidatorText
import LeanGeospatial.Prover.DE9IMClaim

/-!
# JSON Lines front end for the prover

One request per line, one response per line. Two kinds of request:

RCC8, answered by `Graph.check`:

```json
{"id":"case-1","facts":[{"a":"A","relation":"NTPP","b":"B"},{"a":"B","relation":"NTPP","b":"C"}],"query":{"a":"A","b":"C"}}
{"status":"entailed","relation":"NTPP","id":"case-1"}
```

A Simple Features claim about a stated DE-9IM matrix, answered by
`Prover.Claim.decide`; overlaps and crosses also need the kinds:

```json
{"id":"case-2","matrix":"FF2F11212","claim":"touches"}
{"status":"entailed","id":"case-2","claim":"touches"}
{"id":"case-3","matrix":"0F1FF0102","claim":"crosses","a_kind":"line","b_kind":"line"}
{"status":"entailed","id":"case-3","claim":"crosses"}
```

Key order in the output carries no meaning.

## Trust boundary

This file is glue and is not proved: it turns JSON into a `Graph` or a
`Matrix9` and turns the answer back into JSON. The answer itself comes from
`Graph.check` (sound by `Graph.check_entailed`, `check_possible`,
`check_contradictory`) or from `Claim.decide` (exact by `Claim.decide_iff`;
for claims that do not need kinds, the kinds passed make no difference by
`Claim.decide_kinds_irrel`). Those theorems are about the facts as given: Lean does not know whether the
stated relations or matrix are true of any real geometry. Every problem with
the input (malformed JSON, missing field, unknown relation, a matrix that is
not 9 characters of `F 0 1 2`, a line with both `facts` and `matrix`) is
answered with `"status":"error"`.
-/

namespace Geospatial.Prover

open Lean Geospatial RCC8

/-! ## RCC8 requests -/

def parseFact (j : Json) : Except String Fact := do
  let a ← j.getObjValAs? String "a"
  let r ← j.getObjValAs? String "relation"
  let b ← j.getObjValAs? String "b"
  match Relation.ofString? r with
  | some rel => pure ⟨a, rel, b⟩
  | none => throw s!"unknown relation: {r}"

def verdictFields : Verdict → List (String × Json)
  | .entailed t => [("status", "entailed"), ("relation", t.name)]
  | .possible S =>
    [("status", "possible"),
     ("relations", toJson ((Relation.list.filter (· ∈ S)).map Relation.name))]
  | .contradictory => [("status", "contradictory")]

def handleRCC8 (j : Json) : Except String (List (String × Json)) := do
  let facts ← j.getObjValAs? (Array Json) "facts"
  let facts ← facts.mapM parseFact
  let q ← j.getObjVal? "query"
  let a ← q.getObjValAs? String "a"
  let c ← q.getObjValAs? String "b"
  pure (verdictFields ((⟨facts.toList⟩ : Graph).check a c))

/-! ## DE-9IM requests -/

def Claim.ofString? (s : String) : Option Claim :=
  match s.toLower with
  | "equals" | "sfequals" => some .equals
  | "disjoint" | "sfdisjoint" => some .disjoint
  | "intersects" | "sfintersects" => some .intersects
  | "touches" | "sftouches" => some .touches
  | "within" | "sfwithin" => some .within
  | "contains" | "sfcontains" => some .contains
  | "overlaps" | "sfoverlaps" => some .overlaps
  | "crosses" | "sfcrosses" => some .crosses
  | _ => none

def Claim.name : Claim → String
  | .equals => "equals"
  | .disjoint => "disjoint"
  | .intersects => "intersects"
  | .touches => "touches"
  | .within => "within"
  | .contains => "contains"
  | .overlaps => "overlaps"
  | .crosses => "crosses"

open GeoSPARQL.Table2 in
def kindOfString? (s : String) : Option Kind :=
  match s.toLower with
  | "point" | "p" => some .P
  | "line" | "linestring" | "l" => some .L
  | "area" | "polygon" | "a" => some .A
  | _ => none

open GeoSPARQL.Table2 in
/-- Read an optional kind field: `none` if absent, an error if present but
not a kind. -/
def parseKind (j : Json) (key : String) : Except String (Option Kind) :=
  match j.getObjVal? key with
  | .error _ => pure none
  | .ok v => do
    let s ← v.getStr?
    match kindOfString? s with
    | some k => pure (some k)
    | none => throw s!"unknown {key}: {s} (expected point, line or area)"

def handleDE9IM (j : Json) : Except String (List (String × Json)) := do
  let ms ← j.getObjValAs? String "matrix"
  let some m := Matrix9.ofString? ms
    | throw s!"not a DE-9IM matrix (9 characters of F 0 1 2): {ms}"
  let cs ← j.getObjValAs? String "claim"
  let some c := Claim.ofString? cs
    | throw s!"unsupported claim: {cs}"
  let ka ← parseKind j "a_kind"
  let kb ← parseKind j "b_kind"
  -- Kinds matter only for overlaps and crosses (`Claim.decide_kinds_irrel`).
  let (k, k') ← match c.needsKinds, ka, kb with
    | true, some k, some k' => pure (k, k')
    | true, _, _ => throw s!"claim {c.name} needs a_kind and b_kind (point, line or area)"
    | false, _, _ => pure (ka.getD .P, kb.getD .P)
  pure [("status", if c.decide k k' m then "entailed" else "refuted"), ("claim", c.name)]

/-! ## Lines -/

def errorResponse (id : Json) (msg : String) : Json :=
  Json.mkObj [("id", id), ("status", "error"), ("error", msg)]

/-- Answer one request line. -/
def handleLine (line : String) : Json :=
  match Json.parse line with
  | .error e => errorResponse Json.null s!"malformed JSON: {e}"
  | .ok j =>
    let id := (j.getObjVal? "id").toOption.getD Json.null
    let hasMatrix := (j.getObjVal? "matrix").toOption.isSome
    let hasFacts := (j.getObjVal? "facts").toOption.isSome
    let result :=
      if hasMatrix && hasFacts then
        .error "ambiguous request: has both facts (RCC8) and matrix (DE-9IM)"
      else if hasMatrix then handleDE9IM j else handleRCC8 j
    match result with
    | .ok fields => Json.mkObj (("id", id) :: fields)
    | .error e => errorResponse id e

end Geospatial.Prover
