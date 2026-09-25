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
`Prover.Claim.decide`:

```json
{"id":"case-2","matrix":"FF2F11212","claim":"touches"}
{"status":"entailed","id":"case-2","claim":"touches"}
```

Key order in the output carries no meaning.

## Trust boundary

This file is glue and is not proved: it turns JSON into a `Graph` or a
`Matrix9` and turns the answer back into JSON. The answer itself comes from
`Graph.check` (sound by `Graph.check_entailed`, `check_possible`,
`check_contradictory`) or from `Claim.decide` (exact by `Claim.decide_iff`).
Those theorems are about the facts as given: Lean does not know whether the
stated relations or matrix are true of any real geometry. Every problem with
the input (malformed JSON, missing field, unknown relation, a matrix that is
not 9 characters of `F 0 1 2`) is answered with `"status":"error"`.
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
  | "disjoint" | "sfdisjoint" => some .disjoint
  | "intersects" | "sfintersects" => some .intersects
  | "touches" | "sftouches" => some .touches
  | "within" | "sfwithin" => some .within
  | "contains" | "sfcontains" => some .contains
  | _ => none

def Claim.name : Claim → String
  | .disjoint => "disjoint"
  | .intersects => "intersects"
  | .touches => "touches"
  | .within => "within"
  | .contains => "contains"

def handleDE9IM (j : Json) : Except String (List (String × Json)) := do
  let ms ← j.getObjValAs? String "matrix"
  let some m := Matrix9.ofString? ms
    | throw s!"not a DE-9IM matrix (9 characters of F 0 1 2): {ms}"
  let cs ← j.getObjValAs? String "claim"
  let some c := Claim.ofString? cs
    | throw s!"unsupported claim: {cs} (supported: disjoint, intersects, touches, within, contains)"
  pure [("status", if c.decide m then "entailed" else "refuted"), ("claim", c.name)]

/-! ## Lines -/

def errorResponse (id : Json) (msg : String) : Json :=
  Json.mkObj [("id", id), ("status", "error"), ("error", msg)]

/-- Answer one request line. -/
def handleLine (line : String) : Json :=
  match Json.parse line with
  | .error e => errorResponse Json.null s!"malformed JSON: {e}"
  | .ok j =>
    let id := (j.getObjVal? "id").toOption.getD Json.null
    let result :=
      if (j.getObjVal? "matrix").toOption.isSome then handleDE9IM j else handleRCC8 j
    match result with
    | .ok fields => Json.mkObj (("id", id) :: fields)
    | .error e => errorResponse id e

end Geospatial.Prover
