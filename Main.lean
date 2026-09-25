import LeanGeospatial
import LeanGeospatial.ValidatorText

open Geospatial.RCC8

/-- Check each query of each input file and print the verdict. Every verdict
comes from `Graph.check`, whose soundness is proved in
`LeanGeospatial/Validator.lean`. -/
def main (args : List String) : IO UInt32 := do
  if args.isEmpty then
    IO.println "usage: lean-geospatial FILE..."
    IO.println "  lines: 'A NTPP B' (a fact), '? A C' (a query), '# ...' (a comment)"
    return 1
  let mut status : UInt32 := 0
  for path in args do
    match Input.parse (← IO.FS.readFile path) with
    | .error e =>
      IO.eprintln s!"{path}: {e}"
      status := 1
    | .ok input =>
      for (a, c) in input.queries do
        IO.println s!"{path}: {a} → {c}: {(input.graph.check a c).render}"
  return status
