import LeanGeospatial.ProverJSON

open Geospatial.Prover

/-- Read JSON Lines requests on stdin, write one JSON response per line on
stdout. Blank lines are skipped.

The loop is a `repeat`, not a recursive function: a recursive loop whose call
sits after an `unless` block compiles to a call through a separate closure,
not a jump, and overflowed the stack after about 170,000 lines. -/
def main : IO Unit := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  repeat do
    let line ← stdin.getLine
    if line.isEmpty then break
    let line := line.trimRight
    unless line.isEmpty do
      stdout.putStrLn (handleLine line).compress
      stdout.flush
