import LeanGeospatial.ProverJSON

open Geospatial.Prover

/-- Read JSON Lines requests on stdin, write one JSON response per line on
stdout. Blank lines are skipped. -/
partial def loop (stdin : IO.FS.Stream) (stdout : IO.FS.Stream) : IO Unit := do
  let line ← stdin.getLine
  if line.isEmpty then return
  let line := line.trimRight
  unless line.isEmpty do
    stdout.putStrLn (handleLine line).compress
    stdout.flush
  loop stdin stdout

def main : IO Unit := do
  loop (← IO.getStdin) (← IO.getStdout)
