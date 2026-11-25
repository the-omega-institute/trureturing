import Lake.Build.Trace

/-- Compute the Lake trace hash of each artifact in a staged import tree. -/
def main : IO Unit := do
  for path in (← (← IO.getStdin).readToEnd).splitOn "\n" do
    IO.println (← Lake.computeBinFileHash path).hex
