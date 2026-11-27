import OmegaChecks.InitInventory.PointerObservations

/-! Observe the native results used by the full Init inventory on the pinned Lean runtime. -/

unsafe def main (args : List String) : IO Unit := do
  if args == ["--exclusivity"] then
    let differs := OmegaChecks.InitBoundaries.PointerObservations.distinguishesExclusivity
    IO.println (differs 0 && differs 1)
    return
  let results ← OmegaChecks.InitBoundaries.PointerObservations.observe args.length
  unless results.length == 6 do
    throw <| IO.userError s!"only {results} distinguished the equal inputs"
  IO.println s!"Observed different results on equal inputs for {results}."
