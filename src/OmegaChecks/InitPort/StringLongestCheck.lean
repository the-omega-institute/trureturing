module
meta import OmegaChecks.InitPort.StrictReplay
import OmegaChecks.InitPort.StrictReplay
meta import OmegaChecks.InitPort.Translation
import OmegaChecks.InitPort.Translation

open Lean InitKernelPort

/-- Compare the complete translated types and replay both implications before emitting evidence. -/
public def main (args : List String) : IO Unit := do
  let [lib, evidence, output] := args | throw <| IO.userError "expected strict library, proof directory, and output"
  let owner := `Init.Data.String.Lemmas.Pattern.Basic
  let target := `Classical.em
  let official ← importModules #[{module := owner}] {} (level := .private)
  let some em := official.find? target | throw <| IO.userError "missing official excluded middle"
  searchPathRef.set [evidence, lib]
  let proofModule := `StrictStringLongest
  let env ← importModules #[{module := proofModule}] {} (level := .private)
  unless env.allImportedModuleNames.all (fun n => n == proofModule || n.getRoot == `OmegaInit) do
    throw <| IO.userError "unexpected import in strict string evidence"
  let implications := #[
    (`String.Slice.Pattern.Model.IsMatch.exists_isLongestMatch, `OmegaStrictString.excludedMiddleOfLongest),
    (`String.Slice.Pattern.Model.IsRevMatch.exists_isLongestRevMatch, `OmegaStrictString.excludedMiddleOfRevLongest)]
  for (name, witness) in implications do
    let some source := official.find? name | throw <| IO.userError s!"missing official theorem {name}"
    let some proof := env.find? witness | throw <| IO.userError s!"missing strict proof {witness}"
    let expected := Expr.forallE .anonymous (translate portName source.type) (translate portName em.type) .default
    unless source matches .thmInfo _ do throw <| IO.userError s!"expected official theorem {name}"
    unless source.levelParams.isEmpty && proof.levelParams.isEmpty && em.levelParams.isEmpty &&
        official.getModuleIdxFor? name == official.getModuleIdx? owner &&
        env.getModuleIdxFor? witness == env.getModuleIdx? proofModule &&
        Kernel.isDefEqGuarded env {} proof.type expected do
      throw <| IO.userError s!"incorrect strict implication for {owner}/{name}"
  let count ← OmegaChecks.InitPort.replayStrict env.toKernelEnv (implications.map Prod.snd)
  let rows := implications.map fun (name, witness) => #[owner.toString, name.toString, target.toString, witness.toString]
  IO.FS.writeFile output (toJson rows).compress
  IO.println s!"Replayed {rows.size} strict longest-match implications of excluded middle with {count} declarations and zero axioms."
