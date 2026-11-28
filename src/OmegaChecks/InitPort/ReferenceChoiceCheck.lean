module
meta import OmegaChecks.InitPort.StrictReplay
import OmegaChecks.InitPort.StrictReplay
meta import OmegaChecks.InitPort.Translation
meta import OmegaChecks.InitInventory.ReferenceSelection
import OmegaChecks.InitPort.Translation
import all OmegaChecks.InitInventory.ReferenceSelection

open Lean InitKernelPort OmegaChecks.InitBoundaries

/-- Reuse each official read specialization but return a selector using the actual strict allocation. -/
public def main (args : List String) : IO Unit := do
  let lib :: evidence :: output :: owners := args | throw <| IO.userError "expected strict library, strict proof module, output, and owners"
  let official ← importModules #[{module := `OmegaChecks.InitInventory.ReferenceSelection, importAll := true},
    {module := `Init.Internal.Order.MonadTail, importAll := true}] {} (level := .private)
  let owners := owners.toArray.map String.toName
  searchPathRef.set [evidence, lib]
  let evidenceModule := if owners.contains `OmegaInit.System.Promise then `StrictPromiseChoice else `StrictReferenceChoice
  let env ← importModules (#[{module := evidenceModule : Import}] ++ (owners.map fun n => {module := n})) {}
    (level := .private)
  let mut kernelEnv := env.toKernelEnv
  let target := mkConst `OmegaStrictReference.Choice
  let some choice := official.find? ``Classical.choice | throw <| IO.userError "missing pinned choice axiom"
  unless choice.isAxiom && choice.levelParams.length == 1 &&
      Kernel.isDefEqGuarded env {} target (translate portName (choice.type.instantiateLevelParams choice.levelParams [.succ .zero])) do
    throw <| IO.userError "incorrect universe or type for strict small selection"
  let some common := official.find? ``ReferenceSelection.choiceUsing | throw <| IO.userError "missing abstract constructor proof"
  let some generic := common.value? | throw <| IO.userError "missing constructor proof body"
  let actual := mkApp2 (translate portName generic) (mkConst `Omega.Void.mk) (mkConst `Omega.ST.Prim.mkRef)
  unless Kernel.isDefEqGuarded env {} actual (mkConst `OmegaStrictReference.selector) do
    throw <| IO.userError "the strict selector differs from the construction for arbitrary official constructors"
  unless [`Omega.Void.mk, `Omega.ST.Prim.mkRef].all (fun n => env.getModuleIdxFor? n == env.getModuleIdx? `OmegaInit.System.ST) do
    throw <| IO.userError "strict constructors must belong to OmegaInit.System.ST"
  let mut checked : Array (String × String × String) := #[]
  for (owner, name, witness) in ReferenceSelection.witnesses do
    if name == `IO.Promise.result! then continue
    unless owners.contains (owner.replacePrefix `Init `OmegaInit) do continue
    let some ci := official.find? name | throw <| IO.userError s!"missing official {name}"
    let some proof := official.find? witness | throw <| IO.userError s!"missing read specialization {witness}"
    let some (.lam arg input (.app head read) bi) := proof.value? (allowOpaque := true)
      | throw <| IO.userError s!"unexpected read specialization at {witness}"
    unless head.constName?.map privateToUserName == some `OmegaChecks.InitBoundaries.ReferenceSelection.fromRead &&
        official.getModuleIdxFor? name == official.getModuleIdx? owner &&
        ci.levelParams.isEmpty && Kernel.isDefEqGuarded official {} input ci.type do
      throw <| IO.userError s!"incorrect official argument of {witness}"
    if [`ST.Prim.Ref.take, `ST.Ref.take, `ST.Prim.Ref.modifyGetUnsafe].contains name then
      let some original := ci.value? (allowOpaque := true) | throw <| IO.userError s!"missing body of {name}"
      let some (.opaqueInfo take) := official.find? `ST.Prim.Ref.take | throw <| IO.userError "missing pinned take"
      unless take.isUnsafe && getExternNameFor official `c take.name == some "lean_st_ref_take" do
        throw <| IO.userError "unexpected pinned reference take"
      -- Open the private logical implementation of the primitive, keeping the put opaque.
      let readBody := (read.instantiate1 original).replace fun t => if t.isConstOf take.name then some take.value else none
      let selected := mkApp3 generic (mkConst `Void.mk) (mkConst `ST.Prim.mkRef) readBody
      unless Kernel.isDefEqGuarded official {} selected (mkConst `Classical.choice [.succ .zero]) do
        throw <| IO.userError s!"the logical implementation of {name} differs from the pinned choice"
    let type := translate portName ci.type
    let argument := translate portName read
    if (type.getUsedConstants ++ argument.getUsedConstants).any (!env.contains ·) then continue
    let n := `OmegaStrictReference ++ name
    let decl := Declaration.defnDecl {
      name := n
      levelParams := []
      type := .forallE arg type target bi
      value := .lam arg type (mkApp (mkConst `OmegaStrictReference.selector) argument) bi
      safety := .safe
      hints := .opaque }
    let .ok next := kernelEnv.addDeclCore 0 1000 decl none | throw <| IO.userError s!"invalid strict selection from {name}"
    kernelEnv := next
    checked := checked.push (owner.toString, name.toString, n.toString)
  for (owner, name) in [(`Init.System.Promise, `IO.Promise.result!),
      (`Init.Internal.Order.Basic, `Lean.Order.EST.bot),
      (`Init.Internal.Order.MonadTail, `Lean.Order.ST.bot')] do
    unless owners.contains (owner.replacePrefix `Init `OmegaInit) do continue
    let n := `OmegaStrictReference ++ name
    let some source := official.find? name | throw <| IO.userError s!"missing official {name}"
    let some witness := env.find? n | throw <| IO.userError s!"missing strict selection witness {n}"
    let .forallE _ input output _ := witness.type | throw <| IO.userError s!"incorrect witness type for {n}"
    -- Unfolding the official flat carrier removes its unused choice-dependent point index.
    let sourceInput := translate (fun k => k.replacePrefix `Omega .anonymous) input
    unless source.levelParams.isEmpty && official.getModuleIdxFor? name == official.getModuleIdx? owner &&
        Kernel.isDefEqGuarded official {} source.type sourceInput &&
        Kernel.isDefEqGuarded env {} input (translate portName sourceInput) &&
        Kernel.isDefEqGuarded env {} target output do
      throw <| IO.userError s!"incorrect strict state selection from {name}"
    checked := checked.push (owner.toString, name.toString, n.toString)
  let _ ← OmegaChecks.InitPort.replayStrict kernelEnv (checked.map fun (_, _, witness) => witness.toName)
  IO.FS.writeFile output (toJson (checked.map fun (owner, name, proof) => #[owner, name, proof])).compress
  IO.println s!"Replayed {checked.size} strict reference and state interfaces implying explicit selection on Type with zero axioms."
