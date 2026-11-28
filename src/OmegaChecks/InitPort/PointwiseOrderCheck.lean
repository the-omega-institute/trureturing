module
import all OmegaChecks.InitInventory.OriginalType
import OmegaChecks.InitPort.StrictReplay
import OmegaChecks.InitPort.PublicTypeClient
meta import OmegaChecks.InitPort.PublicTypeClient
meta import OmegaChecks.InitPort.StrictReplay
meta import OmegaChecks.InitInventory.OriginalType

open Lean InitKernelPort OmegaChecks.InitPort OmegaChecks.InitInventory

private def reverseRelations (type : Expr) : Expr :=
  type.replace fun e => do
    guard (e.isAppOfArity `Lean.Order.PartialOrder.rel 4)
    let args := e.getAppArgs
    return mkAppN e.getAppFn ((args.set! 2 args[3]!).set! 3 args[2]!)

public unsafe def main (args : List String) : IO Unit := do
  let [lib, mod, dir] := args | throw <| IO.userError "expected a strict library, owner and client directory"
  initSearchPath (← findSysroot)
  let owner := mod.toName
  unless [`Init.Internal.Order.Basic, `Init.Internal.Order.Lemmas, `Init.Internal.Order.MonadTail].contains owner do
    throw <| IO.userError s!"unexpected pointwise order module {owner}"
  let orders := [`Lean.Order.instOrderPi, `Lean.Order.instPartialOrderReaderT,
    `Lean.Order.instPartialOrderStateT, `Lean.Order.instPartialOrderStateRefT']
  let strictOwner := owner.replacePrefix `Init `OmegaInit
  let visible ← importModules #[{module := owner}] {} (level := .exported)
  let official ← importModules #[{module := owner, importAll := true}] {}
  searchPathRef.set [lib]
  let strict ← importModules #[{module := strictOwner}] {} (level := .exported)
  let full ← importModules #[{module := strictOwner, importAll := true}] {}
  let mut roots := #[]
  let mut clients := #[]
  for mod in [owner, strictOwner] do
    let header := s!"module\nprelude\nimport {mod}\nset_option autoImplicit false\nset_option linter.unusedVariables false\n"
    clients := clients ++ #[header, header]
  let idx := (visible.getModuleIdx? owner).get!
  for name in visible.header.moduleData[idx.toNat]!.constNames do
    if isPrivateName name || name.isInternalOrNum || name.hasMacroScopes then continue
    let some src := official.find? name | continue
    let some dst := strict.find? (portName name) | continue
    unless src.isTheorem && !src.isUnsafe && !src.isPartial && src.numLevelParams == dst.numLevelParams &&
        strict.getModuleIdxFor? dst.name == strict.getModuleIdx? strictOwner do continue
    let pinned := src.type.instantiateLevelParams src.levelParams (dst.levelParams.map Level.param)
    let missing := (translate portName pinned).getUsedConstants.filter fun d => !strict.contains d
    unless missing.size == 1 && orders.contains (originalName missing[0]!) &&
        checkedOrderFields visible strict owner src pinned dst.type missing do continue
    -- Use the entire exported proposition as a common formula in the two ordinary imports.
    let common := translate originalName dst.type
    let lifted := translate portName common
    unless (Kernel.check visible {} common).isOk && Kernel.isDefEqGuarded visible {} common pinned &&
        (Kernel.check strict {} lifted).isOk && Kernel.isDefEqGuarded strict {} lifted dst.type do continue
    let reverse := reverseRelations common
    unless (Kernel.check visible {} reverse).isOk && !Kernel.isDefEqGuarded visible {} common reverse do
      throw <| IO.userError s!"reversing the comparison does not distinguish {name}"
    roots := roots.push dst.name
    let statements := #[(common, name), (reverse, name), (lifted, dst.name), (translate portName reverse, dst.name)]
    for (typ, term) in statements, i in [:4] do
      clients := clients.modify i (· ++ PublicTypeClient.client typ term dst.levelParams)
  let _ ← replayStrict full.toKernelEnv roots
  for body in clients, filename in ["Official", "OfficialReversed", "Strict", "StrictReversed"] do
    IO.FS.writeFile (System.FilePath.mk dir / (filename ++ ".lean")) body
  for n in roots do IO.println (toJson #[owner.toString, (originalName n).toString]).compress
