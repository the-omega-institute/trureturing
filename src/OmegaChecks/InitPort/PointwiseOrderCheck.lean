module
import all OmegaChecks.InitInventory.OriginalType
import OmegaChecks.InitPort.StrictReplay
meta import OmegaChecks.InitPort.StrictReplay
meta import OmegaChecks.InitInventory.OriginalType

open Lean InitKernelPort OmegaChecks.InitPort OmegaChecks.InitInventory

/-- Render complete kernel applications and binders without typeclass search or implementation imports. -/
private partial def levelText : Level → String
  | .zero => "0"
  | .succ l => "(" ++ levelText l ++ " + 1)"
  | .max a b => "(max " ++ levelText a ++ " " ++ levelText b ++ ")"
  | .imax a b => "(imax " ++ levelText a ++ " " ++ levelText b ++ ")"
  | .param n => n.toString
  | _ => panic! "unexpected level"

private partial def source (e : Expr) (xs : List String := []) : String := Id.run do
  let var := "x" ++ toString xs.length
  let bind := fun (info : BinderInfo) (dom : Expr) =>
    let (l,r) := match info with
      | .implicit => ("{","}") | .strictImplicit => ("⦃","⦄")
      | .instImplicit => ("[","]") | _ => ("(",")")
    l ++ var ++ " : " ++ source dom xs ++ r
  match e with
  | .bvar i => return xs[i]!
  | .sort l => return "(Sort " ++ levelText l ++ ")"
  | .const n us =>
    return "@" ++ n.toString ++ (if us.isEmpty then "" else ".{" ++ String.intercalate ", " (us.map levelText) ++ "}")
  | .app _ _ => return "(" ++ String.intercalate " " ((source e.getAppFn xs) :: (e.getAppArgs.toList.map (source · xs))) ++ ")"
  | .forallE _ dom body bi => return "(∀ " ++ bind bi dom ++ ", " ++ source body (var::xs) ++ ")"
  | .lam _ dom body bi => return "(fun " ++ bind bi dom ++ " => " ++ source body (var::xs) ++ ")"
  | .letE _ dom value body _ => return "(let " ++ var ++ " : " ++ source dom xs ++ " := " ++ source value xs ++ "; " ++ source body (var::xs) ++ ")"
  | .mdata _ x => return source x xs
  | .proj _ i x => return "(" ++ source x xs ++ ")." ++ toString (i+1)
  | .lit (.natVal n) => return toString n
  | _ => panic! "unhandled kernel expression"

private def reverseRelations (type : Expr) : Expr :=
  type.replace fun e => do
    guard (e.isAppOfArity `Lean.Order.PartialOrder.rel 4)
    let args := e.getAppArgs
    return mkAppN e.getAppFn ((args.set! 2 args[3]!).set! 3 args[2]!)

private def client (typ : Expr) (n : Name) (universes : List Name) : String := Id.run do
  let decl := if universes.isEmpty then "" else "universe " ++ String.intercalate " " (universes.map Name.toString) ++ "\n"
  return "section\n" ++ decl ++ "example : " ++ source typ ++ " :=\n  " ++
    source (mkConst n (universes.map Level.param)) ++ "\nend\n"

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
      clients := clients.modify i (· ++ client typ term dst.levelParams)
  let _ ← replayStrict full.toKernelEnv roots
  for body in clients, filename in ["Official", "OfficialReversed", "Strict", "StrictReversed"] do
    IO.FS.writeFile (System.FilePath.mk dir / (filename ++ ".lean")) body
  for n in roots do IO.println (toJson #[owner.toString, (originalName n).toString]).compress
