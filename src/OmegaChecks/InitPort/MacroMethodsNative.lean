module
import Lean
import all Lean.Environment
import all Lean.OriginalConstKind
import Lean.Compiler.LCNF.EmitC
import OmegaChecks.InitPort.NativeState
import OmegaChecks.InitPort.Translation
meta import OmegaChecks.InitPort.Translation
meta import OmegaChecks.InitPort.NativeState

open Lean Compiler.LCNF OmegaChecks.InitPort

namespace MacroMethodsNative

private unsafe def readTable (ctx : Lean.Macro.Context) (s : Lean.Macro.State) :
    EStateM.Result Lean.Macro.Exception Lean.Macro.State Lean.Macro.Methods :=
  .ok (unsafeCast ctx.methods) s

private def readerCode := mkPrivateNameCore `OmegaChecks.InitPort.MacroMethodsNative `MacroMethodsNative.readTable

private def operations := #[(`Lean.Macro.mkMethods, `Lean.Macro.mkMethodsImp, `Lean.Macro.mkMethodsImp),
  (`Lean.Macro.mkMethodsImp, `Lean.Macro.mkMethodsImp, `Lean.Macro.mkMethodsImp),
  (`Lean.Macro.getMethods, `Lean.Macro.getMethodsImp, readerCode),
  (`Lean.Macro.getMethodsImp, `Lean.Macro.getMethodsImp, readerCode)]

/-- Compile the verified runtime bodies in a transient compiler environment. Only the compiler
extensions are written back to the already checked opaque declarations. -/
public unsafe def main (args : List String) : IO Unit := do
  let [lib, output] := args | throw <| IO.userError "expected strict library and C output"
  let owner := `OmegaInit.Prelude
  let source ← importModules #[{module := `Init.Prelude, importAll := true}, {module := `OmegaChecks.InitPort.MacroMethodsNative, importAll := true}] {} (level := .private)
  searchPathRef.set [lib]
  let strict ← importModules #[{module := owner, importAll := true}] {} (level := .private)
  let api := `Omega.Lean.Macro.mkMethods
  unless strict.contains api do return
  let some castImpl := source.find? `unsafeCast | throw <| IO.userError "missing the pinned compiler cast"
  let mut kernel := strict.toKernelEnv
  kernel := {kernel with constants := kernel.constants.insert castImpl.name castImpl}
  let rename := fun n => if n == `unsafeCast then n else InitKernelPort.portName n
  let point := `Lean.Macro.MethodsRefPointed
  let some (.opaqueInfo carrier) := source.find? point | throw <| IO.userError "missing the pinned method reference carrier"
  let originalCarrier : ConstantInfo := .opaqueInfo {carrier with
    name := rename point
    type := InitKernelPort.translate rename carrier.type
    value := InitKernelPort.translate rename carrier.value
    all := [rename point]}
  kernel := {kernel with constants := {kernel.constants with map₁ := kernel.constants.map₁.insert (rename point) originalCarrier, map₂ := kernel.constants.map₂.erase (rename point)}}
  let mut targets := #[]
  for (name, impl, code) in operations do
    let target := rename name
    let some entry := strict.find? target | continue
    let logical := if name == `Lean.Macro.getMethodsImp then `Lean.Macro.getMethods
      else if name == `Lean.Macro.mkMethodsImp then `Lean.Macro.mkMethods else name
    if name == impl then
      let some (.defnInfo alias) := strict.find? target | throw <| IO.userError s!"missing strict alias {target}"
      unless alias.safety == .unsafe && alias.value == mkConst (rename logical) do
        throw <| IO.userError s!"incorrect strict body for {target}"
    else
      unless entry matches .opaqueInfo _ do throw <| IO.userError s!"expected opaque {target}"
    let some (.defnInfo pinned) := source.find? impl | throw <| IO.userError s!"missing {impl}"
    let some template := source.find? code >>= (·.value?) | throw <| IO.userError s!"missing {code}"
    unless Compiler.getImplementedBy? source logical == some impl && pinned.safety == .unsafe &&
        Kernel.isDefEqGuarded source {} pinned.value template && entry.isUnsafe == (name == impl) do
      throw <| IO.userError s!"incorrect runtime implementation of {name}"
    let entry : DefinitionVal := {pinned with
      name := target
      type := entry.type
      value := InitKernelPort.translate rename template
      all := [target]}
    let executable := ConstantInfo.defnInfo entry
    kernel := {kernel with constants := {kernel.constants with map₁ := kernel.constants.map₁.insert target executable, map₂ := kernel.constants.map₂.erase target}}
    targets := targets.push target
  if targets.isEmpty then return
  let context ← NativeState.localEnv (Environment.ofKernelEnv kernel) owner targets
  let mut context := context
  for ext in [baseExt, monoExt] do
    let some decl := getDeclCore? source ext `unsafeCast | throw <| IO.userError "missing the compiler representation cast"
    context := ext.addEntry context decl
    context := setDeclTransparent context (if ext.name == baseExt.name then .base else .mono) `unsafeCast
  let some castSig := getSigCore? source impureSigExt `unsafeCast | throw <| IO.userError "missing the compiler cast signature"
  context := impureSigExt.addEntry context castSig
  let compiled ← NativeState.compile context do
    for target in targets do
      modifyEnv fun e => setDeclPublic (privateConstKindsExt.insert e target .defn) target
      (← compileDeclsRef.get) #[target] {}
  for (name, impl, _) in operations do
    let target := rename name
    unless targets.contains target do continue
    let some (.fdecl _ a r b i) := IR.findEnvDecl source impl | throw <| IO.userError s!"missing official code {impl}"
    let some (.fdecl _ a' r' b' i') := IR.findEnvDecl compiled target | throw <| IO.userError s!"missing code {target}"
    let sameABI := a.map (fun p => (p.ty, p.borrow)) == a'.map (fun p => (p.ty, p.borrow)) && r == r'
    let expected := if impl == `Lean.Macro.mkMethodsImp then
      match a, b, a', b' with
      | #[p], .inc x 1 _ false (.ret (.var y)), #[q], .inc u 1 _ false (.ret (.var v)) =>
        x == p.x && y == x && u == q.x && v == u
      | _, _, _, _ => false
    else
      let observe (args : Array IR.Param) (body : IR.FnBody) (resultName : Name) := Id.run do
        let #[ctx, state] := args | return false
        let .vdecl field .tobject (.proj 0 fromCtx) (.inc kept 1 true false
          (.vdecl out .object (.ctor ctor #[.var value, .var finalState]) (.ret (.var returned)))) := body | return false
        return ctx.x == fromCtx && field == kept && field == value && state.x == finalState && out == returned &&
          ctor.name == resultName && ctor.cidx == 0 && ctor.size == 2 && ctor.usize == 0 && ctor.ssize == 0
      observe a b `EStateM.Result.ok && observe a' b' (rename `EStateM.Result.ok)
    unless sameABI && i.sorryDep?.isNone && i'.sorryDep?.isNone && expected do
      throw <| IO.userError s!"incorrect compiled calling convention or table operation {target}"
  let compiled := baseExt.modifyState compiled (·.erase `unsafeCast)
  let compiled := monoExt.modifyState compiled (·.erase `unsafeCast)
  let compiled := impureSigExt.modifyState compiled (·.erase `unsafeCast)
  NativeState.writeCode lib owner compiled (NativeState.codeExtensions ++ #[privateConstKindsExt.name])
  NativeState.emitBridge compiled owner none output

end MacroMethodsNative

public unsafe def main := MacroMethodsNative.main
