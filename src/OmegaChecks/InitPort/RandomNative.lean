module
meta import OmegaChecks.InitPort.NativeState
import OmegaChecks.InitPort.NativeState
meta import OmegaChecks.InitPort.RandomState
import OmegaChecks.InitPort.RandomState
import all Lean.OriginalConstKind
import all Lean.Compiler.LCNF.ToImpureType

open Lean Compiler.LCNF OmegaChecks.InitPort.NativeState

private def checkGenerator (env : Environment) (name : Name) : IO Unit := do
  let some (.ctorInfo ctor) := env.find? name | throw <| IO.userError "missing StdGen constructor"
  let some fields := ctorLayoutExt.find? env name | throw <| IO.userError "missing StdGen native layout"
  let #[.object 0 _, .object 1 _] := fields.fieldInfo | throw <| IO.userError "unexpected StdGen fields"
  unless ctor.numFields == 2 && fields.ctorInfo.cidx == 0 && fields.ctorInfo.size == 2 &&
      fields.ctorInfo.usize == 0 && fields.ctorInfo.ssize == 0 do throw <| IO.userError "unexpected StdGen layout"

/-- Compile the strict global against the already initialized reference from the pinned runtime. -/
public unsafe def main (args : List String) : IO Unit := do
  let [lib, output] := args | throw <| IO.userError "expected strict library and C output"
  let official := OmegaChecks.InitPort.RandomState.owner
  let original ← importModules #[{module := official, importAll := true}] {}
  checkGenerator original `StdGen.mk
  unless (getRegularInitFnNameFor? original `IO.stdGenRef).isSome do throw <| IO.userError "missing generator initializer"
  searchPathRef.set [lib]
  let owner := `OmegaInit.Data.Random
  let imports := #[{module := owner, importAll := true : Import}]
  let env ← importModules imports {}
  let refName := `Omega.IO.stdGenRef
  unless env.contains refName do return
  if (env.find? `Omega.Nat).any (· matches .inductInfo _) then return
  checkNativeNat env
  let support := InitKernelPort.portName OmegaChecks.InitPort.RandomState.support
  let gen ← compileLayouts env `Omega.StdGen
  writeCode lib owner gen layouts
  let env ← importModules imports {}
  checkGenerator env `Omega.StdGen.mk
  let some (some layout) := impureTrivialStructureInfoExt.find? env `Omega.ST.Ref | throw <| IO.userError "missing reference layout"
  unless layout.numParams == 2 && layout.fieldIdx == 0 do throw <| IO.userError "unexpected default generator reference"
  let draw := `Omega.IO.rand
  let names := #[support, refName] ++ (if env.contains draw then #[draw] else #[])
  let ctx ← localEnv env owner names
  let compiled ← compile ctx do
    modifyEnv fun e => externAttr.ext.addEntry (asyncDecl := support) e (support, ⟨[.standard `all "omega_std_gen_ref"]⟩)
    (← compileDeclsRef.get) #[support] {}
    modifyEnv fun e => Lean.privateConstKindsExt.insert e refName .opaque
    (← compileDeclsRef.get) #[refName] {}
    if names.contains draw then
      modifyEnv fun e => externAttr.ext.addEntry (asyncDecl := draw) e (draw, ⟨[.standard `all "omega_io_rand"]⟩)
      (← compileDeclsRef.get) #[draw] {}
  verify compiled support #[(.tagged, false)] .tobject "omega_std_gen_ref"
  if names.contains draw then
    let some (.fdecl _ ps .tobject ..) := IR.findEnvDecl original `IO.rand | throw <| IO.userError "missing pinned random draw"
    unless ps.map (fun p => (p.ty, p.borrow)) == #[(.tobject, true), (.tobject, true), (.void, false)] do
      throw <| IO.userError "unexpected pinned random draw ABI"
    verify compiled draw #[(.tobject, false), (.tobject, false), (.tobject, false)] .object "omega_io_rand"
    let some out := ctorLayoutExt.find? env `Omega.ST.Out.mk | throw <| IO.userError "missing strict state layout"
    let #[.object 0 _, .object 1 _] := out.fieldInfo | throw <| IO.userError "incorrect strict state fields"
    unless out.ctorInfo.cidx == 0 && out.ctorInfo.size == 2 && out.ctorInfo.usize == 0 && out.ctorInfo.ssize == 0 do
      throw <| IO.userError "incorrect strict state result layout"
  unless (IR.findEnvDecl compiled refName).isSome do throw <| IO.userError "missing initialized strict generator"
  writeCode lib owner compiled (codeExtensions ++ #[Lean.privateConstKindsExt.name]) (NameSet.ofList [refName])
  emitBridge compiled owner (some "src/OmegaChecks/InitPort/random_runtime.h") output
  let standard := mkModuleInitializationFunctionName (phases := .runtime) official
    (original.getModuleIdx? official >>= original.getModulePackageByIdx?)
  let init := mkModuleInitializationFunctionName (phases := .runtime) owner compiled.getModulePackage?
  let signature := s!"LEAN_EXPORT lean_object* {init}(uint8_t builtin) \{"
  let code ← IO.FS.readFile output
  let [before, after] := code.splitOn signature | throw <| IO.userError "missing strict random module initializer"
  IO.FS.writeFile output (before ++ s!"extern lean_obj_res {standard}(uint8_t);\n" ++ signature ++
    s!"\nlean_obj_res source = {standard}(builtin);\nif (lean_io_result_is_error(source)) return source;\nlean_dec(source);\n" ++ after)
