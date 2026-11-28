module
public import Lean
import all Lean.Compiler.LCNF.ToImpureType
import all Lean.Compiler.LCNF.MonoTypes

/-! Build-time elaboration of the pinned Init inductives in strict prelude modules. -/

open Lean Parser Elab Command
namespace OmegaChecks.InitCompiler

open Compiler.LCNF

/-- Keep the UTF-8 field in slot zero and preserve the boxed calling convention of String. -/
public def prepareStringLayout : CoreM Unit := do
  modifyEnv fun env =>
    let env := trivialStructureInfoExt.insert env `Omega.String none
    let env := impureTrivialStructureInfoExt.insert env `Omega.String none
    impureTypeExt.insert env `Omega.String ImpureType.tobject

public def finishStringLayout : CoreM Unit := do
  let name := `Omega.String.ofByteArray
  let some layout := ctorLayoutExt.find? (← getEnv) name | throwError "missing string constructor"
  unless layout.ctorInfo.size == 1 && layout.ctorInfo.ssize == 0 && layout.ctorInfo.usize == 0 &&
      layout.ctorInfo.cidx == 0 && (layout.fieldInfo matches #[.object 0 _, .erased]) do
    throwError s!"unexpected string constructor layout {layout.ctorInfo.size} {layout.ctorInfo.ssize} {layout.ctorInfo.usize} {layout.fieldInfo.map (fun f => toString (format f))}"
  modifyEnv fun env => ctorLayoutExt.insert env name {layout with ctorInfo := {layout.ctorInfo with ssize := 1}}

public def compilerLayouts (types ctors : Array Name) : CoreM Unit := do
  let layoutEnv ← withoutModifyingEnv do
    -- The compiler queries the erased type markers when computing constructor layouts.
    -- Their bodies and declarations are local to this compiler calculation.
    for n in [`lcAny, `lcErased, `lcVoid] do
      unless (← getEnv).contains n do
        Lean.addDecl (.opaqueDecl {name := n, levelParams := [], type := .sort (.succ .zero), value := .sort .zero, isUnsafe := false})
    if types == #[`Omega.ByteArray] then
      modifyEnv fun env =>
        let env := trivialStructureInfoExt.insert env `Omega.ByteArray none
        let env := impureTrivialStructureInfoExt.insert env `Omega.ByteArray none
        impureTypeExt.insert env `Omega.ByteArray ImpureType.tobject
    if types == #[`Omega.String] then prepareStringLayout
    compileInductives types
    if types == #[`Omega.String] then finishStringLayout
    if types == #[`Omega.ByteArray] then
      let name := `Omega.ByteArray.mk
      let some l := ctorLayoutExt.find? (← getEnv) name | throwError "missing strict byte array constructor"
      unless l.ctorInfo.size == 1 && l.ctorInfo.usize == 0 && l.ctorInfo.ssize == 0 &&
          l.ctorInfo.cidx == 0 && (l.fieldInfo matches #[.object 0 _]) do
        throwError "unexpected strict byte array constructor layout"
      modifyEnv (ctorLayoutExt.insert · name {l with ctorInfo := {l.ctorInfo with usize := 2, ssize := 1}})
    return ← getEnv
  for n in types do
    copyEntry trivialStructureInfoExt layoutEnv n
    copyEntry impureTrivialStructureInfoExt layoutEnv n
    copyEntry impureTypeExt layoutEnv n
  for n in types ++ ctors do copyEntry monoTypeExt layoutEnv n
  for n in ctors do copyEntry ctorLayoutExt layoutEnv n
where
  copyEntry {α : Type} [Inhabited α] (ext : MapDeclarationExtension α) (layoutEnv : Environment) (n : Name) : CoreM Unit := do
    let some info := ext.find? layoutEnv n | throwError "missing compiler layout for {n}"
    modifyEnv (ext.insert · n info)

end OmegaChecks.InitCompiler
