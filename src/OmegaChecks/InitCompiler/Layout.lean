module
public import Lean
import all Lean.Compiler.LCNF.ToImpureType
import all Lean.Compiler.LCNF.MonoTypes

/-! Build-time elaboration of the pinned Init inductives in strict prelude modules. -/

open Lean Parser Elab Command
namespace OmegaChecks.InitCompiler

open Compiler.LCNF in
public def compilerLayouts (types ctors : Array Name) : CoreM Unit := do
  let layoutEnv ← withoutModifyingEnv do
    -- The compiler queries the erased type markers when computing constructor layouts.
    -- Their bodies and declarations are local to this compiler calculation.
    for n in [`lcAny, `lcErased, `lcVoid] do
      Lean.addDecl (.opaqueDecl {name := n, levelParams := [], type := .sort (.succ .zero), value := .sort .zero, isUnsafe := false})
    compileInductives types
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
