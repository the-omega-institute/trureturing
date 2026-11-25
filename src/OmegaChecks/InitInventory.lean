import Lean

/-!
Inventory of named public declarations in every installed module of the pinned `Init` library,
including modules importable separately from its umbrella. Constructors, recursors and other
named generated declarations are included. If several modules emit the same generated name,
the row uses the owner selected by the combined public environment. The inventory omits syntax,
aliases and private or internal names. Each row gives the original implementation's transitive
axioms and the defining module, if any, of its strict `Omega.` counterpart. The strict library
audit checks the corresponding types, implementations and strict axiom closures.

Run from the project root after building the strict basis.
`lean --run src/OmegaChecks/InitInventory.lean .lake/build/omega-strict/lib/lean output.json`.
-/

open Lean

/- Each reduction accepts an implementation of precisely the pinned public type.
Its result implements the named axiom. Both types are elaborated without
referring to the values of the upstream constants. -/
namespace OmegaChecks.InitBoundaries
universe u

def choiceFromChoose (select : type_of% (@Classical.choose.{u})) : type_of% (@Classical.choice.{u}) :=
  fun {α} inhabited => @select α (fun _ => True) (inhabited.elim fun x => ⟨x, trivial⟩)

def choiceFromExistsChoose (select : type_of% (@Exists.choose.{u})) : type_of% (@Classical.choice.{u}) :=
  choiceFromChoose (@select)

def choiceFromEpsilon (select : type_of% (@Classical.epsilon.{u})) : type_of% (@Classical.choice.{u}) :=
  fun {α} inhabited => @select α inhabited (fun _ => True)

def choiceFromDescription (select : type_of% (@Classical.indefiniteDescription.{u})) :
    type_of% (@Classical.choice.{u}) :=
  fun {α} inhabited => (@select α (fun _ => True) (inhabited.elim fun x => ⟨x, trivial⟩)).val

def choiceFromInhabited (select : type_of% (@Classical.inhabited_of_nonempty.{u})) :
    type_of% (@Classical.choice.{u}) :=
  fun {α} inhabited => (@select α inhabited).default

theorem propextFromIffIffEq (equiv : type_of% (@iff_iff_eq)) : type_of% (@propext) :=
  fun {a b} h => (@equiv a b).mp h

theorem propextFromEqIffIff (equiv : type_of% (@eq_iff_iff)) : type_of% (@propext) :=
  fun {a b} h => (@equiv a b).mpr h

theorem propextFromPropIntro (intro : type_of% (@Eq.propIntro)) : type_of% (@propext) :=
  fun {a b} h => @intro a b h.mp h.mpr


def reductions : List (Name × Name × Name) := [
  (`Classical.choose, `Classical.choice, ``choiceFromChoose),
  (`Exists.choose, `Classical.choice, ``choiceFromExistsChoose),
  (`Classical.epsilon, `Classical.choice, ``choiceFromEpsilon),
  (`Classical.indefiniteDescription, `Classical.choice, ``choiceFromDescription),
  (`Classical.inhabited_of_nonempty, `Classical.choice, ``choiceFromInhabited),
  (`iff_iff_eq, `propext, ``propextFromIffIffEq),
  (`eq_iff_iff, `propext, ``propextFromEqIffIff),
  (`Eq.propIntro, `propext, ``propextFromPropIntro)]

run_cmd
  let env ← getEnv
  for (name, axiomName, witness) in reductions do
    let proof ← getConstInfo witness
    let source ← getConstInfo name
    let target ← getConstInfo axiomName
    let levels := proof.levelParams.map Level.param
    let expected := Expr.forallE .anonymous (source.type.instantiateLevelParams source.levelParams levels)
      (target.type.instantiateLevelParams target.levelParams levels) .default
    unless target.isAxiom && source.numLevelParams == levels.length && target.numLevelParams == levels.length &&
        Kernel.isDefEqGuarded env {} proof.type expected && (← collectAxioms witness).isEmpty do
      throwError "invalid axiom reduction for {name}"

end OmegaChecks.InitBoundaries

private def installedModules (dir : System.FilePath) (root : Name) : IO (Array Name) := do
  let mut modules := if ← (modToFilePath dir root "olean").pathExists then #[root] else #[]
  for file in ← (dir / root.toString).walkDir do
    if file.extension == some "olean" then
      modules := modules.push (← moduleNameOfFileName file dir)
  return modules.qsort Name.lt

private def declarationKind : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "definition"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotientPrimitive"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

private def inventory (visible strict : Environment) (modules : Array Name)
    (gaps : Option IO.FS.Handle) : CoreM Json := do
  let official ← getEnv
  let boundaries : NameMap Name := OmegaChecks.InitBoundaries.reductions.foldl
    (init := {}) fun acc (name, target, _) => acc.insert name target
  let mut rows := #[]
  let mut matchingNames := 0
  let mut directAxioms := 0
  let mut withAxioms := 0
  if let some file := gaps then
    file.putStrLn "module\tdeclaration\tkind\tunsafe\tpartial\tupstreamAxioms\timpliesAxiom"
  for owner in modules do
    let some idx := visible.getModuleIdx? owner | throwError "missing official module {owner}"
    for name in visible.header.moduleData[idx]!.constNames.qsort Name.lt do
      if isPrivateName name || name.isInternalOrNum || name.hasMacroScopes then continue
      if visible.getModuleIdxFor? name != some idx then continue
      let some info := official.find? name | throwError "missing official declaration {name}"
      let axioms ← collectAxioms name
      let strictName := `Omega ++ name
      let strictOwner := (strict.getModuleIdxFor? strictName).map (strict.header.moduleNames[·]!)
      let matched := strictOwner == some (owner.replacePrefix `Init `OmegaInit)
      if matched then matchingNames := matchingNames + 1
      if !matched && !info.isAxiom then
        if let some file := gaps then
          file.putStrLn <| String.intercalate "\t" [owner.toString, name.toString,
            declarationKind info, toString info.isUnsafe, toString info.isPartial,
            String.intercalate "," (axioms.toList.map Name.toString),
            ((boundaries.get? name).map Name.toString).getD ""]
      if info.isAxiom then directAxioms := directAxioms + 1
      if !axioms.isEmpty then withAxioms := withAxioms + 1
      rows := rows.push <| Json.mkObj [
        ("name", toJson name.toString), ("module", toJson owner.toString),
        ("kind", toJson (declarationKind info)), ("unsafe", toJson info.isUnsafe), ("partial", toJson info.isPartial),
        ("matchingNameAndModule", toJson matched),
        ("axioms", toJson (axioms.map Name.toString)),
        ("impliesAxiom", toJson ((boundaries.get? name).map Name.toString)),
        ("strictModule", toJson (strictOwner.map Name.toString))]
  let summary := Json.mkObj [("declarations", toJson rows.size), ("directAxioms", toJson directAxioms),
    ("withAxioms", toJson withAxioms), ("matchingNameAndModule", toJson matchingNames)]
  return Json.mkObj [("leanVersion", toJson Lean.versionString), ("leanCommit", toJson Lean.githash),
    ("modules", toJson (modules.map Name.toString)), ("summary", summary), ("declarations", .arr rows)]

def main (args : List String) : IO Unit := do
  let strictDir :: outputPath :: rest := args | throw <| IO.userError "expected strict olean directory and output file"
  let gaps ← match rest with
    | [] => pure none
    | [path] =>
      if path == outputPath then throw <| IO.userError "inventory and gaps require distinct files"
      pure (some (← IO.FS.Handle.mk path .write))
    | _ => throw <| IO.userError "expected at most one gaps TSV file"
  let sysroot ← findSysroot
  let lib ← getLibDir sysroot
  searchPathRef.set [lib]
  let modules ← installedModules lib `Init
  let imports := modules.map fun mod => {module := mod : Import}
  let visible ← importModules imports {} (level := .exported)
  -- The public environment can replace a hidden body with an axiom-shaped entry.
  -- Use the private artifact for the original declaration kind and axiom dependencies.
  -- Load Lean's exported-axiom extension from the pinned toolchain so every query
  -- can use the dependency closure recorded by Lean when the module was compiled.
  unsafe enableInitializersExecution
  let official ← importModules imports {} (loadExts := true)
  searchPathRef.set [strictDir]
  let basis ← installedModules strictDir `OmegaInit
  let strict ← importModules (basis.map fun mod => {module := mod}) {} (level := .exported)
  for owner in strict.allImportedModuleNames do
    unless owner.getRoot == `OmegaInit do
      throw <| IO.userError s!"expected a strict OmegaInit build, found import {owner}"
  let result ← (inventory visible strict modules gaps).toIO' {fileName := "<Init inventory>", fileMap := default} {env := official}
  IO.FS.writeFile outputPath (result.compress ++ "\n")
  IO.println (← IO.ofExcept (result.getObjVal? "summary")).compress
