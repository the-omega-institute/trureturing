module
public import Lean
import all Lean.Util.CollectAxioms

public section

/-!
Inventory of named public declarations in every installed module of the pinned `Init` library,
including modules importable separately from its umbrella. Constructors, recursors and other
named generated declarations are included. Each defining module has its own row for a shared name. The inventory omits syntax,
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

/-- The pinned Lean evaluator can calculate these on closed natural numbers
even when the public constant has no definition body (notably Nat.gcd). -/
private def officialReduction (env : Environment) (n : Name) : Option String := do
  let info ← env.find? n
  if #[`Nat.succ, `Nat.add, `Nat.sub, `Nat.mul, `Nat.div, `Nat.mod, `Nat.pow, `Nat.gcd,
       `Nat.beq, `Nat.ble, `Nat.land, `Nat.lor, `Nat.xor, `Nat.shiftLeft, `Nat.shiftRight].contains n then
    return "builtin natural-number reduction"
  match info with
  | .defnInfo _ => return "public definition body"
  | .recInfo _ => return "recursor computation rule"
  | .ctorInfo _ => return "constructor computation rule"
  | .inductInfo _ => return "primitive inductive type"
  | _ => none

/-- One shortest implementation-body path to a sealed strict implementation
whose official counterpart has a public computation rule or inductive interface. -/
private def reductionPaths (official strict full : Environment) : NameMap (List Name × String) := Id.run do
  let mut users : NameMap (Array Name) := {}
  let mut paths : NameMap (List Name × String) := {}
  let mut todo := #[]
  for (n, info) in full.constants.toList do
    let some value := info.value? (allowOpaque := true) | continue
    if !(strict.find? n).any (· matches .defnInfo _) then
      if let some rule := officialReduction official (n.replacePrefix `Omega .anonymous) then
        paths := paths.insert n ([n], rule)
        todo := todo.push n
    if info matches .defnInfo _ | .opaqueInfo _ then
      for dep in value.getUsedConstantsAsSet do
        users := users.insert dep ((users.getD dep #[]).push n)
  todo := todo.qsort Name.lt
  let mut i := 0
  while h : i < todo.size do
    let dependency := todo[i]
    i := i + 1
    let some (path, rule) := paths.get? dependency | continue
    for n in (users.getD dependency #[]).qsort Name.lt do
      unless paths.contains n do
        paths := paths.insert n (n :: path, rule)
        todo := todo.push n
  return paths

private def inventory (lib : System.FilePath) (visible strict full : Environment) (modules : Array Name)
    (gaps : Option IO.FS.Handle) : CoreM Json := do
  let official ← getEnv
  let reductions := reductionPaths visible strict full
  let boundaries : NameMap Name := OmegaChecks.InitBoundaries.reductions.foldl
    (init := {}) fun acc (name, target, _) => acc.insert name target
  let mut names : NameSet := {}
  let mut duplicateNames : NameSet := {}
  let publicName := fun (n : Name) => !isPrivateName n && !n.isInternalOrNum && !n.hasMacroScopes
  for data in visible.header.moduleData do
    for n in data.constNames do
      if publicName n then
        if names.contains n then duplicateNames := duplicateNames.insert n
        names := names.insert n
  let mut matchedUnique : NameSet := {}
  let mut axiomUnique : NameSet := {}
  let mut withAxiomsUnique : NameSet := {}
  let mut rows := #[]
  let mut matchingNames := 0
  let mut directAxioms := 0
  let mut withAxioms := 0
  if let some file := gaps then
    file.putStrLn "module\tdeclaration\tkind\tunsafe\tpartial\tupstreamAxioms\timpliesAxiom"
  for owner in modules do
    let some idx := visible.getModuleIdx? owner | throwError "missing official module {owner}"
    let publicNames := visible.header.moduleData[idx]!.constNames.filter publicName
    let some privateIdx := official.getModuleIdx? owner | throwError "missing private module {owner}"
    let infos ← if publicNames.any duplicateNames.contains then do
      -- Load this defining file directly. The combined environment may select a different
      -- module's declaration with the same name.
      let path := modToFilePath lib owner "olean"
      let parts ← readModuleDataParts #[path, path.addExtension "server", path.addExtension "private"]
      pure (parts.map (·.1))[2]!.constants
    else pure official.header.moduleData[privateIdx]!.constants
    let localDecls : NameMap ConstantInfo := infos.foldl (fun m c => m.insert c.name c) {}
    let localAxioms := exportedAxiomsExt.getModuleEntries official privateIdx
    let expected := owner.replacePrefix `Init `OmegaInit
    let strictNames := (strict.getModuleIdx? expected).map fun i =>
      NameSet.ofList strict.header.moduleData[i]!.constNames.toList
    for name in publicNames.qsort Name.lt do
      let some info := localDecls.find? name | throwError "missing declaration {owner}/{name}"
      let some (_, axioms) := localAxioms.binSearch (name, #[]) (fun a b => Name.quickLt a.1 b.1)
        | throwError "missing official axiom closure for {owner}/{name}"
      let strictName := `Omega ++ name
      let matched := strictNames.any (·.contains strictName)
      let strictOwner := if matched then some expected else none
      if matched then
        matchingNames := matchingNames + 1
        matchedUnique := matchedUnique.insert name
      if !matched && !info.isAxiom then
        if let some file := gaps then
          file.putStrLn <| String.intercalate "\t" [owner.toString, name.toString,
            declarationKind info, toString info.isUnsafe, toString info.isPartial,
            String.intercalate "," (axioms.toList.map Name.toString),
            ((boundaries.get? name).map Name.toString).getD ""]
      if info.isAxiom then
        directAxioms := directAxioms + 1
        axiomUnique := axiomUnique.insert name
      if !axioms.isEmpty then
        withAxioms := withAxioms + 1
        withAxiomsUnique := withAxiomsUnique.insert name
      let reduction := if matched then reductions.get? strictName else none
      rows := rows.push <| Json.mkObj [
        ("name", toJson name.toString), ("module", toJson owner.toString),
        ("kind", toJson (declarationKind info)), ("unsafe", toJson info.isUnsafe), ("partial", toJson info.isPartial),
        ("matchingNameAndModule", toJson matched),
        ("publicReductionBoundary", toJson ((reduction.map Prod.fst).getD []).toArray),
        ("officialReductionMechanism", toJson (reduction.map Prod.snd)),
        ("axioms", toJson (axioms.map Name.toString)),
        ("impliesAxiom", toJson ((boundaries.get? name).map Name.toString)),
        ("strictModule", toJson (strictOwner.map Name.toString))]
  let summary := Json.mkObj [("declarations", toJson rows.size), ("directAxioms", toJson directAxioms),
    ("withAxioms", toJson withAxioms), ("matchingNameAndModule", toJson matchingNames)]
  let unique := Json.mkObj [("declarations",toJson names.size), ("directAxioms",toJson axiomUnique.size),
    ("withAxioms",toJson withAxiomsUnique.size), ("matchingNameAndModule",toJson matchedUnique.size)]
  return Json.mkObj [("schemaVersion", toJson 2), ("uniqueNames", unique), ("leanVersion", toJson Lean.versionString), ("leanCommit", toJson Lean.githash),
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
  let strictImports := basis.map fun mod => {module := mod : Import}
  let strict ← importModules strictImports {} (level := .exported)
  let full ← importModules strictImports {} (level := .private)
  for owner in strict.allImportedModuleNames do
    unless owner.getRoot == `OmegaInit do
      throw <| IO.userError s!"expected a strict OmegaInit build, found import {owner}"
  let result ← (inventory lib visible strict full modules gaps).toIO' {fileName := "<Init inventory>", fileMap := default} {env := official}
  IO.FS.writeFile outputPath (result.compress ++ "\n")
  IO.println (← IO.ofExcept (result.getObjVal? "summary")).compress
