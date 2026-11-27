import Lean
import OmegaChecks.InitCompiler.Proofs
/-!
Find additional constructive proofs using the compiled strict basis. Rows give the pinned Init
owner, declaration, proof strategy and direct module dependencies. The ordinary source build
and interface audit determine whether a proposed addition is available to that module's consumers.

Run with the strict Lake environment after building the basis:
`lean --run src/OmegaChecks/InitCompiler/DiscoverProofs.lean STRICT_OLEAN_DIR OUTPUT.jsonl`.
-/

open Lean
namespace OmegaChecks.InitCompiler.DiscoverProofs

private def ownerOf (env : Environment) (name : Name) : Option Name := do
  return env.header.moduleNames[(← env.getModuleIdxFor? name)]!

structure Context where
  source : Environment
  visible : Environment
  output : IO.FS.Handle
  ambiguous : NameSet

structure State where
  kernel : Kernel.Environment
  failed : NameSet := {}

abbrev M := ReaderT Context (StateRefT State IO)

partial def visit (name : Name) : M Bool := do
  let dest := `Omega ++ name
  if (← get).kernel.find? dest |>.isSome then return true
  if (← get).failed.contains name then return false
  modify fun s => {s with failed := s.failed.insert name}
  let c ← read
  if c.ambiguous.contains name || name.isInternalOrNum || isPrivateName name || name.hasMacroScopes then return false
  let some (.thmInfo proof) := c.source.find? name | return false
  unless c.visible.contains name do return false
  let some owner := ownerOf c.source name | return false
  if owner.getRoot != `Init then return false
  for dep in proof.type.getUsedConstants do
    if !isPrivateName dep && !(← visit dep) then return false
  let .ok type := OmegaChecks.InitCompiler.translateProofTerm c.source proof.type | return false
  for dep in type.getUsedConstants do
    if !(← visit (dep.replacePrefix `Omega .anonymous)) then return false
  let checked := fun (value : Expr) => do
    let decl := Declaration.thmDecl {proof with name := dest, type, value, all := [dest]}
    let s ← get
    let initial ← IO.getNumHeartbeats
    let .ok next := s.kernel.addDeclCore (initial + 1000000).toUSize 1000 decl none | return false
    set {s with kernel := next}
    return true
  let (value, strategy) ← do
    if let some simple := OmegaChecks.InitCompiler.elementaryProof? (.ofKernelEnv (← get).kernel) type then
      if ← checked simple then pure (simple, "by_reflexivity")
      else return false
    else
      for dep in proof.value.getUsedConstants do
        if !isPrivateName dep && !(← visit dep) then return false
      let .ok value := OmegaChecks.InitCompiler.translateProofTerm c.source proof.value | return false
      for dep in value.getUsedConstants do
        if !(← visit (dep.replacePrefix `Omega .anonymous)) then return false
      if !(← checked value) then return false
      pure (value, "")
  let ownersOf := fun (xs : Array Name) =>
    (xs.filterMap (fun n => ownerOf c.source (n.replacePrefix `Omega .anonymous))).toList.eraseDups.toArray.map Name.toString
  c.output.putStrLn (Json.mkObj [("module", toJson owner.toString), ("name", toJson name.toString), ("strategy", toJson strategy),
    ("typeImports", toJson (ownersOf type.getUsedConstants)), ("proofImports", toJson (ownersOf value.getUsedConstants))]).compress
  return true

def run (seed out : System.FilePath) : IO Unit := do
  let lib ← getLibDir (← findSysroot)
  let modulesIn := fun (lib : System.FilePath) (root : Name) => do
    let mut mods := #[root]
    for f in ← (lib / root.toString).walkDir do
      if f.extension == some "olean" then mods := mods.push (← moduleNameOfFileName f lib)
    return mods.qsort Name.lt
  searchPathRef.set [lib]
  let modules ← modulesIn lib `Init
  let imports := modules.map fun n => {module := n : Import}
  let source ← importModules imports {}
  let visible ← importModules imports {} (level := .exported)
  searchPathRef.set [seed]
  let strictModules ← modulesIn seed `OmegaInit
  let strict ← importModules (strictModules.map fun n => {module := n : Import}) {}
  let output ← IO.FS.Handle.mk out .write
  let mut seen : NameSet := {}
  let mut ambiguous : NameSet := {}
  for data in visible.header.moduleData do
    for n in data.constNames do
      if seen.contains n then ambiguous := ambiguous.insert n
      seen := seen.insert n
  let action : M Unit := do
    for owner in modules do
      let i := (visible.getModuleIdx? owner).get!
      for name in visible.header.moduleData[i]!.constNames.qsort Name.lt do
        if ownerOf visible name == some owner then discard <| visit name
  discard <| (action.run {source,visible,output,ambiguous}).run {kernel := strict.toKernelEnv}
  output.flush

end OmegaChecks.InitCompiler.DiscoverProofs
def main (args : List String) : IO Unit := do
  let [seed,out] := args | throw <| IO.userError "expected a strict library and output file"
  OmegaChecks.InitCompiler.DiscoverProofs.run seed out
