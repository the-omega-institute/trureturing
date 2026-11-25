import OmegaChecks.Interface
import OmegaChecks.ObjectOccurrences

/-! Compare protected and candidate mathematical declarations across changes of defining module. -/

open Lean

private structure Request where
  protectedPath : String
  candidatePath : String
  protectedModules : Array String
  candidateModules : Array String
  deriving FromJson

private def load (path : String) (modules : Array String) : IO Environment := do
  let sysroot ← getLibDir (← findSysroot)
  searchPathRef.set (System.SearchPath.parse path ++ [sysroot])
  importModules (modules.map fun module => {module := module.toName}) {}

private def owner? (env : Environment) (name : Name) : Option Name := do
  let index ← env.getModuleIdxFor? name
  return env.header.moduleNames[index]!

/-- Follow old public spellings retained as compiler aliases, including direct upstream
reuse. The standard target must also be exported by a verified port or belong to Init. -/
private def publicationAliases (env : Environment) : NameMap Name × NameSet := Id.run do
  let mut names : NameMap Name := {}
  let mut conflicts : NameSet := {}
  let mut standard : NameSet := {}
  for mod in env.header.modules, i in [:env.header.modules.size] do
    let owner := mod.module.getRoot
    if !([`OmegaMath, `OmegaMathlib, `OmegaInit, `D5].contains owner) then continue
    for (alias, target) in aliasExtension.getModuleEntries env i do
      if owner == `OmegaMathlib && alias.getRoot == `OmegaMathlib then
        standard := standard.insert target
      if let some earlier := names.find? alias then
        if earlier != target then conflicts := conflicts.insert alias
      names := names.insert alias target
  for name in conflicts do names := names.erase name
  return (names, standard)

/-- Public constants identify the destination of a moved module. Private constants
include that module in their internal Lean names. -/
private def ownerMoves (old new : Environment) (modules : Array Name) : IO (NameMap Name) := do
  let mut moves : NameMap Name := {}
  for owner in modules do
    let some idx := old.getModuleIdx? owner | throw <| IO.userError s!"missing protected module {owner}"
    let mut targets : NameSet := {}
    for n in old.header.moduleData[idx]!.constNames do
      if !isPrivateName n && !n.isInternalOrNum then
        if let some dst := owner? new n then targets := targets.insert dst
    if let [target] := targets.toList then moves := moves.insert owner target
  return moves

private def translateName (old : Environment) (moves : NameMap Name) (n : Name) : Name := Id.run do
  if let some userName := privateToUserName? n then
    if let some owner := owner? old n then
      if let some target := moves.find? owner then
        return mkPrivateNameCore target userName
  return n

private def canonicalName : Name → String
  | .anonymous => "n0"
  | .str parent s => s!"ns({canonicalName parent},{s.utf8ByteSize}:{s})"
  | .num parent n => s!"nn({canonicalName parent},{n})"

private partial def translate (f : Name → Name) (e : Expr) : Expr :=
  e.replace fun
    | .const n us => some (.const (f n) us)
    | .proj n i b => if f n == n then none else some (.proj (f n) i (translate f b))
    | _ => none

private abbrev Bridges := NameMap (Name × Name)

/-- Discover a proved pointwise interpretation of a protected definition when its
candidate becomes an alias to an official constant. Build the two sides from the actual
compiled bodies. A theorem about a same-named substitute cannot certify the change. -/
private def findBridges (old new : Environment) (modules : Array Name) (rename : Name → Name) :
    IO Bridges := do
  let mut found : Bridges := {}
  for module in modules do
    if module.getRoot != `OmegaMath then continue
    let some idx := old.getModuleIdx? module | continue
    for n in old.header.moduleData[idx]!.constNames do
      let some (.defnInfo before) := old.find? n | continue
      let some (.defnInfo after) := new.find? (rename n) | continue
      let .const official _ := after.value | continue
      let some upstreamOwner := owner? new official | continue
      if !([`Mathlib, `Init].contains upstreamOwner.getRoot) || translate rename before.value == after.value then continue
      let some owner := new.getModuleIdxFor? after.name | continue
      let expected : MetaM (Array Expr) := Meta.forallTelescope after.type fun xs result => do
        let lhs := mkAppN (translate rename before.value) xs
        let rhs := mkAppN after.value xs
        let eq ← Meta.mkForallFVars xs (← Meta.mkEq lhs rhs)
        if result.isProp then
          return #[eq, ← Meta.mkForallFVars xs (mkApp2 (mkConst ``Iff) lhs rhs)]
        return #[eq]
      let proofTypes ← expected.run' |>.toIO' { fileName := "<migration>", fileMap := default } { env := new }
      for proof in new.header.moduleData[owner]!.constNames do
        let some (.thmInfo cert) := new.find? proof | continue
        if proofTypes.any fun t => Kernel.isDefEqGuarded new {} t cert.type then
          let axioms ← (collectAxioms proof : CoreM _).toIO' { fileName := "<migration>", fileMap := default } { env := new }
          if axioms.all fun a => #[`propext, `Classical.choice, `Quot.sound].contains a then
            found := found.insert n (official, proof)
            break
  return found

/-- A positional check preserves upstream object identity even for definitionally equal
local wrappers. The interface check separately checks binder visibility and inductive shape. -/
private def compare (env : Environment) (rename : Name → Name) (old new : ConstantInfo)
    (bridge : Option (Name × Name)) (standardAlias := false) : IO Unit := do
  let fromOld := fun (e : Expr) =>
    translate rename (e.instantiateLevelParams old.levelParams (new.levelParams.map Level.param))
  if standardAlias then
    discard <| OmegaChecks.Interface.compare env rename old new
    return
  unless old.ctorIdx == new.ctorIdx do throw <| IO.userError "declaration kind changed"
  unless fromOld old.type == new.type do
    -- Numeric literals and macro metadata may differ across compilations. Keep every
    -- mathematical object at its original position and require kernel conversion.
    unless OmegaChecks.ObjectOrigins.occurrences (fromOld old.type) false ==
        OmegaChecks.ObjectOrigins.occurrences new.type false &&
        Kernel.isDefEqGuarded env {} (fromOld old.type) new.type do
      throw <| IO.userError "compiled type changed"
  if bridge.isSome then return
  match old, new with
  | .defnInfo x, .defnInfo y =>
    unless x.safety == y.safety && fromOld x.value == y.value do
      throw <| IO.userError "definition implementation changed"
  | .opaqueInfo x, .opaqueInfo y =>
    unless fromOld x.value == y.value do throw <| IO.userError "opaque implementation changed"
  | _, _ => pure ()
  discard <| OmegaChecks.Interface.compare env rename old new

def main (args : List String) : IO Unit := do
  let [request, output] := args | throw <| IO.userError "expected comparison request and output paths"
  let input : Request ← IO.ofExcept <| Json.parse (← IO.FS.readFile request) >>= fromJson?
  let old ← load input.protectedPath input.protectedModules
  let new ← load input.candidatePath input.candidateModules
  let modules := input.protectedModules.map String.toName
  let moves ← ownerMoves old new modules
  let (aliases, ports) := publicationAliases new
  let lookup := fun n =>
    let target := translateName old moves n
    if new.contains target then target else (aliases.find? target).getD target
  let bridges ← findBridges old new modules lookup
  let rename := fun n => (bridges.find? n).map Prod.fst |>.getD (lookup n)
  let mut rows := #[]
  for module in modules do
    let some idx := old.getModuleIdx? module | throw <| IO.userError s!"missing protected module {module}"
    for name in old.header.moduleData[idx]!.constNames do
      let some before := old.find? name | throw <| IO.userError s!"missing protected declaration {name}"
      let dst := lookup name
      let fields := [("module", toJson module.toString), ("nameKey", toJson (canonicalName name)),
        ("name", toJson name.toString), ("candidateKey", toJson (canonicalName dst))]
      let row ← match new.find? dst, owner? new dst with
        | some after, some owner => do
          let fields := ("candidateModule", toJson owner.toString) :: ("candidateTheorem", toJson after.isTheorem) :: fields
          try
            let bridge := bridges.find? name
            let standardAlias := dst != name && (owner.getRoot == `Init || owner.getRoot == `Mathlib && ports.contains dst)
            compare new rename before after bridge standardAlias
            let fields := ("standardAlias", toJson standardAlias) :: fields
            let fields := match bridge with
              | some (target, proof) =>
                ("upstream", toJson target.toString) :: ("correspondence", toJson proof.toString) :: fields
              | none => fields
            pure (("comparison", toJson "checked compiled declaration") :: fields)
          catch ex =>
            pure (("obligation", toJson ex.toString) :: fields)
        | _, _ => pure (("obligation", toJson "missing candidate declaration") :: fields)
      rows := rows.push (Json.mkObj row)
  IO.FS.writeFile output (Json.arr rows).compress
