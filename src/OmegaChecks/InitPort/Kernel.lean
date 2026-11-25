import Lean
import Lean.Replay
import OmegaChecks.InitCompiler.Proofs

open Lean

namespace InitKernelPort

def moduleOf (env : Environment) (n : Name) : Option Name := do
  let i ← env.getModuleIdxFor? n
  return env.header.moduleNames[i]!

/-- Keep generated private names tied to the translated owner. -/
def portName (source : Environment) (n : Name) : Name :=
  if let some u := privateToUserName? n then
    if let some owner := moduleOf source n then
      mkPrivateNameCore (owner.replacePrefix `Init `OmegaInit) (`Omega ++ u)
    else `Omega ++ n
  else `Omega ++ n

/-- Binary expansion avoids allocating a unary term for a huge numeral. -/
partial def natTerm (n : Nat) : Expr :=
  if n < 32 then
    n.fold (init := mkConst `Omega.Nat.zero) (fun _ _ x => mkApp (mkConst `Omega.Nat.succ) x)
  else
    let x := mkBVar 0
    let twice := mkApp2 (mkConst `Omega.Nat.add) x x
    .letE `half (mkConst `Omega.Nat) (natTerm (n / 2))
      (if n % 2 == 0 then twice else mkApp (mkConst `Omega.Nat.succ) twice) false

/-- Replace recursively inside projection subjects, preserving binder syntax and universe levels. -/
partial def translate (rename : Name → Name) (e : Expr) : Expr :=
  e.replace fun
    | .const n ls => some (.const (rename n) ls)
    | .proj owner field target => some (.proj (rename owner) field (translate rename target))
    | .lit (.natVal n) => some (natTerm n)
    | _ => none

def invalidExpr (e : Expr) : Bool :=
  e.hasFVar || e.hasMVar || e.hasLooseBVars ||
    (e.find? fun x => x matches .lit (.strVal _)).isSome

def translateDecl (source : Environment) (info : ConstantInfo) : Except String Declaration := do
  let rename := portName source
  let val (v : ConstantVal) := { v with name := rename v.name, type := translate rename v.type }
  if info.isUnsafe || info.isPartial then throw "unsafe/partial"
  let some body := info.value? (allowOpaque := true) | throw "no kernel body"
  if invalidExpr info.type || invalidExpr body then throw "open term or unsupported string literal"
  let body := translate rename body
  match info with
  | .defnInfo d => return .defnDecl { d with toConstantVal := val d.toConstantVal, value := body, all := d.all.map rename }
  | .thmInfo d => return .thmDecl { d with toConstantVal := val d.toConstantVal, value := body, all := d.all.map rename }
  | .opaqueInfo d => return .opaqueDecl { d with toConstantVal := val d.toConstantVal, value := body, all := d.all.map rename }
  | _ => throw "unsupported declaration kind"

inductive Outcome
  | existing
  | added
  | blocked (reason : String) (cause : Option Name := none)
  deriving Inhabited

structure State where
  env : Kernel.Environment
  results : Std.HashMap Name Outcome := {}
  visiting : NameSet := {}

structure Context where
  source : Environment
  base : Environment
  maxHeartbeats : Nat
  excluded : NameMap String
  publicNames : NameSet
  output : IO.FS.Handle

abbrev M := ReaderT Context (StateRefT State IO)

def describe : Outcome → String × Option Name
  | .existing => ("existing", none)
  | .added => ("added", none)
  | .blocked s n => (s,n)

def record (name : Name) (outcome : Outcome) : M Bool := do
  let c ← read
  let owner := moduleOf c.source name |>.getD .anonymous
  let (diagnostic, cause) := describe outcome
  c.output.putStrLn (toJson #[owner.toString,name.toString, (toString (c.publicNames.contains name)),
    diagnostic, (cause.map Name.toString).getD ""]).compress
  c.output.flush
  modify fun s => { s with results := s.results.insert name outcome, visiting := s.visiting.erase name }
  return match outcome with | .blocked .. => false | _ => true

/-- Compare the entire generated kernel entry, including the iota rules of recursors. -/
def expectGenerated (source : Environment) (ci : ConstantInfo) : Option ConstantInfo := Id.run do
  let ren := portName source
  let val (v : ConstantVal) := {v with name := ren v.name, type := translate ren v.type}
  match ci with
  | .inductInfo v => return some <| .inductInfo { v with toConstantVal := val v.toConstantVal, ctors := v.ctors.map ren, all := v.all.map ren }
  | .ctorInfo v => return some <| .ctorInfo { v with toConstantVal := val v.toConstantVal, induct := ren v.induct }
  | .recInfo v => return some <| .recInfo { v with toConstantVal := val v.toConstantVal, all := v.all.map ren, rules := v.rules.map fun r => {r with ctor := ren r.ctor, rhs := translate ren r.rhs} }
  | _ => return none

/-- The original kernel erases typeclass output markers while generating recursors.
Our independently named markers are definitionally transparent, so compare all shape data
literally and the types and computation rules up to kernel conversion. -/
def agrees (env : Kernel.Environment) (src target : Option ConstantInfo) : Bool := Id.run do
  if src == target then return true
  let eqv := Kernel.isDefEqGuarded (.ofKernelEnv env) {}
  if let some (.recInfo a) := src then
    if let some (.recInfo b) := target then
      unless {a with type := b.type, rules := b.rules} == b && a.rules.length == b.rules.length && eqv a.type b.type do return false
      for x in a.rules, y in b.rules do
        unless x.ctor == y.ctor && x.nfields == y.nfields && eqv x.rhs y.rhs do return false
      return true
  return false

structure Family where
  decl : Declaration
  externals : NameSet
  generated : Array Name

def family (src : Environment) (i : InductiveVal) : Except String Family := do
  let rename := portName src
  let mut types := []
  let mut deps : NameSet := {}
  let mut names := #[]
  for n in i.all do
    let some (.inductInfo v) := src.find? n | throw "missing family member"
    if v.isUnsafe || invalidExpr v.type then throw "inadmissible family"
    let mut ctors := []
    deps := deps ++ v.type.getUsedConstantsAsSet
    names := names.push n
    for k in v.ctors do
      let some (.ctorInfo cv) := src.find? k | throw "missing constructor"
      if cv.isUnsafe || invalidExpr cv.type then throw "inadmissible constructor"
      names := names.push k
      deps := deps ++ cv.type.getUsedConstantsAsSet
      ctors := ctors ++ [{name := rename k, type := translate rename cv.type : Constructor}]
    let recn := n ++ `rec
    names := names.push recn
    types := types ++ [{name := rename n, type := translate rename v.type, ctors : InductiveType}]
  for n in names do deps := deps.erase n
  return {decl := .inductDecl i.levelParams i.numParams types false, externals := deps, generated := names}

/-- Run each declaration on a fresh worker so the kernel heartbeat counter is local. -/
def checkDecl (env : Kernel.Environment) (decl : Declaration) (budget : Nat) :
    BaseIO (Except Kernel.Exception Kernel.Environment) := do
  let work : BaseIO (Except Kernel.Exception Kernel.Environment) := do
    let initial ← IO.getNumHeartbeats
    return env.addDeclCore (initial + budget).toUSize 1000 decl none
  let task ← work.asTask (prio := .dedicated)
  return task.get

/-- For equations compiled by the pattern matcher, expose at most two Nat or List arguments.
Each leaf proposes reflexivity. The kernel checks the entire resulting elimination term. -/
private partial def equationCases? (type : Expr) (fuel := 2) (depth := 0) : Option Expr := do
  let fresh := fun (n : Name) => mkFVar ⟨Name.num n depth⟩
  let lam := fun (x : Expr) n domain body bi => Expr.lam n domain (body.abstract #[x]) bi
  let .forallE n dom body bi := type |
    let .const `Omega.Eq us := type.getAppFn | none
    let #[α, lhs, _] := type.getAppArgs | none
    return mkApp2 (mkConst `Omega.Eq.refl us) α lhs
  let x := fresh `x
  let motive := Expr.lam n dom body .default
  let after := fun y f => equationCases? (body.instantiate1 y) f (depth + 1)
  if fuel > 0 && dom.isConstOf `Omega.Nat then
    let zero ← after (mkConst `Omega.Nat.zero) (fuel - 1)
    let k := fresh `k
    let step ← after (mkApp (mkConst `Omega.Nat.succ) k) (fuel - 1)
    let ihType := body.instantiate1 k
    let succ := lam k `k dom (.lam `ih ihType step .default) .default
    return lam x n dom (mkApp4 (mkConst `Omega.Nat.rec [.zero]) motive zero succ x) bi
  if let .app (.const `Omega.List [u]) α := dom then
    if fuel > 0 then
      let nil ← after (mkApp (mkConst `Omega.List.nil [u]) α) (fuel - 1)
      let head := fresh `head
      let tail := fresh `tail
      let step ← after (mkApp3 (mkConst `Omega.List.cons [u]) α head tail) (fuel - 1)
      let ih := Expr.lam `ih (body.instantiate1 tail) step .default
      let cons := lam head `head α (lam tail `tail dom ih .default) .default
      return lam x n dom (mkApp5 (mkConst `Omega.List.rec [.zero,u]) α motive nil cons x) bi
  return lam x n dom (← after x fuel) bi

/-- Search only theorem interfaces with all referenced constants present. Share one kernel
heartbeat limit across all attempted proofs and keep the original rejection on failure. -/
private def alternateProof (ci : ConstantInfo) : M Bool := do
  let .thmInfo th := ci | return false
  let c ← read
  let rename := portName c.source
  let type := translate rename th.type
  let state ← get
  if invalidExpr type || type.getUsedConstants.any (fun n => (state.env.find? n).isNone) then return false
  let base := {th with name := rename th.name, type, all := [rename th.name]}
  let work : BaseIO (Option Kernel.Environment) := do
    let stop := (← IO.getNumHeartbeats) + c.maxHeartbeats
    let mut candidates := OmegaChecks.InitCompiler.elementaryCandidates type
    if th.name == th.name.getPrefix ++ `eq_def then
      if let some term := equationCases? type then candidates := term :: candidates
    for term in candidates do
      if (← IO.getNumHeartbeats) >= stop then break
      let decl := Declaration.thmDecl {base with value := term}
      if let .ok next := state.env.addDeclCore stop.toUSize 1000 decl none then return some next
    return none
  let task ← work.asTask (prio := .dedicated)
  if let some next := task.get then
    modify fun s => {s with env := next}
    return ← record ci.name .added
  return false

partial def visit (n : Name) : M Bool := do
  let c ← read
  if let some result := (← get).results[n]? then
    return match result with | .blocked .. => false | _ => true
  if (← get).visiting.contains n then return false
  let some owner := moduleOf c.source n | return ← record n (.blocked "unknown official module")
  if owner.getRoot != `Init then return ← record n (.blocked "outside Init")
  let some ci := c.source.find? n | return ← record n (.blocked "missing official constant")
  let dest := portName c.source n
  if let some i := c.base.find? dest then
    if i.isAxiom || i.isUnsafe || i.isPartial || (i matches .quotInfo _) ||
        moduleOf c.base dest != some (owner.replacePrefix `Init `OmegaInit) then
      return ← record n (.blocked "unverified seed name or wrong seed owner")
    return ← record n .existing
  if let some generated := (← get).env.find? dest then
    if agrees (← get).env (expectGenerated c.source ci) (some generated) then return ← record n .added
    return ← record n (.blocked "target name collision")
  if n == Meta.mkSmartUnfoldingNameFor n.getPrefix then
    if c.base.contains (portName c.source n.getPrefix) then
      return ← record n (.blocked "smart unfolding belongs to a different implementation" (some n.getPrefix))
    if let some body := ci.value? then
      let missing := body.find? fun expr => Id.run do
        let some m := Meta.smartUnfoldingMatch? expr | return false
        let some matcher := m.getAppFn.constName? | return true
        return (Meta.getMatcherInfoCore? c.base (portName c.source matcher)).isNone
      if missing.isSome then return ← record n (.blocked "smart unfolding requires unavailable matcher metadata")
  if let some reason := c.excluded.find? n then return ← record n (.blocked reason)
  if ci.isAxiom then return ← record n (.blocked "axiom")
  if ci.isUnsafe || ci.isPartial then return ← record n (.blocked "unsafe/partial")
  if let .inductInfo i := ci then
    let .ok f := family c.source i | return ← record n (.blocked "malformed family")
    if let some member := f.generated.find? (fun member => c.excluded.contains member) then
      return ← record n (.blocked "unavailable family member" (some member))
    modify fun s => {s with visiting := s.visiting.insert n}
    for dep in f.externals do
      if !(← visit dep) then return ← record n (.blocked "unavailable family dependency" (some dep))
    match ← checkDecl (← get).env f.decl c.maxHeartbeats with
    | .error ex =>
      let msg ← ex.toMessageData {} |>.toString
      return ← record n (.blocked ("kernel family: " ++ (msg.take 1200).toString))
    | .ok env =>
      for orig in f.generated do
        let some spec := c.source.find? orig | return ← record n (.blocked "missing family result" (some orig))
        if !agrees env (expectGenerated c.source spec) (env.find? (portName c.source orig)) then
          return ← record n (.blocked "generated kernel entry mismatch" (some orig))
      modify fun s => {s with env}
      return ← record n .added
  if ci matches .ctorInfo _ | .recInfo _ then
    let parent := match ci with | .ctorInfo v => v.induct | .recInfo v => v.all.head! | _ => Name.anonymous
    if !(← visit parent) then return ← record n (.blocked "unavailable family" (some parent))
    if let some generated := (← get).env.find? dest then
      if agrees (← get).env (expectGenerated c.source ci) (some generated) then return ← record n .added
    return ← record n (.blocked "generated kernel entry mismatch" (some parent))
  if !(ci matches .thmInfo _ | .defnInfo _ | .opaqueInfo _) then
    return ← record n (.blocked "requires inductive family or primitive")
  modify fun s => {s with visiting := s.visiting.insert n}
  for dep in ci.type.getUsedConstantsAsSet do
    if !(← visit dep) then return ← record n (.blocked "unavailable dependency" (some dep))
  for dep in ci.getUsedConstantsAsSet do
    if !(← visit dep) then
      if ← alternateProof ci then return true
      return ← record n (.blocked "unavailable dependency" (some dep))
  let .ok decl := translateDecl c.source ci |
    if ← alternateProof ci then return true
    return ← record n (.blocked "open term or unsupported literal")
  match ← checkDecl (← get).env decl c.maxHeartbeats with
  | .error ex =>
    if ← alternateProof ci then return true
    let msg ← ex.toMessageData {} |>.toString
    return ← record n (.blocked ("kernel: " ++ (msg.take 1200).toString))
  | .ok next =>
    modify fun s => {s with env := next}
    return ← record n .added

def modulesIn (root : System.FilePath) : IO (Array Name) := do
  let mut names := #[`Init]
  for f in ← (root / "Init").walkDir do
    if f.extension == some "olean" then names := names.push (← moduleNameOfFileName f root)
  return names.qsort Name.lt

/-- Save the kernel-checked additions as an importable file. Seed constants remain imported. -/
def writeMonolithic (base : Environment) (final : Kernel.Environment)
    (output : System.FilePath) : IO Unit := do
  let mut cs := #[]
  for (n, c) in final.constants.toList do
    if !base.contains n then cs := cs.push c
  cs := cs.qsort fun a b => Name.lt a.name b.name
  let imports := base.header.moduleNames.map (fun owner => {module := owner, isExported := true : Import})
  let data : ModuleData := { isModule := false, imports, constNames := cs.map (·.name), constants := cs, extraConstNames := #[], entries := #[] }
  IO.FS.createDirAll output
  saveModuleData (output / "OmegaImported.olean") `OmegaImported data
  IO.println s!"Wrote {cs.size} kernel declarations to {output / "OmegaImported.olean"}"

def run (strictPath artifacts : System.FilePath) (outPath : String) (exclude : System.FilePath) (modules : List Name) : IO Unit := do
  let lib ← getLibDir (← findSysroot)
  searchPathRef.set [lib]
  let allMods ← if modules.isEmpty then modulesIn lib else pure modules.toArray
  let imports := allMods.map fun n => {module := n : Import}
  let source ← importModules imports {} (level := .private)
  let vis ← importModules imports {} (level := .exported)
  let mut publicNames : NameSet := {}
  for d in vis.header.moduleData do
    for n in d.constNames do
      if !isPrivateName n && !n.isInternalOrNum && !n.hasMacroScopes then
        publicNames := publicNames.insert n
  searchPathRef.set [strictPath]
  let mut seedModules := #[{module := `OmegaInit : Import}]
  for file in ← (strictPath / "OmegaInit").walkDir do
    if file.extension == some "olean" then
      seedModules := seedModules.push {module := ← moduleNameOfFileName file strictPath}
  let base ← importModules seedModules {}
  for (_, ci) in base.constants.toList do
    if ci.isAxiom || ci.isUnsafe || ci.isPartial || ci matches .quotInfo _ then
      throw <| IO.userError s!"invalid strict seed {ci.name}"
  let initial ← (← mkEmptyEnvironment).toKernelEnv.replay base.constants.map₁
  let output ← IO.FS.Handle.mk outPath .write
  let config ← IO.ofExcept <| Json.parse (← IO.FS.readFile exclude)
  let exclusions : Array (String × String) ← IO.ofExcept <| do
    if let .ok entries := fromJson? (α := Array (String × String)) config then return entries
    return (← fromJson? (α := Array String) config).map fun n => (n, "no computation correspondence")
  for (name, _) in exclusions do
    if base.contains (portName source name.toName) then
      throw <| IO.userError s!"cannot exclude {name}: already present in the source seed"
  let excluded := exclusions.foldl (init := ({} : NameMap String)) fun acc (n, r) => acc.insert n.toName r
  let maxHeartbeats := (← IO.getEnv "OMEGA_PORT_HEARTBEATS").bind String.toNat? |>.getD 5000
  let ctx := {source,base,publicNames,excluded,output, maxHeartbeats : Context}
  let action : M Unit := do
    for owner in source.header.moduleNames, data in source.header.moduleData do
      if owner.getRoot == `Init then
        for n in data.constNames do discard <| visit n
  let (_, s) ← action.run ctx |>.run {env := initial}
  output.flush
  writeMonolithic base s.env artifacts
  IO.println s!"{s.results.size} outcomes in {outPath}"

end InitKernelPort

def main (args : List String) : IO Unit := do
  let dir :: artifacts :: out :: exclusions :: mods := args | throw <| IO.userError "expected seed, artifacts, report, exclusions, and official roots"
  InitKernelPort.run dir artifacts out exclusions (mods.map String.toName)
