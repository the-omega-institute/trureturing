import Lean
import Lean.Replay
import OmegaChecks.Interface
import OmegaChecks.InitPort.HostedBitwise

/-! Share pinned physical roots with an ordinary Lean importer. -/

open Lean

namespace OmegaChecks.HostedProjection

private def parts (path : System.FilePath) := #[path, path.addExtension "server", path.addExtension "private"]

private def sameImplementation (ported pinned : ConstantInfo) : Bool := Id.run do
  unless ported.name == pinned.name && ported.levelParams == pinned.levelParams &&
      ported.type.equal pinned.type do return false
  if OmegaChecks.InitPort.CompilerMarkers.valid ported then
    return pinned.isAxiom && pinned.isUnsafe
  if let .thmInfo _ := ported then return pinned matches .thmInfo _
  unless ported == pinned do return false
  unless (ported.value? (allowOpaque := true)).map ExprStructEq.mk ==
      (pinned.value? (allowOpaque := true)).map ExprStructEq.mk do return false
  if let .recInfo a := ported then
    let .recInfo b := pinned | return false
    return (a.rules.zip b.rules).all (fun (x, y) => x.rhs.equal y.rhs)
  return true

/-- The literal enum eliminator uses the isolated implementation of False.elim.
Unfold that helper at each actual universe and check its entire body in the pinned kernel. -/
private def sameEnumEliminator (isolated pinned : Environment) (ported official : ConstantInfo) : Bool := Id.run do
  unless ported.name == `noConfusionEnum && ported.name == official.name &&
      ported.levelParams == official.levelParams && ported.type.equal official.type do return false
  let some (.defnInfo elim) := isolated.find? `Omega.False.elim | return false
  let .defnInfo raw := ported | return false
  let .defnInfo original := official | return false
  let value := raw.value.replace fun e => match e with
    | .const `Omega.False.elim us => some (elim.value.instantiateLevelParams elim.levelParams us)
    | _ => none
  let .ok type := Kernel.check pinned {} value | return false
  return Kernel.isDefEqGuarded pinned {} type original.type &&
    Kernel.isDefEqGuarded pinned {} value original.value

private def physicalRoot (name : Name) : Bool :=
  name.getRoot != `Omega && !(`_private.OmegaInit).isPrefixOf name

private def renameTerm (moved : NameSet) (value : Expr) : Expr :=
  value.replace fun e => match e with
    | .const n us => if moved.contains n then some (.const (`Omega ++ n) us) else none
    | _ => none

private def relocate (moved : NameSet) (ci : ConstantInfo) : ConstantInfo := Id.run do
  if !(moved.contains ci.name || ci.getUsedConstantsAsSet.toArray.any moved.contains) then return ci
  let name := fun n => if moved.contains n then `Omega ++ n else n
  let term := renameTerm moved
  let base (v : ConstantVal) := {v with name := name v.name, type := term v.type}
  match ci with
  | .defnInfo v => return .defnInfo {v with toConstantVal := base v.toConstantVal, all := v.all.map name, value := term v.value}
  | .opaqueInfo v => return .opaqueInfo {v with toConstantVal := base v.toConstantVal, all := v.all.map name, value := term v.value}
  | .thmInfo v => return .thmInfo {v with toConstantVal := base v.toConstantVal, all := v.all.map name, value := term v.value}
  | .axiomInfo v => return .axiomInfo {v with toConstantVal := base v.toConstantVal}
  | .inductInfo v => return .inductInfo {v with toConstantVal := base v.toConstantVal}
  | .ctorInfo v => return .ctorInfo {v with toConstantVal := base v.toConstantVal}
  | .recInfo v => return .recInfo {v with toConstantVal := base v.toConstantVal, rules := v.rules.map fun r => {r with rhs := term r.rhs}}
  | .quotInfo v => return .quotInfo {v with toConstantVal := base v.toConstantVal}

private def digitProofName (n : Name) : Bool :=
  [`Omega.Nat.bitwise.eq_def, `Omega.Nat.one_and_eq_mod_two, `Omega.Nat.testBit_bitwise,
    `Omega.Nat.bitwise_lt_two_pow, `Omega.Nat.and_lt_two_pow].contains
    ((privateToUserName? n).getD n)

/-- Transport first-order occurrences of the digit computation one at a time. The original
proof uses the isolated division and remainder. Each substitution is an equality of naturals. -/
private def transportDigits (env : Environment) (moved : NameSet) (certificate : Expr)
    (th : TheoremVal) : IO Expr := do
  let some (.defnInfo bitwise) := env.find? `Omega.Nat.bitwise
    | throw <| IO.userError "missing isolated bitwise"
  let slow := renameTerm moved bitwise.value
  let expandAnd (e : Expr) := Meta.deltaExpand e (· == `Omega.Nat.land) (allowOpaque := true)
  let work : MetaM Expr := Meta.forallTelescope th.type fun xs target => do
    let target ← Meta.zetaReduce (← expandAnd target)
    let target := renameTerm moved target
    let proof := (← expandAnd th.value).replace fun e =>
      if e.isConstOf `Omega.Nat.bitwise then some bitwise.value else none
    let mut result := mkAppN (renameTerm moved proof) xs
    let isCall := fun (e : Expr) => e.isAppOfArity `Omega.Nat.bitwise 3
    let mut remaining := target
    let mut calls := #[]
    while let some call := remaining.find? isCall do
      calls := calls.push call
      remaining := remaining.replace fun e => if e == call then some (mkNatLit 0) else none
    if calls.isEmpty then throwError "no binary digit computation in {th.name}"
    let mut converted := target
    for call in calls do
      converted := converted.replace fun e =>
        if e == call then some (mkAppN slow call.getAppArgs) else none
    for call in calls do
      let args := call.getAppArgs
      let before := mkAppN slow args
      let after := converted.replace fun e => if e == before then some call else none
      let motive ← Meta.withLocalDeclD `value (mkConst `Nat) fun v => do
        Meta.mkLambdaFVars #[v] (after.replace fun e => if e == call then some v else none)
      let equality := mkApp4 certificate args[0]! (mkApp (mkConst `Nat.succ) args[1]!) args[1]! args[2]!
      result := mkAppN (mkConst `Eq.subst [.succ .zero]) #[mkConst `Nat, motive, before, call, equality, result]
      converted := after
    Meta.mkLambdaFVars xs result
  work.run'.toIO' {fileName := "<hosted digit computation>", fileMap := default} {env}

/-- Check the pointwise equality even for a selected module that exports no digit theorem. -/
private def checkDigitComputation (kernel : Environment) (moved : NameSet) (certificate : Expr) : IO Unit := do
  let some (.defnInfo bitwise) := kernel.find? `Omega.Nat.bitwise
    | throw <| IO.userError "missing hosted bitwise"
  let slow := renameTerm moved bitwise.value
  let work : MetaM (Expr × Expr) := Meta.forallTelescope bitwise.type fun xs _ => do
    let #[f, n, m] := xs | throwError "unexpected bitwise interface"
    let equality := mkApp4 certificate f (mkApp (mkConst `Nat.succ) n) n m
    let claim := mkApp3 (mkConst `Eq [.succ .zero]) (mkConst `Nat)
      (mkAppN slow xs) (mkAppN (mkConst bitwise.name) xs)
    return (← Meta.mkLambdaFVars xs equality, ← Meta.mkForallFVars xs claim)
  let (proof, expected) ← work.run'.toIO'
    {fileName := "<hosted bitwise equality>", fileMap := default} {env := kernel}
  let .ok inferred := Kernel.check kernel {} proof
    | throw <| IO.userError "invalid hosted bitwise equality"
  unless Kernel.isDefEqGuarded kernel {} inferred expected do
    throw <| IO.userError "hosted bitwise differs from the isolated digit computation"

private def hostedConstant (env : Environment) (moved : NameSet) (certificate : Expr)
    (ci : ConstantInfo) : IO ConstantInfo := do
  let changed := relocate moved ci
  unless moved.contains `Nat.xor do return changed
  if ci.name == `Omega.Nat.bitwise then
    if let some (.defnInfo impl) := env.find? ci.name then
      return .defnInfo impl
  if ci.name == `Nat.xor then
    if let some (.defnInfo impl) := env.find? ci.name then
      return relocate moved (.defnInfo impl)
  if digitProofName ci.name then
    if let .thmInfo th := ci then
      if let .thmInfo out := changed then
        return .thmInfo {out with value := ← transportDigits env moved certificate th}
  return changed

private def project (source output : System.FilePath) (env pinned : Environment) (moved : NameSet) (certificate : Expr) (owner : Name) : IO Unit := do
  let raw := modToFilePath source owner "olean"
  let path := modToFilePath output owner "olean"
  let strict := (← readModuleDataParts (parts raw)).map Prod.fst
  let original := owner.replacePrefix `OmegaInit `Init
  let idx := (env.getModuleIdx? owner).get!
  let mut shared : NameSet := {}
  for ci in strict[2]!.constants do
    unless owner.getRoot == `OmegaInit && physicalRoot ci.name && !moved.contains ci.name do continue
    if let some target := pinned.find? ci.name then
      unless sameImplementation ci target || sameEnumEliminator env pinned ci target do throw <| IO.userError s!"incompatible physical root {owner}/{ci.name}"
      shared := shared.insert ci.name
  let affected := strict[2]!.constants.any fun ci =>
    moved.contains ci.name || ci.getUsedConstantsAsSet.toArray.any moved.contains ||
    (moved.contains `Nat.xor && (ci.name == `Omega.Nat.bitwise || digitProofName ci.name))
  if shared.isEmpty && !affected then return
  IO.FS.createDirAll path.parent.get!
  let mut outputParts := #[]
  for data in strict, file in parts path, level in #[OLeanLevel.exported,.server,.private] do
    let remaining := data.constants.filter fun ci => !shared.contains ci.name
    let constants ← remaining.mapM (hostedConstant env moved certificate)
    let mut metadata := (← mkEmptyEnvironment).setMainModule owner
    for (aliasName, target) in aliasExtension.getModuleEntries env idx (level := level) do
      let target := if moved.contains target then `Omega ++ target else target
      if aliasName != target then metadata := addAlias metadata aliasName target
    let renamed := fun n => if moved.contains n then `Omega ++ n else n
    for n in protectedExt.getModuleEntries env idx (level := level) do
      metadata := addProtected metadata (renamed n)
    for (n, status) in reducibilityCoreExt.getModuleEntries env idx (level := level) do
      let expose := moved.contains `Nat.xor && [`Nat.xor, `Omega.Nat.bitwise].contains n
      let status := if expose then .semireducible else status
      metadata := reducibilityCoreExt.addEntry (asyncDecl := renamed n) metadata (renamed n, status)
    let replaced := #[aliasExtension.name, protectedExt.name, reducibilityCoreExt.name]
    let mut entries := data.entries.filter fun e => !replaced.contains e.1
    let mut redirects := #[]
    for n in data.constNames do
      if moved.contains n && (env.find? n).any (· matches .defnInfo _) then
        metadata := Compiler.implementedByAttr.ext.addEntry (asyncDecl := `Omega ++ n) metadata (`Omega ++ n, n)
        redirects := redirects.push (`Omega ++ n)
    -- Keep every pre-existing compiler entry and add the same native calls used by the isolated library.
    -- The input entries are already restricted to this visibility level.
    let dataMeta ← mkModuleData metadata .private
    entries := entries ++ dataMeta.entries.filter (fun e => replaced.contains e.1 && !e.2.isEmpty)
    for (ext, more) in dataMeta.entries do
      if ext == Compiler.implementedByAttr.ext.name && !more.isEmpty then
        let earlier := (entries.find? (·.1 == ext)).map Prod.snd |>.getD #[]
        entries := (entries.filter (·.1 != ext)).push (ext, earlier ++ more)
    let imports := if shared.isEmpty && redirects.isEmpty then data.imports else data.imports.push {module := original}
    let result := { data with
      constants
      constNames := constants.map (·.name)
      entries
      imports
      extraConstNames := data.extraConstNames.filter (!shared.contains ·) }
    outputParts := outputParts.push (file, result)
  saveModuleDataParts owner outputParts

def write (source output : System.FilePath) (names : Array Name)
    (referencePath? : Option System.SearchPath := none) : IO Unit := do
  unless names.all (fun n => #[`OmegaInit, `OmegaMathlib, `OmegaMath].contains n.getRoot) do
    throw <| IO.userError "expected isolated mathematical library modules"
  if let some paths := referencePath? then searchPathRef.set paths else initSearchPath (← findSysroot)
  let certificates ← importModules #[{module := `OmegaChecks.InitPort.HostedBitwise}] {} (level := .private)
  searchPathRef.set [← getLibDir (← findSysroot)]
  let upstream := names.filter (·.getRoot == `OmegaInit)
  let pinned ← importModules (upstream.map fun n => {module := n.replacePrefix `OmegaInit `Init, importAll := true}) {} (level := .private)
  searchPathRef.set [source]
  let env ← importModules (names.map fun n => {module := n, importAll := true}) {} (level := .private)
  let mut moved : NameSet := {}
  for n in #[`Nat.div, `Nat.mod, `Nat.gcd, `Nat.xor] do
    if let some raw := env.find? n then
      let some host := pinned.find? n | throw <| IO.userError s!"missing official {n}"
      unless sameImplementation raw host do
        unless raw.type.equal host.type && raw matches .defnInfo _ do throw <| IO.userError s!"invalid arithmetic interface for {n}"
        OmegaChecks.Interface.checkInstalledEquation env certificates n
        moved := moved.insert n
  let some (.thmInfo same) := certificates.find? `OmegaChecks.InitPort.HostedBitwise.sameSteps
    | throw <| IO.userError "missing hosted bitwise certificate"
  let localProof := fun n => [`OmegaChecks.InitPort.HostedBitwise, `OmegaChecks.Interface.Equations].any fun mod =>
    certificates.getModuleIdx? mod == certificates.getModuleIdxFor? n
  let certificate ← (Meta.deltaExpand same.value localProof (allowOpaque := true)).toIO'
    {fileName := "<hosted bitwise certificate>", fileMap := default} {env := certificates}
  let operations := moved
  for (n, ci) in env.constants.toList do
    if ci.isTheorem && operations.toArray.any (·.isPrefixOf n) then moved := moved.insert n
  let mut terms := {}
  for (n,ci) in env.constants.toList do
    if moved.contains n || !pinned.contains n then
      let changed ← hostedConstant env moved certificate ci
      terms := terms.insert changed.name changed
  let checked ← pinned.toKernelEnv.replay terms
  if moved.contains `Nat.xor then
    checkDigitComputation (Environment.ofKernelEnv checked) moved certificate
  -- Each physical proof occurrence has a body, including duplicated public equations.
  for data in env.header.moduleData do
    for ci in data.constants do
      if let .thmInfo t := ci then
        let name := if moved.contains t.name then `Omega ++ t.name else t.name
        let some canonical := terms[name]? | continue
        let some body := (← hostedConstant env moved certificate ci).value? (allowOpaque := true) | unreachable!
        if (canonical.value? (allowOpaque := true)).any (·.equal body) then continue
        let kernel := Environment.ofKernelEnv checked
        let .ok type := Kernel.check kernel {} body | throw <| IO.userError s!"invalid hosted proof {name}"
        unless Kernel.isDefEqGuarded kernel {} type (renameTerm moved t.type) do
          throw <| IO.userError s!"hosted proof type mismatch for {name}"
  for name in names do project source output env pinned moved certificate name


/-- Compare imported foundation bytes with the kernel-replayed projection of the isolated library. -/
def verify (source view : System.FilePath) (names : Array Name) (referencePath : System.SearchPath) : IO Unit :=
  IO.FS.withTempDir fun tmp => do
    write source tmp names (some referencePath)
    for owner in names do
      let rel := modToFilePath "." owner "olean"
      for file in parts rel do
        let generated := tmp / file
        let expected := if ← generated.pathExists then generated else source / file
        unless (← IO.FS.readBinFile expected) == (← IO.FS.readBinFile (view / file)) do
          throw <| IO.userError s!"hosted projection differs from isolated source for {file}"

end OmegaChecks.HostedProjection
