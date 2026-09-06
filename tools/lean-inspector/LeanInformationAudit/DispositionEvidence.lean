import LeanInformationAudit.AnalysisDisposition
import LeanInformationAudit.SealCommand
import LeanInformationAudit.StructuralRealization

namespace LeanInformationAudit

open Lean Meta
open D5.S3.ConceptDynamics.InformationEscape

universe u v w

/-- Catalog membership evidence for a generated structural theorem.
This type alone never grants structural provenance. -/
structure StructuralRegistrationEvidence (theoremName : Name) (arena : StructuralArena.{u})
    (unit : StructuralTheoremUnit.{u, v} arena)
    (catalogValue : StructuralCatalog.{u, v, w} arena) (index : catalogValue.Index)
    (statement : Prop) : Prop where
  membership : catalogValue.theoremAt index = unit
  statement_eq : unit.Statement = statement

/-- A directionally explicit bounded comparison. The reverse direction is a
separate transfer obligation, checked only for the transferred constructor. -/
structure BoundedTruncationFamily (statement : Prop) where
  arena : Nat → Arena.{u}
  approximation : Nat → Prop
  restrict : ∀ bound, statement → approximation bound

/-- A named elaboration observation, not a mathematical impossibility claim.
The census verifies absence of registered realizations in its import closure.
Reasons about a known carrier must name that carrier explicitly. -/
structure UnreachableElaborationEvidence (statement : Prop) where
  reason : UnreachableReason
  candidateArena : Option Name
  explanation : String
  failedObligation : Option Name := none

namespace DispositionCensus

/-- Judge-owned provenance, retained without proposition normalization.
The section 23.6 payload types remain unchanged. -/
structure StructuralProvenanceEntry where
  theoremName : Name
  lawArenaConst : Name
  realizationConst : Name
  unitConst : Name
  statementExpr : Expr
  proofExpr : Expr
  levelParams : List Name
  certificateName : Name
  registrationModule : Name
  canonicalArena : Name
  deriving Inhabited

private initialize structuralRegistry :
    SimplePersistentEnvExtension StructuralProvenanceEntry (Array StructuralProvenanceEntry) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := Array.push
    addImportedFn := fun entries => entries.foldl (· ++ ·) #[] }

private def failClass (key : StatementKey) (className invalid : String) : MetaM α :=
  throwError (classError key.theoremName className invalid)

private def constant (key : StatementKey) (className field : String)
    (name : Name) : MetaM Expr := do
  unless (← getEnv).contains name do
    failClass key className field
  let info ← getConstInfo name
  if info.isUnsafe then failClass key className field
  let axioms ← collectAxioms name
  unless axioms.all (#[`propext, `Classical.choice, `Quot.sound].contains ·) do
    failClass key className s!"{field}.axioms"
  mkConstWithFreshMVarLevels name

private def typed (key : StatementKey) (className field : String)
    (name : Name) (expected : Expr) : MetaM Expr := do
  let value ← constant key className field name
  unless ← isDefEq (← inferType value) expected do
    failClass key className field
  checkWithKernel value
  return value

private def canonicalArgument (key : StatementKey) (actual : Expr)
    (expected : Name) : MetaM Unit := do
  unless actual.isConstOf expected do
    throwError (identityError key.theoremName "canonical_arena"
      (actual.getAppFn.constName?.map Name.toString |>.getD "noncanonical-expression")
      expected.toString)

private def validateFinite (root : Name) (key : StatementKey)
    (payload : FiniteOccurrenceDisposition key) : MetaM Unit := do
  let env ← getEnv
  let candidates := InformationRegistry.entries env |>.filter fun entry =>
    entry.theoremName == key.theoremName &&
      entry.canonicalObjectArenaName == payload.canonicalArena
  let some registration := candidates[0]?
    | throwError (identityError key.theoremName "canonical_arena" "registered-arena"
        payload.canonicalArena.toString)
  match ← validatePersistedEntry env registration with
  | .error message => throwError message
  | .ok () => pure ()
  unless payload.registration == registration.unitName do
    throwError (identityError key.theoremName "registration" registration.unitName.toString
      payload.registration.toString)
  unless payload.realization == registration.realizationName do
    throwError (identityError key.theoremName "realization" registration.realizationName.toString
      payload.realization.toString)
  let some sealed := (SealRecords.occurrencesForRoot env root).find? fun occurrence =>
      occurrence.theoremName == key.theoremName && occurrence.objectArenaName == payload.canonicalArena
    | failClass key "finite_occurrence" "maximal_catalog_seal"
  let certificate ← constant key "finite_occurrence" "seal_certificate" sealed.certificateName
  checkWithKernel certificate
  let lawArena ← mkConstWithFreshMVarLevels registration.arenaName
  let arena ← mkAppM ``PrimitiveLawArena.toArena #[lawArena]
  let _ ← typed key "finite_occurrence" "nondegeneracy_certificate"
    payload.nondegeneracyCertificate (← mkAppM ``Arena.Nondegenerate #[arena])
  let _ ← typed key "finite_occurrence" "state_enumeration_certificate"
    payload.stateEnumerationCertificate (← mkAppM ``Arena.StateEnumeration #[arena])

/-- Module ownership and transitive imports come from Lean's elaborated environment. -/
private def rootModules (env : Environment) (root : Name) : Array Name := Id.run do
  let mut closure := #[]
  let mut visited : Std.HashSet Name := {root}
  let mut pending := #[root]
  for _ in [:env.header.moduleNames.size + 1] do
    let some name := pending.back? | return closure
    pending := pending.pop
    closure := closure.push name
    let imports := if name == env.header.mainModule then env.header.imports else
      match env.getModuleIdx? name with
      | some index => env.header.moduleData[index.toNat]!.imports
      | none => #[]
    for item in imports do
      unless visited.contains item.module do
        visited := visited.insert item.module
        pending := pending.push item.module
  return closure

private def inRoot (env : Environment) (modules : Array Name) (name : Name) : Bool :=
  env.contains name && modules.contains
    ((env.getModuleIdxFor? name).map (env.header.moduleNames[·.toNat]!)
      |>.getD env.header.mainModule)

private def structuralRegistrations (modules : Array Name) : MetaM (Array (Name × Expr)) := do
  let mut result := #[]
  for (name, info) in (← getEnv).constants.toList do
    if info.type.isAppOfArity ``StructuralRegistrationEvidence 6 &&
        inRoot (← getEnv) modules name then
      let registration ← mkConstWithFreshMVarLevels name
      result := result.push (name, ← inferType registration)
  return result.qsort fun left right => left.1.toString < right.1.toString

open Elab Command Term

/-- Generate the statement, proof declaration and compiled unit as one transaction.
There is no command that registers a pre-existing theorem. -/
elab "structural_theorem " theoremId:ident " in " lawArenaId:ident
    " realization " realizationTerm:term " nondegeneracy " certificateId:ident
    " := " proofTerm:term : command => do
  let rawName := theoremId.getId.eraseMacroScopes
  let currentNamespace ← getCurrNamespace
  let theoremName := if (`_root_).isPrefixOf rawName then
      rawName.replacePrefix `_root_ .anonymous else currentNamespace ++ rawName
  let realizationName := theoremName.str "__structural_realization"
  let unitName := theoremName.str "__structural_unit"
  let before ← getEnv
  for name in [theoremName, realizationName, unitName] do
    if before.contains name then throwError "structural declaration already exists: {name}"
  try
    let lawArenaName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo lawArenaId
    let certificateName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo certificateId
    let entry ← liftTermElabM do
      let key : StatementKey := ⟨theoremName, ""⟩
      let className := "structural_occurrence"
      let lawArena ← constant key className "law_registration" lawArenaName
      let lawType ← inferType lawArena
      unless lawType.isAppOfArity ``StructuralPrimitiveLawArena 1 &&
          lawType.getAppArgs[0]!.isConst do
        failClass key className "law_registration.arena"
      let arena := lawType.getAppArgs[0]!
      let canonicalArena := arena.constName!
      for entry in structuralRegistry.getState before do
        if entry.canonicalArena == canonicalArena && entry.lawArenaConst != lawArenaName then
          failClass key className "realization.canonical_law_arena"
      let _ ← typed key className "law.nondegeneracy" certificateName
        (← mkAppM ``StructuralPrimitiveLawArena.Nondegenerate #[lawArena])
      let signature ← mkAppM ``StructuralPrimitiveLawArena.signature #[lawArena]
      let realizationType ← mkAppM ``StructuralPrimitiveRealization #[arena, signature]
      let realized ← elabTermEnsuringType realizationTerm realizationType
      synthesizeSyntheticMVarsNoPostponing
      let realizationType ← levelMVarToParam (← instantiateMVars realizationType)
      let realized ← levelMVarToParam (← instantiateMVars realized)
      let realizationParams := (collectLevelParams
        (collectLevelParams {} realizationType) realized).params.toList
      addAndCompile <| .defnDecl {
        name := realizationName, levelParams := realizationParams
        type := realizationType, value := realized, hints := .abbrev, safety := .safe }
      let realizationConst := Lean.mkConst realizationName (realizationParams.map Lean.Level.param)
      let lawArena ← instantiateMVars lawArena
      -- Retain this constructed tree, not a re-elaboration or a normal form.
      let statement ← mkAppM ``StructuralPrimitiveLawArena.Law #[lawArena, realizationConst]
      let proof ← elabTermEnsuringType proofTerm statement
      synthesizeSyntheticMVarsNoPostponing
      let statement ← levelMVarToParam (← instantiateMVars statement)
      let proof ← levelMVarToParam (← instantiateMVars proof)
      let levelParams := (collectLevelParams (collectLevelParams {} statement) proof).params.toList
      addAndCompile <| .thmDecl {
        name := theoremName, levelParams, type := statement, value := proof }
      let theoremConst := Lean.mkConst theoremName (levelParams.map Lean.Level.param)
      let _ ← constant key className "theorem" theoremName
      let unit ← mkAppM ``StructuralPrimitiveRealization.toTheoremUnit
        #[realizationConst, statement, theoremConst]
      let unitType ← instantiateMVars (← inferType unit)
      let unit ← instantiateMVars unit
      let unitParams := (collectLevelParams (collectLevelParams {} unitType) unit).params.toList
      addAndCompile <| .defnDecl {
        name := unitName, levelParams := unitParams, type := unitType, value := unit
        hints := .abbrev, safety := .safe }
      checkWithKernel theoremConst
      checkWithKernel (mkConst unitName (unitParams.map Lean.Level.param))
      return ({
        theoremName := theoremName
        lawArenaConst := lawArenaName
        realizationConst := realizationName
        unitConst := unitName
        statementExpr := statement
        proofExpr := proof
        levelParams := levelParams
        certificateName := certificateName
        registrationModule := before.header.mainModule
        canonicalArena := canonicalArena } : StructuralProvenanceEntry)
    modifyEnv fun env => structuralRegistry.addEntry env entry
  catch error =>
    setEnv before
    throw error

private def validateStructuralProvenance (root : Name) (head : String) (modules : Array Name)
    (key : StatementKey) (payload : StructuralOccurrenceDisposition key) : MetaM Unit := do
  let className := "structural_occurrence"
  let env ← getEnv
  let entries := (structuralRegistry.getState env).filter (·.theoremName == key.theoremName)
  unless entries.size == 1 do failClass key className "realization.provenance"
  let entry := entries[0]!
  unless modules.contains entry.registrationModule && inRoot env modules key.theoremName do
    throwError (censusError head "root" s!"import-closure-containing:{key.theoremName}" root.toString)
  let info ← getConstInfo key.theoremName
  unless info.levelParams.length == entry.levelParams.length do
    failClass key className "realization.provenance"
  let levels := entry.levelParams.map Level.param
  let actualType := info.type.instantiateLevelParams info.levelParams levels
  unless actualType == entry.statementExpr do failClass key className "realization.provenance"
  let some proof := info.value? (allowOpaque := true)
    | failClass key className "realization.provenance"
  unless proof.instantiateLevelParams info.levelParams levels == entry.proofExpr do
    failClass key className "realization.provenance"
  let statementArgs := entry.statementExpr.getAppArgs
  unless entry.statementExpr.isAppOfArity ``StructuralPrimitiveLawArena.Law 3 &&
      statementArgs[0]!.isConstOf entry.canonicalArena &&
      statementArgs[1]!.isConstOf entry.lawArenaConst &&
      statementArgs[2]!.isConstOf entry.realizationConst do
    failClass key className "realization.canonical_law_arena"
  unless payload.realization == entry.realizationConst do
    failClass key className "realization.provenance"
  canonicalArgument key (mkConst entry.canonicalArena) payload.canonicalArena
  for (field, name) in [("realization.law_arena", entry.lawArenaConst),
      ("realization", entry.realizationConst), ("realization.unit", entry.unitConst),
      ("realization.law_nondegeneracy", entry.certificateName)] do
    let value ← constant key className field name
    unless inRoot env modules name do failClass key className s!"{field}.root_membership"
    checkWithKernel value
  let lawArena ← mkConstWithFreshMVarLevels entry.lawArenaConst
  let lawType ← inferType lawArena
  unless lawType.isAppOfArity ``StructuralPrimitiveLawArena 1 &&
      lawType.getAppArgs[0]!.isConstOf entry.canonicalArena do
    failClass key className "realization.canonical_law_arena"
  for other in structuralRegistry.getState env do
    if other.canonicalArena == entry.canonicalArena &&
        other.lawArenaConst != entry.lawArenaConst then
      failClass key className "realization.canonical_law_arena"
  let _ ← typed key className "realization.law_nondegeneracy" entry.certificateName
    (← mkAppM ``StructuralPrimitiveLawArena.Nondegenerate #[lawArena])
  let registration ← constant key className "registration" payload.registration
  let registrationType ← inferType registration
  unless registrationType.isAppOfArity ``StructuralRegistrationEvidence 6 do
    failClass key className "registration"
  unless registrationType.getAppArgs[2]!.isConstOf entry.unitConst do
    failClass key className "realization.compiled_kernels"

private def validateStructural (root : Name) (head : String) (modules : Array Name)
    (registrations : Array (Name × Expr)) (key : StatementKey)
    (theoremProof statement : Expr) (payload : StructuralOccurrenceDisposition key) : MetaM Unit := do
  let className := "structural_occurrence"
  validateStructuralProvenance root head modules key payload
  unless inRoot (← getEnv) modules payload.registration do
    failClass key className "registration.root_membership"
  let registration ← constant key className "registration" payload.registration
  let registrationType ← inferType registration
  unless registrationType.isAppOfArity ``StructuralRegistrationEvidence 6 do
    failClass key className "registration"
  let args := registrationType.getAppArgs
  let registeredName : Name ← reduceEval args[0]!
  unless registeredName == key.theoremName do
    throwError (identityError key.theoremName "theorem_name" registeredName.toString
      key.theoremName.toString)
  canonicalArgument key args[1]! payload.canonicalArena
  unless ← isDefEq args[5]! statement do failClass key className "registration.statement"
  let unit := args[2]!
  let catalogValue := args[3]!
  let index := args[4]!
  unless catalogValue.isConst do failClass key className "canonical_catalog"
  for (field, name) in [("theorem", key.theoremName), ("canonical_arena", payload.canonicalArena),
      ("canonical_catalog", catalogValue.constName!), ("realization", payload.realization),
      ("strictness_certificate", payload.strictnessCertificate),
      ("witness_certificate", payload.witnessCertificate)] do
    if (← getEnv).contains name && !inRoot (← getEnv) modules name then
      failClass key className s!"{field}.root_membership"
  let realized ← constant key className "realization" payload.realization
  let realizationType ← inferType realized
  unless realizationType.isAppOfArity ``StructuralPrimitiveRealization 2 do
    failClass key className "realization"
  unless ← isDefEq realizationType.getAppArgs[0]! args[1]! do
    failClass key className "realization.arena"
  checkWithKernel realized
  let compiled ← mkAppM ``StructuralPrimitiveRealization.toTheoremUnit
    #[realized, statement, theoremProof]
  unless ← isDefEq unit compiled do failClass key className "realization.compiled_kernels"
  let strictness ← mkAppM ``StructuralCatalog.StructurallyLowersEscape #[catalogValue, index]
  let witnessType ← mkAppM ``StructuralStrictnessCertificate #[catalogValue, index]
  for (field, name, expected) in
      [("strictness_certificate", payload.strictnessCertificate, strictness),
       ("witness_certificate", payload.witnessCertificate, witnessType)] do
    unless (← getEnv).contains name do
      throwError s!"IE-C038 MissingStructuralWitness theorem={key.theoremName} \
arena={payload.canonicalArena} missing={field}"
    let value ← constant key className field name
    unless ← isDefEq (← inferType value) expected do
      throwError s!"IE-C038 MissingStructuralWitness theorem={key.theoremName} \
arena={payload.canonicalArena} missing={field}"
    checkWithKernel value
  let peers := registrations.filter fun (_, type) =>
    type.getAppArgs[1]!.isConstOf payload.canonicalArena
  let indexType ← mkAppM ``StructuralCatalog.Index #[catalogValue]
  let indexFintype ← mkAppM ``StructuralCatalog.indexFintype #[catalogValue]
  let cardinality ← mkAppOptM ``Fintype.card #[some indexType, some indexFintype]
  let size : Nat ← reduceEval cardinality
  unless size == peers.size do failClass key className "maximal_catalog_membership"
  let indexDecidableEq ← mkAppM ``StructuralCatalog.indexDecidableEq #[catalogValue]
  withLetDecl `censusIndexDecidableEq (← inferType indexDecidableEq) indexDecidableEq fun inst =>
    withNewLocalInstances #[inst] 0 do
      for i in [:peers.size] do
        let peerArgs := peers[i]!.2.getAppArgs
        unless peerArgs[3]!.isConstOf catalogValue.constName! &&
            (← isDefEq peerArgs[3]! catalogValue) do
          failClass key className "split_canonical_catalog"
        for j in [:i] do
          let peerName : Name ← reduceEval peerArgs[0]!
          let previousName : Name ← reduceEval peers[j]!.2.getAppArgs[0]!
          if peerName == previousName then failClass key className "duplicate_structural_registration"
          let distinct := mkNot (← mkEq peerArgs[4]! peers[j]!.2.getAppArgs[4]!)
          try
            checkWithKernel (← mkDecideProof distinct)
          catch _ => failClass key className "duplicate_catalog_index"

private def validateBounded (key : StatementKey) (statement : Expr)
    (payload : BoundedFiniteTruncationDisposition key) : MetaM Unit := do
  let className := "bounded_finite_truncation"
  let family ← constant key className "truncation_family" payload.truncationFamily
  let familyType ← inferType family
  unless familyType.isAppOfArity ``BoundedTruncationFamily 1 do
    failClass key className "truncation_family"
  unless ← isDefEq familyType.getAppArgs[0]! statement do
    failClass key className "truncation_family.statement"
  let approximation ← mkAppM ``BoundedTruncationFamily.approximation #[family, mkNatLit payload.bound]
  let _ ← typed key className "comparison_statement" payload.comparisonStatement
    (← mkArrow statement approximation)
  match payload.certification with
  | .reportOnly => pure ()
  | .transferred theoremName =>
    let _ ← typed key className "transfer_theorem" theoremName (← mkArrow approximation statement)
    pure ()

private def validateUnreachable (modules : Array Name) (registrations : Array (Name × Expr))
    (key : StatementKey) (statement : Expr) (payload : UnreachableDisposition key) : MetaM Unit := do
  let className := "unreachable"
  let evidence ← typed key className "evidence" payload.evidence
    (← mkAppM ``UnreachableElaborationEvidence #[statement])
  let evidence ← whnf evidence
  unless evidence.isAppOfArity ``UnreachableElaborationEvidence.mk 5 do
    failClass key className "evidence"
  let args := evidence.getAppArgs
  let expectedReason := match payload.reason with
    | .noCanonicalObjectCarrier => ``UnreachableReason.noCanonicalObjectCarrier
    | .noFinitePrimitiveBundle => ``UnreachableReason.noFinitePrimitiveBundle
    | .noFaithfulPrimitiveRealization => ``UnreachableReason.noFaithfulPrimitiveRealization
  unless ← isDefEq args[1]! (mkConst expectedReason) do failClass key className "reason"
  let explanation : String ← reduceEval args[3]!
  if explanation.trimAscii.toString.isEmpty then failClass key className "evidence.explanation"
  let obligationOption ← whnf args[4]!
  unless obligationOption.isAppOfArity ``Option.some 2 do
    failClass key className "evidence.failed_obligation"
  let obligationName : Name ← reduceEval obligationOption.getAppArgs[1]!
  let obligation ← constant key className "evidence.failed_obligation" obligationName
  let obligationType ← inferType obligation
  let obligationArgs := obligationType.getAppArgs
  let candidateOption ← whnf args[2]!
  let candidateName : Option Name ←
    if candidateOption.isAppOfArity ``Option.some 2 then do
      let name : Name ← reduceEval candidateOption.getAppArgs[1]!
      pure (some name)
    else pure none
  match payload.reason with
  | .noCanonicalObjectCarrier =>
    unless obligationType.isAppOfArity ``ClosedNumericalObligation 3 && candidateName.isNone do
      failClass key className "evidence.failed_obligation"
    for value in [obligationArgs[1]!, obligationArgs[2]!] do
      unless (← whnf value).rawNatLit?.isSome do failClass key className "evidence.closed_numeral"
    unless ← isDefEq statement (← mkEq obligationArgs[1]! obligationArgs[2]!) do
      failClass key className "evidence.statement"
  | .noFinitePrimitiveBundle =>
    unless obligationType.isAppOfArity ``InfinitePrimitiveObligation 6 do
      failClass key className "evidence.failed_obligation"
    let some candidateName := candidateName | failClass key className "candidate_arena"
    canonicalArgument key obligationArgs[1]! candidateName
    unless ← isDefEq obligationArgs[5]! statement do failClass key className "evidence.statement"
  | .noFaithfulPrimitiveRealization =>
    unless obligationType.isAppOfArity ``UnfaithfulPrimitiveObligation 5 do
      failClass key className "evidence.failed_obligation"
    let some candidateName := candidateName | failClass key className "candidate_arena"
    canonicalArgument key obligationArgs[1]! candidateName
    unless ← isDefEq obligationArgs[4]! statement do failClass key className "evidence.statement"
  let recordedTheorem : Name ← reduceEval obligationArgs[0]!
  unless recordedTheorem == key.theoremName do failClass key className "evidence.theorem"
  checkWithKernel obligation
  if (InformationRegistry.entries (← getEnv)).any (·.theoremName == key.theoremName) then
    failClass key className "registered_realization"
  if (structuralRegistry.getState (← getEnv)).any (fun entry =>
      entry.theoremName == key.theoremName && modules.contains entry.registrationModule) then
    failClass key className "registered_structural_realization"
  for (_, type) in registrations do
    let registeredName : Name ← reduceEval type.getAppArgs[0]!
    if registeredName == key.theoremName then
      failClass key className "registered_structural_realization"
  let candidate ← whnf args[2]!
  match payload.reason with
  | .noCanonicalObjectCarrier =>
    unless candidate.isAppOfArity ``Option.none 1 do
      failClass key className "candidate_arena"
  | _ =>
    unless candidate.isAppOfArity ``Option.some 2 do failClass key className "candidate_arena"
    let name : Name ← reduceEval candidate.getAppArgs[1]!
    let arena ← constant key className "candidate_arena" name
    let type ← inferType arena
    unless type.isConstOf ``Arena || type.isConstOf ``StructuralArena ||
        type.isConstOf ``PrimitiveLawArena do failClass key className "candidate_arena"

/-- Checks declarations and certificate types directly in the elaborated environment.
It never reads a seal artifact or manufactures a carrier from statement syntax. -/
def validateEvidence (root : Name) (inventory : DispositionInventory) : MetaM Unit := do
  let env ← getEnv
  unless root == env.header.mainModule || env.header.moduleNames.contains root do
    throwError (censusError inventory.headSha "root" "existing-module" root.toString)
  let modules := rootModules env root
  let registrations ← structuralRegistrations modules
  for entry in inventory.sortedEntries do
    let key := entry.1
    let theoremExpr ← constant key entry.2.className "theorem" key.theoremName
    unless (← getConstInfo key.theoremName).isTheorem do
      failClass key entry.2.className "theorem"
    let statement ← inferType theoremExpr
    match entry.2 with
    | .finiteOccurrence payload => validateFinite root key payload
    | .structuralOccurrence payload =>
      validateStructural root inventory.headSha modules registrations key theoremExpr statement payload
    | .boundedFiniteTruncation payload => validateBounded key statement payload
    | .unreachable payload =>
      unless inRoot env modules key.theoremName do
        throwError (censusError inventory.headSha "root"
          s!"import-closure-containing:{key.theoremName}" root.toString)
      validateUnreachable modules registrations key statement payload

end DispositionCensus

end LeanInformationAudit
