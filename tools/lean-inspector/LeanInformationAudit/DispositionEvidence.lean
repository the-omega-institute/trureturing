import LeanInformationAudit.AnalysisDisposition
import LeanInformationAudit.SealCommand
import LeanInformationAudit.StructuralRealization

namespace LeanInformationAudit

open Lean Meta
open D5.S3.ConceptDynamics.InformationEscape

universe u v w

/-- A concrete declaration of this type registers a structural occurrence.
The catalog and arena arguments must be canonical declarations. -/
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
      result := result.push (name, info.type)
  return result.qsort fun left right => left.1.toString < right.1.toString

private def validateStructural (modules : Array Name)
    (registrations : Array (Name × Expr)) (key : StatementKey)
    (statement : Expr) (payload : StructuralOccurrenceDisposition key) : MetaM Unit := do
  let className := "structural_occurrence"
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
  let realizationProof ← constant key className "realization" payload.realization
  let realizationType ← inferType realizationProof
  unless realizationType.isAppOfArity ``StructuralLegacyPrimitiveRealization 4 do
    failClass key className "realization"
  let realizationArgs := realizationType.getAppArgs
  unless ← isDefEq realizationArgs[0]! args[1]! do failClass key className "realization.arena"
  unless ← isDefEq realizationArgs[2]! statement do failClass key className "realization.statement"
  checkWithKernel realizationProof
  let theoremProof ← mkConstWithFreshMVarLevels key.theoremName
  let compiled ← mkAppM ``StructuralPrimitiveRealization.toTheoremUnit
    #[realizationArgs[3]!, statement, theoremProof]
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
        unless peerArgs[3]! == catalogValue do failClass key className "split_canonical_catalog"
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

private def validateUnreachable (registrations : Array (Name × Expr))
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
    | .structuralOccurrence payload => validateStructural modules registrations key statement payload
    | .boundedFiniteTruncation payload => validateBounded key statement payload
    | .unreachable payload => validateUnreachable registrations key statement payload

end DispositionCensus

end LeanInformationAudit
