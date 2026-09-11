import LeanInformationAudit.RegistryTypes
import LeanInformationAudit.Census.Report
import LeanInformationAudit.Census.Ownership
import LeanInformationAudit.SealCommand
import LeanInformationAudit.StructuralRealization
import LeanInformationAudit.Sha256
import Lean.Parser.Module

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

/-- Named evidence for a certified closed unreachable reason, not an
`AnalysisObservation` or a general mathematical impossibility claim. Admission
requires a matching reason, a nonempty explanation, and `failedObligation = some
name` naming a kernel-checked, reason-specific obligation tied to the same theorem
and statement: `ClosedNumericalObligation`, `InfinitePrimitiveObligation`, or
`UnfaithfulPrimitiveObligation`, respectively. Reasons about a known carrier must
name it in `candidateArena`; the no-carrier reason requires `none`.
The census also checks absence of registered realizations in its import closure,
but registry absence alone cannot produce this evidence. -/
structure UnreachableElaborationEvidence (statement : Prop) where
  reason : UnreachableReason
  candidateArena : Option Name
  explanation : String
  failedObligation : Option Name := none

namespace DispositionCensus

private initialize structuralRegistry :
    SimplePersistentEnvExtension StructuralProvenanceEntry (Array StructuralProvenanceEntry) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := Array.push
    addImportedFn := fun entries => entries.foldl (· ++ ·) #[] }

/-- Read-only access for exhaustive registration queries. -/
def structuralProvenanceEntries (env : Environment) : Array StructuralProvenanceEntry :=
  structuralRegistry.getState env

private def failClass (key : StatementKey) (className invalid : String) : MetaM α :=
  throwError (classError key.theoremName className invalid)

private def checkedConstant (key : StatementKey) (className field : String)
    (name : Name) : MetaM Expr := do
  unless (← getEnv).contains name do
    failClass key className field
  let info ← getConstInfo name
  if info.isUnsafe then failClass key className field
  let axioms ← collectAxioms name
  unless axioms.all (#[`propext, `Classical.choice, `Quot.sound].contains ·) do
    failClass key className s!"{field}.axioms"
  mkConstWithFreshMVarLevels name

private def constant (modules : Array Name) (key : StatementKey) (className field : String)
    (name : Name) : MetaM Expr := do
  unless ← CensusOwnership.nameInScope (← getEnv) modules name do
    failClass key className s!"{field}.root_membership"
  checkedConstant key className field name

private def typed (modules : Array Name) (key : StatementKey) (className field : String)
    (name : Name) (expected : Expr) : MetaM Expr := do
  let value ← constant modules key className field name
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

/-- Module ownership and transitive imports come from Lean's elaborated environment. -/
def censusRootModules (env : Environment) (root : Name) : Array Name := Id.run do
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

/-- An imported seal is usable only when its catalog covers every in-scope peer. -/
def finiteSealInScope? (env : Environment) (modules : Array Name)
    (theoremName arena : Name) : Option Name := Id.run do
  let peers := (InformationRegistry.entries env).filter fun entry =>
    modules.contains entry.registrationModuleName && entry.canonicalObjectArenaName == arena
  for record in SealRecords.entries env do
    if !modules.contains record.catalog.rootId || record.catalog.arenaName != arena then continue
    unless record.theorems.size == peers.size && peers.all (fun peer =>
        record.theorems.any (·.theoremName == peer.theoremName)) do continue
    if let some occurrence := record.theorems.find? (·.theoremName == theoremName) then
      return some occurrence.certificateName
  return none

private def validateFinite (modules : Array Name) (key : StatementKey)
    (payload : FiniteOccurrenceDisposition key) : MetaM Unit := do
  let env ← getEnv
  let candidates := InformationRegistry.entries env |>.filter fun entry =>
    modules.contains entry.registrationModuleName && entry.theoremName == key.theoremName &&
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
  for (field, name) in [("canonical_arena", payload.canonicalArena),
      ("registration", payload.registration), ("realization", payload.realization),
      ("law_arena", registration.arenaName)] do
    discard <| constant modules key "finite_occurrence" field name
  let some sealed := finiteSealInScope? env modules key.theoremName payload.canonicalArena
    | failClass key "finite_occurrence" "maximal_catalog_seal"
  let certificate ← constant modules key "finite_occurrence" "seal_certificate" sealed
  checkWithKernel certificate
  let lawArena ← mkConstWithFreshMVarLevels registration.arenaName
  let arena ← mkAppM ``PrimitiveLawArena.toArena #[lawArena]
  let _ ← typed modules key "finite_occurrence" "nondegeneracy_certificate"
    payload.nondegeneracyCertificate (← mkAppM ``Arena.Nondegenerate #[arena])
  let _ ← typed modules key "finite_occurrence" "state_enumeration_certificate"
    payload.stateEnumerationCertificate (← mkAppM ``Arena.StateEnumeration #[arena])

private def inRoot (env : Environment) (modules : Array Name) (name : Name) : IO Bool :=
  CensusOwnership.nameInScope env modules name

private def structuralRegistrations (modules : Array Name) : MetaM (Array (Name × Expr)) := do
  let mut result := #[]
  for (name, info) in (← getEnv).constants.toList do
    if info.type.isAppOfArity ``StructuralRegistrationEvidence 6 then
      if ← inRoot (← getEnv) modules name then
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
      let modules := censusRootModules (← getEnv) (← getEnv).header.mainModule
      let key : StatementKey := ⟨theoremName, ""⟩
      let className := "structural_occurrence"
      let lawArena ← constant modules key className "law_registration" lawArenaName
      let lawType ← inferType lawArena
      unless lawType.isAppOfArity ``StructuralPrimitiveLawArena 1 &&
          lawType.getAppArgs[0]!.isConst do
        failClass key className "law_registration.arena"
      let arena := lawType.getAppArgs[0]!
      let canonicalArena := arena.constName!
      for entry in structuralRegistry.getState before do
        if entry.canonicalArena == canonicalArena && entry.lawArenaConst != lawArenaName then
          failClass key className "realization.canonical_law_arena"
      let _ ← typed modules key className "law.nondegeneracy" certificateName
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
      let _ ← constant modules key className "theorem" theoremName
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
        canonicalArena := canonicalArena
        lawArenaSyntax := lawArenaId.raw.reprint.getD ""
        realizationSyntax := realizationTerm.raw.reprint.getD "" } : StructuralProvenanceEntry)
    modifyEnv fun env => structuralRegistry.addEntry env entry
  catch error =>
    setEnv before
    throw error

private def sourceDeclName (ns raw : Name) : Name :=
  if (`_root_).isPrefixOf raw then raw.replacePrefix `_root_ .anonymous else ns ++ raw

private def sourceOpenDecls (env : Environment) (ns : Name) (opens : List OpenDecl)
    (decl : TSyntax ``Parser.Command.openDecl) : List OpenDecl := Id.run do
  let mut result := opens
  let resolve := Lean.ResolveName.resolveNamespace env ns opens
  match decl with
  | `(Parser.Command.openDecl| $names*) =>
    for name in names do
      for resolved in Lean.ResolveName.resolveNamespace env ns result name.getId do
        result := .simple resolved [] :: result
  | `(Parser.Command.openDecl| $name hiding $ids*) =>
    for resolved in resolve name.getId do
      result := .simple resolved (ids.toList.map (·.getId)) :: result
  | `(Parser.Command.openDecl| $name ($ids*)) =>
    for resolved in resolve name.getId do
      for id in ids do result := .explicit id.getId (resolved ++ id.getId) :: result
  | `(Parser.Command.openDecl| $name renaming $[$froms -> $tos],*) =>
    for resolved in resolve name.getId do
      for (old, renamed) in froms.zip tos do
        result := .explicit renamed.getId (resolved ++ old.getId) :: result
  | _ => pure ()
  return result

/-- findLean uses the frontend's current source root followed by the ordered
LEAN_SRC_PATH from getSrcSearchPath. Lake builds do not set LEAN_SRC_PATH, so the
current root also resolves imports from the same library. For the main module
(including standalone probes), the resolved path must equal the input filename.
No source is elaborated. Nested commands, quotations and generated syntax do not
introduce declarations for this contract. Unparseable source fails closed. -/
private def validateProvenanceSyntax (modules : Array Name)
    (entry : StructuralProvenanceEntry) : MetaM ProvenanceSource := do
  let key : StatementKey := ⟨entry.theoremName, ""⟩
  let reject : MetaM ProvenanceSource :=
    failClass key "structural_occurrence" "realization.provenance.syntax"
  let env ← getEnv
  let owner := entry.registrationModule
  unless ← CensusOwnership.recordedModuleContainsTheorem env modules owner entry.theoremName do
    return ← reject
  try
    let mut searchPath ← getSrcSearchPath
    let inputPath ← IO.FS.realPath (← readThe Core.Context).fileName
    let mut base := inputPath
    for _ in env.header.mainModule.components do
      let some parent := base.parent | return ← reject
      base := parent
    searchPath := base :: searchPath
    let path ← IO.FS.realPath (← findLean searchPath owner)
    if owner == env.header.mainModule then
      unless path == inputPath do return ← reject
    let bytes ← IO.FS.readBinFile path
    let some source := String.fromUTF8? bytes | return ← reject
    let input := Parser.mkInputContext source path.toString
    let (_, initial, headerMessages) ← Parser.parseHeader input
    if headerMessages.hasErrors then return ← reject
    let mut state := initial
    let mut ns := Name.anonymous
    let mut opens : List OpenDecl := []
    let mut scopes : List (Name × List OpenDecl) := []
    let mut found := false
    repeat
      let (command, next, messages) := Parser.parseCommand input
        { env, options := ← getOptions, currNamespace := ns, openDecls := opens } state {}
      if messages.hasErrors then return ← reject
      if Parser.isTerminalCommand command then break
      if next.pos == state.pos then return ← reject
      state := next
      if command.isOfKind ``Parser.Command.namespace then
        scopes := (ns, opens) :: scopes
        ns := ns ++ command[1].getId
      else if command.isOfKind ``Parser.Command.section then
        scopes := (ns, opens) :: scopes
      else if command.isOfKind ``Parser.Command.end then
        let previous :: rest := scopes | return ← reject
        ns := previous.1
        opens := previous.2
        scopes := rest
      else if let `(command| open $decl:openDecl) := command then
        opens := sourceOpenDecls env ns opens decl
      else if command.isOfKind ``Parser.Command.declaration then
        let declaration := command[1]
        if declaration[1][0].isIdent &&
            sourceDeclName ns declaration[1][0].getId == entry.theoremName then
          return ← reject
      else if let `(command| structural_theorem $theoremId:ident in $lawId:ident
          realization $realizationTerm:term nondegeneracy $_:ident := $_:term) := command then
        if sourceDeclName ns theoremId.getId == entry.theoremName then
          if found then return ← reject
          unless lawId.raw.reprint == some entry.lawArenaSyntax &&
              entry.realizationConst == entry.theoremName.str "__structural_realization" &&
              realizationTerm.raw.reprint == some entry.realizationSyntax do
            return ← reject
          found := true
    unless found do return ← reject
    return {
      moduleName := owner
      path := path.toString
      sha256 := "sha256:" ++ Sha256.hex bytes }
  catch _ => reject

private def validateStructuralProvenance (root : Name) (head : String) (modules : Array Name)
    (key : StatementKey) (payload : StructuralOccurrenceDisposition key) : MetaM ProvenanceSource := do
  let className := "structural_occurrence"
  let env ← getEnv
  let occurrences := (structuralRegistry.getState env).filter (·.theoremName == key.theoremName)
  let entries := occurrences.filter (fun entry => modules.contains entry.registrationModule)
  if entries.isEmpty && !occurrences.isEmpty then
    throwError (censusError head "root" s!"import-closure-containing:{key.theoremName}" root.toString)
  unless entries.size == 1 do failClass key className "realization.provenance"
  let entry := entries[0]!
  unless modules.contains entry.registrationModule &&
      (← CensusOwnership.nameInScope env modules key.theoremName) do
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
    let value ← constant modules key className field name
    unless ← inRoot env modules name do failClass key className s!"{field}.root_membership"
    checkWithKernel value
  let lawArena ← mkConstWithFreshMVarLevels entry.lawArenaConst
  let lawType ← inferType lawArena
  unless lawType.isAppOfArity ``StructuralPrimitiveLawArena 1 &&
      lawType.getAppArgs[0]!.isConstOf entry.canonicalArena do
    failClass key className "realization.canonical_law_arena"
  for other in structuralRegistry.getState env do
    if modules.contains other.registrationModule && other.canonicalArena == entry.canonicalArena &&
        other.lawArenaConst != entry.lawArenaConst then
      failClass key className "realization.canonical_law_arena"
  let _ ← typed modules key className "realization.law_nondegeneracy" entry.certificateName
    (← mkAppM ``StructuralPrimitiveLawArena.Nondegenerate #[lawArena])
  let registration ← constant modules key className "registration" payload.registration
  let registrationType ← inferType registration
  unless registrationType.isAppOfArity ``StructuralRegistrationEvidence 6 do
    failClass key className "registration"
  unless registrationType.getAppArgs[2]!.isConstOf entry.unitConst do
    failClass key className "realization.compiled_kernels"
  validateProvenanceSyntax modules entry

private def validateStructural (root : Name) (head : String) (modules : Array Name)
    (registrations : Array (Name × Expr)) (key : StatementKey)
    (theoremProof statement : Expr) (payload : StructuralOccurrenceDisposition key) : MetaM ProvenanceSource := do
  let className := "structural_occurrence"
  let source ← validateStructuralProvenance root head modules key payload
  unless ← inRoot (← getEnv) modules payload.registration do
    failClass key className "registration.root_membership"
  let registration ← constant modules key className "registration" payload.registration
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
    if (← getEnv).contains name && !(← inRoot (← getEnv) modules name) then
      failClass key className s!"{field}.root_membership"
  let realized ← constant modules key className "realization" payload.realization
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
    let value ← constant modules key className field name
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
  return source

private def validateBounded (modules : Array Name) (key : StatementKey) (statement : Expr)
    (payload : BoundedFiniteTruncationDisposition key) : MetaM Unit := do
  let className := "bounded_finite_truncation"
  let family ← constant modules key className "truncation_family" payload.truncationFamily
  let familyType ← inferType family
  unless familyType.isAppOfArity ``BoundedTruncationFamily 1 do
    failClass key className "truncation_family"
  unless ← isDefEq familyType.getAppArgs[0]! statement do
    failClass key className "truncation_family.statement"
  let approximation ← mkAppM ``BoundedTruncationFamily.approximation #[family, mkNatLit payload.bound]
  let _ ← typed modules key className "comparison_statement" payload.comparisonStatement
    (← mkArrow statement approximation)
  match payload.certification with
  | .reportOnly => pure ()
  | .transferred theoremName =>
    let _ ← typed modules key className "transfer_theorem" theoremName (← mkArrow approximation statement)
    pure ()

private def validateUnreachable (modules : Array Name) (registrations : Array (Name × Expr))
    (key : StatementKey) (statement : Expr) (payload : UnreachableDisposition key) : MetaM Unit := do
  let className := "unreachable"
  let evidence ← typed modules key className "evidence" payload.evidence
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
  let obligation ← constant modules key className "evidence.failed_obligation" obligationName
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
  if (InformationRegistry.entries (← getEnv)).any (fun entry =>
      entry.theoremName == key.theoremName && modules.contains entry.registrationModuleName) then
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
    let arena ← constant modules key className "candidate_arena" name
    let type ← inferType arena
    unless type.isConstOf ``Arena || type.isConstOf ``StructuralArena ||
        type.isConstOf ``PrimitiveLawArena do failClass key className "candidate_arena"

private def validateObserved (head : String) (root : Name) (modules : Array Name)
    (registrations : Array (Name × Expr)) (key : StatementKey)
    (payload : AnalysisObservation key) : MetaM Unit := do
  unless payload.root == root do
    throwError (censusError head "root" root.toString payload.root.toString)
  ofExcept <| checkObservationStatus head payload
  let expectedModules := modules.qsort Name.quickLt
  let actualModules := payload.importScope.modules.qsort Name.quickLt
  unless actualModules == expectedModules do
    throwError (censusError head "import_scope" "root-import-closure" "module-set-mismatch")
  let env ← getEnv
  let actualOwner := env.getModuleIdxFor? key.theoremName |>.map
      (env.header.moduleNames[·.toNat]!) |>.getD env.header.mainModule
  unless ← CensusOwnership.recordedModuleContainsTheorem env modules
      payload.owningModule key.theoremName do
    throwError (censusError head "owning_module" actualOwner.toString payload.owningModule.toString)
  for candidate in payload.candidates do
    let finite := (InformationRegistry.entries env).any fun entry =>
      entry.theoremName == key.theoremName && modules.contains entry.registrationModuleName &&
        (entry.realizationName == candidate || entry.unitName == candidate)
    let structural := (structuralRegistry.getState env).any fun entry =>
      entry.theoremName == key.theoremName && modules.contains entry.registrationModule &&
        (entry.realizationConst == candidate || entry.unitConst == candidate)
    let mut registered := false
    for (name, type) in registrations do
      if name == candidate then
        let registeredName : Name ← reduceEval type.getAppArgs[0]!
        registered := registeredName == key.theoremName
    unless (← inRoot env modules candidate) && (finite || structural || registered) do
      throwError (censusError head "candidates" "matching-registration-or-realization"
        candidate.toString)

/-- Checks declaration records and certificates in the environment, then requires
structural_theorem source syntax as creation authority. It reads no seal artifact
and manufactures no carrier from statement syntax. Returns the source input closure. -/
def validateEvidenceSources (root : Name) (inventory : DispositionInventory)
    (scope : Option (Array Name) := none) :
    MetaM (Array ProvenanceSource) := do
  let env ← getEnv
  unless scope.isSome || root == env.header.mainModule || env.header.moduleNames.contains root do
    throwError (censusError inventory.headSha "root" "existing-module" root.toString)
  let modules := scope.getD (censusRootModules env root)
  let registrations ← structuralRegistrations modules
  let mut sources := #[]
  for entry in inventory.sortedEntries do
    let key := entry.1
    let theoremExpr ← checkedConstant key entry.2.className "theorem" key.theoremName
    unless (← getConstInfo key.theoremName).isTheorem do
      failClass key entry.2.className "theorem"
    let statement ← inferType theoremExpr
    match entry.2 with
    | .certified disposition =>
      match disposition with
      | .finiteOccurrence payload => validateFinite modules key payload
      | .structuralOccurrence payload =>
        let source ← validateStructural root inventory.headSha modules registrations
          key theoremExpr statement payload
        unless sources.contains source do sources := sources.push source
      | .boundedFiniteTruncation payload => validateBounded modules key statement payload
      | .unreachable payload =>
        unless ← CensusOwnership.theoremInScope env modules key.theoremName do
          throwError (censusError inventory.headSha "root"
            s!"import-closure-containing:{key.theoremName}" root.toString)
        validateUnreachable modules registrations key statement payload
    | .observed payload =>
      validateObserved inventory.headSha root modules registrations key payload
  return sources.qsort fun left right => left.moduleName.toString < right.moduleName.toString

/-- Validation-only interface; census publication also records the source hashes. -/
def validateEvidence (root : Name) (inventory : DispositionInventory)
    (scope : Option (Array Name) := none) : MetaM Unit := do
  discard <| validateEvidenceSources root inventory scope

end DispositionCensus

end LeanInformationAudit
