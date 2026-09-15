import D5.S3.ConceptDynamics.InformationEscape.ReifierTemplates
import LeanInformationAudit.SealCommand
import D5.S3.ConceptDynamics.InformationEscapeHierarchy.StructuralCatalog
import D5.S0.Tower.DBonacci.Substitution
import D5.S3.StatisticalMechanics.HardCore.SquareGridCoordinates

namespace LeanInformationAudit.Tests.ReifierShadow
open Lean Meta Elab Command
open D5.S3.ConceptDynamics.InformationEscape PointwiseRegistrationTemplates
open D5.S0.Tower.DBonacci.Substitution
open D5.S0.Tower.Tribonacci.Substitution (TribonacciGapLetter gapLetterSubstitution)
open D5.S3.StatisticalMechanics.HardCore.OrderedGridMemory
open D5.S3.StatisticalMechanics.HardCore.SquareGridCoordinates

-- Each arena plus its complete via form below is three authored physical lines.
def substitutionArena := pointwiseEqArena (Arena.ofFintype (Fin 3)) (List TribonacciGapLetter)
def recenterArena := pointwiseEqArena (Arena.ofFintype (Fin 3)) Point

private def viaForms : CommandElabM (Array Syntax) := do
  let substitution ← `(command| register_information_theorem gapLabelSubstitution_three_compatible via (D5.S3.ConceptDynamics.InformationEscape.ReifierTemplates.pointwise
    (fun label : Fin 3 => (gapLabelSubstitution 3 label.1).map tribonacciGapLetterOfLabel) (fun label => gapLetterSubstitution (tribonacciGapLetterOfLabel label.1))) in substitutionArena output_evidence (nontrivial_of_ne [] [.small] (by decide)))
  let recenter ← `(command| register_information_theorem recenter_direction via (D5.S3.ConceptDynamics.InformationEscape.ReifierTemplates.pointwise
    (fun d : Fin 3 => recenter d (direction d)) (fun _ => (0, 0))) in recenterArena)
  return #[substitution, recenter]

expect_information_occurrence gapLabelSubstitution_three_compatible in substitutionArena
  from "LeanInformationAudit.Tests.RegistrationGates.ReifierShadow"
expect_information_occurrence recenter_direction in recenterArena
  from "LeanInformationAudit.Tests.RegistrationGates.ReifierShadow"

/-- Actual consumer observations: identities/ownership, raw expressions, universes,
C048 payload types, axiom closures and complete provenance/semantic outcomes.
Certificate presence is intentionally separate: the manual entry has none. -/
def registrationObservations (e : InformationRegistryEntry) : MetaM (Array String × Array Expr) := do
  let mut scalars := #[reprStr (RegistrationReifier.occurrenceBinding e), reprStr e.catalogKind,
    reprStr e.localRegistrationNames, e.statementIdentity, reprStr e.occurrenceKey]
  let mut expressions := #[]
  for name in #[e.theoremName, e.unitName, e.realizationName, e.variationWitness, e.sensitivityWitness] do
    let info ← getConstInfo name
    scalars := scalars.push (reprStr info.levelParams)
    scalars := scalars.push (reprStr (← collectAxioms name))
    expressions := expressions.push info.type
    if name == e.unitName then
      expressions := expressions.push (info.value? (allowOpaque := true)).get!
  scalars := scalars.push (reprStr (← RegistrationGates.provenanceErrorCurrent
    e.registrationModuleName e.effectiveCatalogId e.theoremName e.realizationName))
  scalars := scalars.push (reprStr (← RegistrationGates.validateFinite e))
  return (scalars, expressions)

private def sealObservations : MetaM (Array String × Array Expr) := do
  let records := SealRecords.forRoot (← getEnv) (← getEnv).header.mainModule
  let mut scalars := #[← serializeSealArtifact records]
  let mut expressions := #[]
  for record in records do
    let c := record.catalog
    scalars := scalars ++ #[reprStr (c.rootId, c.catalogId, c.arenaName, c.catalogName),
      reprStr c.catalogKind, reprStr c.localSealNames, reprStr record.stateEnumeration]
    for unit in c.units do
      scalars := scalars.push (reprStr (unit.theoremName, unit.unitName, unit.realizationName,
        unit.registrationModuleName, unit.index))
    for name in #[c.catalogName] ++ record.stateEnumeration.toArray do
      let info ← getConstInfo name
      scalars := scalars.push (reprStr info.levelParams)
      expressions := expressions ++ #[info.type, info.value?.get!]
  return (scalars, expressions)

private def sameObservations (m d : Array String × Array Expr) : MetaM Bool := do
  unless m.1 == d.1 && m.2.size == d.2.size do return false
  for (a,b) in m.2.zip d.2 do
    unless ← RegistrationReifier.exact a b do return false
  return true

private def ownEntries : CoreM (Array InformationRegistryEntry) := do
  return InformationRegistry.entries (← getEnv) |>.filter (·.registrationModuleName == (← getEnv).header.mainModule)

/-- Independent manual expansion uses the old command, never the reifier producer.
Companion names match the derived convention to compare the same occurrences. -/
private def manual (form : Syntax) (wrapped : Bool) : CommandElabM Unit := do
  let theoremName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo form[1]
  let arenaName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo form[5]
  let unit := localCompanionName (← getEnv) theoremName theoremUnitSuffix
  let bridge := localCompanionName (← getEnv) theoremName primitiveRealizationSuffix
  let nd := unit.str "__nondegenerate"
  let sens := unit.str "__sensitivity"
  let vari := unit.str "__variation"
  let bundleName := unit.str "__manual_bundle"
  liftTermElabM do
    let descriptor ← Term.elabTerm form[3] none
    Term.synthesizeSyntheticMVarsNoPostponing
    let descriptor ← instantiateMVars descriptor
    let p := descriptor.getAppArgs
    let native := (← inferType descriptor).getAppArgs[2]!
    let arena := mkConst arenaName
    let source := (← getConstInfo theoremName).type
    let proof := fun name type value => addDecl (.thmDecl { name, levelParams := [], type, value })
    let bridgeProof ← if wrapped then mkAppM ``id #[descriptor] else pure descriptor
    proof bridge (← mkAppM ``LegacyPrimitiveRealization #[arena, source, native]) bridgeProof
    let ndType ← mkAppM ``Arena.Nondegenerate #[← mkAppM ``PrimitiveLawArena.toArena #[arena]]
    proof nd ndType (← mkDecideProof ndType)
    let expected ← mkAppM ``Nontrivial #[p[1]!]
    let outputInstance ← if form[6].getNumArgs == 0 then synthInstance expected else do
      let value ← Term.elabTerm form[6][1] (some expected)
      Term.synthesizeSyntheticMVarsNoPostponing
      instantiateMVars value
    proof sens (← mkAppM ``FiniteSlotSensitivity #[arena])
      (mkAppN (mkConst ``D5.S3.ConceptDynamics.InformationEscape.ReifierTemplates.sensitivity) (p.extract 0 5 ++ #[outputInstance, mkConst nd]))
    proof vari (← mkAppM ``FiniteLawVariation #[arena])
      (← mkAppM ``D5.S3.ConceptDynamics.InformationEscape.ReifierTemplates.variation #[arena, mkConst ``Bool.false, mkConst sens])
    let compiled ← compilePrimitiveBundle arena native
    let value ← mkAppOptM ``PrimitiveRealization.toPrimitiveBundle (compiled.getAppArgs.map some)
    let type ← inferType value
    addAndCompile (.defnDecl {
      name := bundleName, levelParams := [], type, value, hints := .abbrev, safety := .safe })
  let primitive := mkIdent bundleName
  let theoremId := mkIdent theoremName
  let arenaId := mkIdent arenaName
  let bridgeId := mkIdent bridge
  let variId := mkIdent vari
  let sensId := mkIdent sens
  elabCommand (← `(command| register_information_theorem $theoremId in $arenaId
    primitives $primitive:ident realization $bridgeId variation $variId sensitivity $sensId))
  unless InformationRegistry.hasTheorem (← getEnv) theoremName do
    throwError "manual lowering failed; generated_unit={(← getEnv).contains unit}"

elab "check_pointwise_shadow" : command => do
  let initial ← get
  let forms ← viaForms
  forms.forM (fun form => manual form false)
  let manualEntries ← liftCoreM ownEntries
  unless manualEntries.size == 2 do throwError "manual count"
  let manualObs ← liftTermElabM <| (manualEntries.mapM registrationObservations : MetaM _)
  let manifest := reprStr <| ExpectedOccurrenceManifest.declaredEntries (← getEnv) (← getEnv).header.mainModule
  elabCommand (← `(command| #seal_information_theory))
  if (← get).messages.hasErrors then throwError "manual seal command rejected"
  let manualSeal ← liftTermElabM <| sealObservations
  set initial
  forms.forM (fun form => manual form true)
  let wrappedEntries ← liftCoreM ownEntries
  let wrappedObs ← liftTermElabM <| (wrappedEntries.mapM registrationObservations : MetaM _)
  unless wrappedObs.size == manualObs.size do throwError "wrapped manual count"
  for (m, w) in manualObs.zip wrappedObs do
    unless ← liftTermElabM <| sameObservations m w do
      throwError "harmless bridge proof changed consumer observations"
  set initial
  forms.forM elabCommand
  let derivedEntries ← liftCoreM ownEntries
  unless derivedEntries.size == 2 do throwError "derived count"
  let derivedObs ← liftTermElabM <| (derivedEntries.mapM registrationObservations : MetaM _)
  unless manifest == reprStr (ExpectedOccurrenceManifest.declaredEntries (← getEnv) (← getEnv).header.mainModule) do
    throwError "independent manifest changed"
  for (m, d) in manualObs.zip derivedObs do
    unless ← liftTermElabM <| sameObservations m d do
      throwError "consumer observations differ (alpha-renaming only)"
  for entry in derivedEntries do
    liftTermElabM <| RegistrationReifier.validateDerivedCertificate entry
    unless entry.derivedCertificate.isSome do throwError "missing derived certificate"
  elabCommand (← `(command| #seal_information_theory))
  if (← get).messages.hasErrors then throwError "derived seal command rejected"
  let derivedSeal ← liftTermElabM <| sealObservations
  unless ← liftTermElabM <| sameObservations manualSeal derivedSeal do throwError "seal/catalog ordering or enumeration differs"
  logInfo "P1_SHADOW_EQUIVALENT registrations=2 manifest=equal raw=equal witnesses=equal seals=equal"

check_pointwise_shadow
end LeanInformationAudit.Tests.ReifierShadow
