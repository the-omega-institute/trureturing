import LeanInformationAudit.Tests.Census.RegisteredClosedTruth

open Lean LeanInformationAudit DispositionCensus
open Lean.Elab.Command

namespace LeanInformationAudit.Tests.Census.LawRegistry

private def tamperDeclaration (change : TSyntax `term) (certificate : Name) :
    CommandElabM Unit := do
  let env ← getEnv
  let some (replaceName, _) := env.constants.toList.find? (fun (name, _) =>
      privateToUserName? name == some `Lean.Environment.setCheckedSync)
    | throwError "private environment replacement not found"
  let replaceId := mkIdent replaceName
  let privateId (userName : Name) : CommandElabM Ident := do
    let some (name, _) := env.constants.toList.find? (fun (name, _) =>
        privateToUserName? name == some userName)
      | throwError "private fixture dependency missing: {userName}"
    return mkIdent name
  let constructor ← privateId `Lean.Kernel.Environment.mk
  let extensions ← privateId `Lean.Kernel.Environment.extensions
  let irExtensions ← privateId `Lean.Kernel.Environment.irBaseExts
  try
    elabCommand (← `(command| run_cmd do
      let .thmInfo info ← getConstInfo ``RegisteredClosedTruth.generated
        | throwError "generated theorem missing"
      let replacement := ($change) info
      modifyEnv fun current =>
        let kernel := current.toKernelEnv
        let constants := { kernel.constants with
          map₁ := kernel.constants.map₁.insert info.name (.thmInfo replacement) }
        ($replaceId) current (($constructor) constants kernel.quotInit kernel.diagnostics
          kernel.const2ModIdx (($extensions) kernel) (($irExtensions) kernel) kernel.header)
      let .thmInfo actual ← getConstInfo ``RegisteredClosedTruth.generated
        | throwError "tampered theorem missing"
      unless actual.type == replacement.type && actual.value == replacement.value do
        throwError "fixture did not replace the declaration"))
    expectRejectedCensus `LeanInformationAudit.Tests.Census.RegisteredClosedTruth
      ``RegisteredClosedTruth.positive certificate RegisteredClosedTruth.positive
      (classError ``RegisteredClosedTruth.generated "structural_occurrence" "realization.provenance")
  finally
    setEnv env

-- Fixture-only access to private metadata; production exposes only the generator.
private def tamper (change : TSyntax `term) (certificate : Name) (expected : String) :
    CommandElabM Unit := do
  let env ← getEnv
  let some (registryName, _) := env.constants.toList.find? (fun (name, _) =>
      privateToUserName? name == some `LeanInformationAudit.DispositionCensus.structuralRegistry)
    | throwError "private structural registry not found"
  let registryId := mkIdent registryName
  try
    elabCommand (← `(command| run_cmd
      modifyEnv fun current => ($registryId).modifyState current fun entries =>
        entries.map fun entry =>
          if entry.theoremName == ``RegisteredClosedTruth.generated then
            ($change) entry else entry))
    expectRejectedCensus `LeanInformationAudit.Tests.Census.RegisteredClosedTruth
      ``RegisteredClosedTruth.positive certificate RegisteredClosedTruth.positive expected
  finally
    setEnv env

/--
info: IE-C037 DispositionClassMismatch theorem=LeanInformationAudit.Tests.Census.RegisteredClosedTruth.generated class=structural_occurrence invalid=realization.provenance
---
info: rejected=true output-absent=true certificate-absent=true
-/
#guard_msgs in
run_cmd do
  -- defEqTypeTamper: replace the declaration's type, retaining the constructed tree.
  tamperDeclaration (← `(term| fun info => { info with
    type := mkApp3 (mkConst ``Eq [.succ .zero]) (mkConst ``Nat)
      (mkNatLit 5) (mkNatLit 5) }))
    `defEqTypeTamper

/--
info: IE-C037 DispositionClassMismatch theorem=LeanInformationAudit.Tests.Census.RegisteredClosedTruth.generated class=structural_occurrence invalid=realization.provenance
---
info: rejected=true output-absent=true certificate-absent=true
-/
#guard_msgs in
run_cmd do
  tamperDeclaration (← `(term| fun info => { info with
    value := mkConst ``RegisteredClosedTruth.closedTruth }))
    `replacedProof

/--
info: IE-C044 DispositionCensusMismatch head=probe-head component=root expected=import-closure-containing:LeanInformationAudit.Tests.Census.RegisteredClosedTruth.generated actual=LeanInformationAudit.Tests.Census.RegisteredClosedTruth
---
info: rejected=true output-absent=true certificate-absent=true
-/
#guard_msgs in
run_cmd do
  tamper (← `(term| fun entry => { entry with registrationModule :=
    `LeanInformationAudit.Tests.Census.LawRegistry }))
    `outsideRootEntry (censusError "probe-head" "root"
      "import-closure-containing:LeanInformationAudit.Tests.Census.RegisteredClosedTruth.generated"
      "LeanInformationAudit.Tests.Census.RegisteredClosedTruth")

def lawAlias : StructuralPrimitiveLawArena Evidence.infiniteArena := Evidence.structuralLawArena

/--
info: IE-C037 DispositionClassMismatch theorem=LeanInformationAudit.Tests.Census.RegisteredClosedTruth.generated class=structural_occurrence invalid=realization.law_nondegeneracy
---
info: rejected=true output-absent=true certificate-absent=true
-/
#guard_msgs in
run_cmd do
  tamper (← `(term| fun entry => { entry with certificateName := ``Evidence.closedNumerical }))
    `corruptNondegeneracy (classError ``RegisteredClosedTruth.generated
      "structural_occurrence" "realization.law_nondegeneracy")

/-- error: IE-C037 DispositionClassMismatch theorem=LeanInformationAudit.Tests.Census.LawRegistry.aliasGenerated class=structural_occurrence invalid=realization.canonical_law_arena -/
#guard_msgs in
structural_theorem aliasGenerated in lawAlias realization Evidence.structuralReadouts
  nondegeneracy Evidence.structuralLawNondegenerate := fun n => Nat.mod_lt n (by decide)

/-- error: structural declaration already exists: LeanInformationAudit.Tests.Census.RegisteredClosedTruth.closedTruth -/
#guard_msgs in
structural_theorem _root_.LeanInformationAudit.Tests.Census.RegisteredClosedTruth.closedTruth
  in RegisteredClosedTruth.lawArena realization RegisteredClosedTruth.readouts
  nondegeneracy RegisteredClosedTruth.nondegenerate := rfl

/--
info: IE-C037 DispositionClassMismatch theorem=LeanInformationAudit.Tests.Census.RegisteredClosedTruth.generated class=structural_occurrence invalid=realization.provenance
---
info: rejected=true output-absent=true certificate-absent=true
-/
#guard_msgs in
run_cmd do
  tamper (← `(term| fun entry => { entry with
    statementExpr := mkApp3 (mkConst ``Eq [.succ .zero]) (mkConst ``Nat)
      (mkNatLit 5) (mkNatLit 5) }))
    `defEqRecordType (classError ``RegisteredClosedTruth.generated
      "structural_occurrence" "realization.provenance")

/--
info: IE-C037 DispositionClassMismatch theorem=LeanInformationAudit.Tests.Census.RegisteredClosedTruth.generated class=structural_occurrence invalid=realization.canonical_law_arena
---
info: rejected=true output-absent=true certificate-absent=true
-/
#guard_msgs in
run_cmd do
  tamper (← `(term| fun entry => { entry with lawArenaConst := ``lawAlias }))
    `differentRecordLaw (classError ``RegisteredClosedTruth.generated
      "structural_occurrence" "realization.canonical_law_arena")

/--
info: IE-C037 DispositionClassMismatch theorem=LeanInformationAudit.Tests.Census.RegisteredClosedTruth.generated class=structural_occurrence invalid=realization.provenance.syntax
---
info: rejected=true output-absent=true certificate-absent=true
-/
#guard_msgs in
run_cmd do
  tamper (← `(term| fun entry => { entry with registrationModule :=
    `LeanInformationAudit.Tests.Census.Evidence }))
    `wrongOwnerInClosure (classError ``RegisteredClosedTruth.generated
      "structural_occurrence" "realization.provenance.syntax")

/--
info: IE-C037 DispositionClassMismatch theorem=LeanInformationAudit.Tests.Census.RegisteredClosedTruth.generated class=structural_occurrence invalid=realization.provenance.syntax
---
info: rejected=true output-absent=true certificate-absent=true
-/
#guard_msgs in
run_cmd do
  tamper (← `(term| fun entry => { entry with lawArenaSyntax := "RegisteredClosedTruth.lawArena" }))
    `differentSourceLaw (classError ``RegisteredClosedTruth.generated
      "structural_occurrence" "realization.provenance.syntax")

/--
info: IE-C037 DispositionClassMismatch theorem=LeanInformationAudit.Tests.Census.RegisteredClosedTruth.generated class=structural_occurrence invalid=realization.provenance.syntax
---
info: rejected=true output-absent=true certificate-absent=true
-/
#guard_msgs in
run_cmd do
  tamper (← `(term| fun entry => { entry with realizationSyntax := "otherReadouts" }))
    `differentSourceRealization (classError ``RegisteredClosedTruth.generated
      "structural_occurrence" "realization.provenance.syntax")

end LeanInformationAudit.Tests.Census.LawRegistry
