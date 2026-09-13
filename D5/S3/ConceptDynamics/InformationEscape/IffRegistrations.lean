/- GID: D5/S3/ConceptDynamics/InformationEscape/IffRegistrations
   generality: I
   mirror-B: D5/B/S3/ConceptDynamics/InformationEscape/IffRegistrations
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=checker; basis=terminal=gid:D5/S3/ConceptDynamics/InformationEscape/IffRegistrations.dual_lawSensitive; instance=D5/S3/ConceptDynamics/InformationEscape/IffRegistrations.dualRealization
   digest: Two frozen iff theorems retain their predicates in one Boolean readout template. -/

import D5.S3.ConceptDynamics.InformationEscape.IffRegistrationTemplates
import D5.S3.ConceptDynamics.Answering.AssertionSettlementCeiling
import D5.S0.Certificates.SelfInterestConventionDeviationGain
import LeanInformationAudit.SealCommand

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.InformationEscape.IffRegistrations

open IffRegistrationTemplates PointwiseRegistrationTemplates RegistrationTemplates LeanInformationAudit

section OpenClaim
open D5.S3.ConceptDynamics.Answering.AssertionSettlementCeiling

instance : Fintype Claim where
  elems := {.unsettled, .nonformalJudgment, .consequentUnderConditions, .assertP, .assertNegP}
  complete := by intro c; cases c <;> simp

local instance openPermissionDecidable : DecidablePred (fun c : Claim =>
    permits .open c = true) := by
  intro c
  cases c <;> exact inferInstance
local instance openUnsettledDecidable : DecidablePred (fun c : Claim =>
    c = .unsettled) := by
  intro c
  cases c <;> exact inferInstance

def openArena := iffArena (Arena.ofFintype Claim)
def openRealization := @iffRealization Claim
  (fun c : Claim => permits .open c = true)
  (fun c : Claim => c = .unsettled) openPermissionDecidable openUnsettledDecidable
theorem open_bridge : LegacyPrimitiveRealization openArena
    (∀ c : Claim, permits .open c = true ↔ c = .unsettled) openRealization :=
  @iffLegacy (Arena.ofFintype Claim)
    (fun c : Claim => permits .open c = true)
    (fun c : Claim => c = .unsettled) openPermissionDecidable openUnsettledDecidable
theorem open_lawSensitive : openArena.Law openRealization ∧
    ¬ openArena.Law (iffRealization (fun _ : Claim => True) (fun _ => False)) := by
  classical
  refine ⟨open_bridge.equivalence.mp (fun c => open_permits_only_unsettled c), ?_⟩
  intro h
  have contradiction := h (.unsettled : Claim)
  simpa [openArena, iffArena, iffRealization, pointwiseEqArena,
    pointwiseEqRealization, separationRealization] using contradiction
theorem open_slotSensitive : FiniteSlotSensitivity openArena :=
  iff_sensitivity _ (.unsettled : Claim)
register_information_theorem open_permits_only_unsettled in openArena
  primitives openRealization.toPrimitiveBundle realization open_bridge
  variation open_lawSensitive sensitivity open_slotSensitive
example : open_permits_only_unsettled.__information_unit.Statement =
    (∀ c : Claim, permits .open c = true ↔ c = .unsettled) := rfl
#print axioms open_bridge
#print axioms open_lawSensitive
#print axioms open_slotSensitive
expect_information_occurrence open_permits_only_unsettled in openArena
  from "D5.S3.ConceptDynamics.InformationEscape.IffRegistrations"
end OpenClaim

section DualConvention
open D5.S0.Certificates.SelfInterestConventionDeviationGain

local instance dualDecidable : DecidablePred (fun convention : Convention =>
    dual convention = convention) := by
  intro convention
  rcases convention with ⟨first, second⟩
  cases first <;> cases second <;> exact inferInstance
local instance dualAlternativesDecidable : DecidablePred (fun convention : Convention =>
    convention = FvF ∨ convention = AvA) := by
  intro convention
  rcases convention with ⟨first, second⟩
  cases first <;> cases second <;> exact inferInstance

def dualArena := iffArena (Arena.ofFintype Convention)
def dualRealization := @iffRealization Convention
  (fun convention : Convention => dual convention = convention)
  (fun convention : Convention => convention = FvF ∨ convention = AvA)
  dualDecidable dualAlternativesDecidable
theorem dual_bridge : LegacyPrimitiveRealization dualArena
    (∀ convention : Convention, dual convention = convention ↔
      convention = FvF ∨ convention = AvA) dualRealization :=
  @iffLegacy (Arena.ofFintype Convention)
    (fun convention : Convention => dual convention = convention)
    (fun convention : Convention => convention = FvF ∨ convention = AvA)
    dualDecidable dualAlternativesDecidable
theorem dual_lawSensitive : dualArena.Law dualRealization ∧
    ¬ dualArena.Law (iffRealization (fun _ : Convention => True) (fun _ => False)) := by
  classical
  refine ⟨dual_bridge.equivalence.mp (fun convention => dual_fixed_iff convention), ?_⟩
  intro h
  have contradiction := h FvF
  simpa [dualArena, iffArena, iffRealization, pointwiseEqArena,
    pointwiseEqRealization, separationRealization] using contradiction
theorem dual_slotSensitive : FiniteSlotSensitivity dualArena :=
  iff_sensitivity _ FvF
register_information_theorem dual_fixed_iff in dualArena
  primitives dualRealization.toPrimitiveBundle realization dual_bridge
  variation dual_lawSensitive sensitivity dual_slotSensitive
example : dual_fixed_iff.__information_unit.Statement =
    (∀ convention : Convention, dual convention = convention ↔
      convention = FvF ∨ convention = AvA) := rfl
#print axioms dual_bridge
#print axioms dual_lawSensitive
#print axioms dual_slotSensitive
expect_information_occurrence dual_fixed_iff in dualArena
  from "D5.S3.ConceptDynamics.InformationEscape.IffRegistrations"
end DualConvention

#seal_information_theory

open Lean in
run_meta do
  let env ← getEnv
  for entry in InformationRegistry.entries env do
    if entry.registrationModuleName == env.header.mainModule then
      let info ← getConstInfo (RegistrationGates.diagnosticName entry.unitName env.header.mainModule)
      let some (.lit (.strVal diagnostic)) := info.value?
        | throwError "registration diagnostic is not a literal"
      if diagnostic.isEmpty then
        logInfo m!"REGISTRATION_WITNESSES_CHECKED {entry.theoremName} support=[readout[0],readout[1]]"
      else
        logWarning diagnostic

end D5.S3.ConceptDynamics.InformationEscape.IffRegistrations
