/- GID: D5/S3/ConceptDynamics/InformationEscape/PointwiseDisequalityRegistrations
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/InformationEscape/PointwiseDisequalityRegistrations
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=checker; basis=terminal=gid:D5/S3/ConceptDynamics/InformationEscape/PointwiseDisequalityRegistrations.recurrent_lawSensitive; instance=D5/S3/ConceptDynamics/InformationEscape/PointwiseDisequalityRegistrations.recurrentRealization
   digest: Recurrent and transient channel exclusions share a pointwise disequality template and one digit arena. -/

import D5.S3.ConceptDynamics.InformationEscape.PointwiseRegistrationTemplates
import D5.S3.ConceptDynamics.InformationEscapeHierarchy.StructuralCatalog
import D5.S0.Certificates.SkeletonChannelRetraction
import LeanInformationAudit.SealCommand

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.InformationEscape.PointwiseDisequalityRegistrations

open PointwiseRegistrationTemplates LeanInformationAudit
open D5.S0.Certificates.SkeletonChannelRetraction

def digitArena := pointwiseNeArena (Arena.ofFintype (Fin 4)) (Fin 4)
theorem digit_slotSensitive : FiniteSlotSensitivity digitArena :=
  pointwiseNe_sensitivity _ (0 : Fin 4) (0 : Fin 4) 1 (by decide)

def recurrentRealization := pointwiseNeRealization recurrentRetract (fun _ => (2 : Fin 4))
theorem recurrent_bridge : LegacyPrimitiveRealization digitArena
    (∀ d : Fin 4, recurrentRetract d ≠ 2) recurrentRealization := pointwiseNeLegacy _ _ _
theorem recurrent_lawSensitive : digitArena.Law recurrentRealization ∧
    ¬ digitArena.Law (pointwiseNeRealization (fun _ => (2 : Fin 4)) (fun _ => 2)) :=
  ⟨recurrent_bridge.equivalence.mp recurrentRetract_ne_two, fun h => h (0 : Fin 4) rfl⟩
register_information_theorem recurrentRetract_ne_two in digitArena
  primitives recurrentRealization.toPrimitiveBundle realization recurrent_bridge
  variation recurrent_lawSensitive sensitivity digit_slotSensitive
example : recurrentRetract_ne_two.__information_unit.Statement =
    (∀ d : Fin 4, recurrentRetract d ≠ 2) := rfl
#print axioms recurrent_bridge
#print axioms recurrent_lawSensitive
expect_information_occurrence recurrentRetract_ne_two in digitArena
  from "D5.S3.ConceptDynamics.InformationEscape.PointwiseDisequalityRegistrations"

def transientRealization := pointwiseNeRealization transientRetract (fun _ => (0 : Fin 4))
theorem transient_bridge : LegacyPrimitiveRealization digitArena
    (∀ d : Fin 4, transientRetract d ≠ 0) transientRealization := pointwiseNeLegacy _ _ _
theorem transient_lawSensitive : digitArena.Law transientRealization ∧
    ¬ digitArena.Law (pointwiseNeRealization (fun _ => (0 : Fin 4)) (fun _ => 0)) :=
  ⟨transient_bridge.equivalence.mp transientRetract_ne_zero, fun h => h (0 : Fin 4) rfl⟩
register_information_theorem transientRetract_ne_zero in digitArena
  primitives transientRealization.toPrimitiveBundle realization transient_bridge
  variation transient_lawSensitive sensitivity digit_slotSensitive
example : transientRetract_ne_zero.__information_unit.Statement =
    (∀ d : Fin 4, transientRetract d ≠ 0) := rfl
#print axioms transient_bridge
#print axioms transient_lawSensitive
expect_information_occurrence transientRetract_ne_zero in digitArena
  from "D5.S3.ConceptDynamics.InformationEscape.PointwiseDisequalityRegistrations"

#print axioms digit_slotSensitive
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

end D5.S3.ConceptDynamics.InformationEscape.PointwiseDisequalityRegistrations
