/- GID: D5/S3/ConceptDynamics/InformationEscape/DisjunctionRegistrations
   generality: I
   mirror-B: D5/B/S3/ConceptDynamics/InformationEscape/DisjunctionRegistrations
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=checker; basis=terminal=gid:D5/S3/ConceptDynamics/InformationEscape/DisjunctionRegistrations.eisenstein_lawSensitive; instance=D5/S3/ConceptDynamics/InformationEscape/DisjunctionRegistrations.eisensteinRealization
   digest: Three frozen disjunction theorems use one state-dependent admissible disjunction template with checked slot sensitivity. -/

import D5.S3.ConceptDynamics.InformationEscape.DisjunctionRegistrationTemplates
import D5.S0.Certificates.SkeletonSlotProfileSymmetry
import D5.S1.Phase.ZeroOrbitCongruence
import D5.S3.ConceptDynamics.Answering.AssertionSettlementCeiling
import LeanInformationAudit.SealCommand

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096

namespace D5.S3.ConceptDynamics.InformationEscape.DisjunctionRegistrations

open DisjunctionRegistrationTemplates LeanInformationAudit
open D5.S0.Certificates.SkeletonSlotProfileSymmetry
open D5.S1.Phase.ZeroOrbitCongruence
open D5.S3.ConceptDynamics.Answering.AssertionSettlementCeiling

abbrev EisensteinState := Prod (ZMod 3) (ZMod 3)

def eisensteinArena :=
  disjunctionArena (Arena.ofFintype EisensteinState) (fun _ => True)
def eisensteinRealization := disjunctionRealization
  (fun s : EisensteinState => s.1 ^ 2 - s.1 * s.2 + s.2 ^ 2 = 0)
  (fun s : EisensteinState => s.1 ^ 2 - s.1 * s.2 + s.2 ^ 2 = 1)
theorem eisenstein_bridge : LegacyPrimitiveRealization eisensteinArena
    (∀ (x y : ZMod 3),
      x ^ 2 - x * y + y ^ 2 = 0 ∨ x ^ 2 - x * y + y ^ 2 = 1)
    eisensteinRealization := by
  refine ⟨?_⟩
  constructor
  · intro h
    rintro ⟨x, y⟩ _
    simpa [eisensteinRealization, disjunctionRealization] using h x y
  · intro h x y
    simpa [eisensteinRealization, disjunctionRealization] using h (x, y) trivial
theorem eisenstein_lawSensitive : eisensteinArena.Law eisensteinRealization ∧
    ¬ eisensteinArena.Law (disjunctionRealization (X := EisensteinState)
      (fun _ => False) (fun _ => False)) := by
  constructor
  · rintro ⟨x, y⟩ _
    simpa [eisensteinRealization, disjunctionRealization] using
      eisenstein_norm_mod_three x y
  · intro h
    have hs := h ((0 : ZMod 3), (0 : ZMod 3)) trivial
    simp [disjunctionRealization] at hs
theorem eisenstein_slotSensitive : FiniteSlotSensitivity eisensteinArena :=
  disjunction_sensitivity _ _ ((0 : ZMod 3), (0 : ZMod 3)) trivial
register_information_theorem eisenstein_norm_mod_three in eisensteinArena
  primitives eisensteinRealization.toPrimitiveBundle realization eisenstein_bridge
  variation eisenstein_lawSensitive sensitivity eisenstein_slotSensitive
example : eisenstein_norm_mod_three.__information_unit.Statement =
    (∀ (x y : ZMod 3),
      x ^ 2 - x * y + y ^ 2 = 0 ∨ x ^ 2 - x * y + y ^ 2 = 1) := rfl
#print axioms eisenstein_bridge
#print axioms eisenstein_lawSensitive
#print axioms eisenstein_slotSensitive
expect_information_occurrence eisenstein_norm_mod_three in eisensteinArena
  from "D5.S3.ConceptDynamics.InformationEscape.DisjunctionRegistrations"


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

end D5.S3.ConceptDynamics.InformationEscape.DisjunctionRegistrations
