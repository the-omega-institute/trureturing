/- GID: D5/S3/ConceptDynamics/InformationEscape/HughesIterationDepthNoGapRegistration
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/InformationEscape/HughesIterationDepthNoGapRegistration
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A two-origin coordinate registers no-gap with a shifted counterfactual. -/

import D5.S1.Words.HughesIterationDepthNoGap
import D5.S3.ConceptDynamics.InformationEscape.RegistrationTemplates
import LeanInformationAudit.RegistrationWitnesses
import LeanInformationAudit.Syntax

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.InformationEscape.HughesIterationDepthNoGapRegistration

open D5.S1.Words.HughesIterationDepthNoGap
open LeanInformationAudit
open RegistrationTemplates

/-- The identity readout keeps the published zero-based depth coordinate. -/
def depthOriginRealization :
    PrimitiveRealization (cutSignature (Fin 2) (Fin 2)) :=
  cutRealization (fun origin : Fin 2 => origin)

/-- The counterfactual readout shifts every requested origin to coordinate one. -/
private def shiftedDepthOriginRealization :
    PrimitiveRealization (cutSignature (Fin 2) (Fin 2)) :=
  cutRealization (fun _ : Fin 2 => (1 : Fin 2))

/-- The law asks for downward closure of the whole arbitrary-language spectrum
at the read origin. -/
abbrev depthNoGapArena : PrimitiveLawArena where
  toArena := Arena.ofFintype (Fin 2)
  signature := cutSignature (Fin 2) (Fin 2)
  Law realization :=
    ∀ (α : Type) [Finite α]
      (A B : D5.S1.Words.HughesIterationDepthNoGap.Language α) (r : Nat),
      r ∈ iterationDepthSpectrumAt
          (realization.readout () closedSourceZero) A B →
        ∀ q ≤ r,
          q ∈ iterationDepthSpectrumAt
            (realization.readout () closedSourceZero) A B

private theorem depth_no_gap_bridge : LegacyPrimitiveRealization depthNoGapArena
    (∀ (α : Type) [Finite α]
      (A B : D5.S1.Words.HughesIterationDepthNoGap.Language α) (r : Nat),
      r ∈ iterationDepthSpectrumAt closedSourceZero A B →
        ∀ q ≤ r, q ∈ iterationDepthSpectrumAt closedSourceZero A B)
    depthOriginRealization :=
  ⟨Iff.rfl⟩

private def emptyLanguage : D5.S1.Words.HughesIterationDepthNoGap.Language (Fin 0) := ∅

private def epsilonLanguage : D5.S1.Words.HughesIterationDepthNoGap.Language (Fin 0) := {[]}

private theorem epsilon_has_depth_zero :
    hasIterationDepth emptyLanguage epsilonLanguage [] 0 := by
  refine ⟨⟨1, by decide, ?_⟩, ?_⟩
  · simp [fixedDegreeIterate, epsilonLanguage]
  · omega

private theorem one_mem_shifted_spectrum :
    1 ∈ iterationDepthSpectrumAt (1 : Fin 2) emptyLanguage epsilonLanguage := by
  exact ⟨0, ⟨[], epsilon_has_depth_zero⟩, by decide⟩

private theorem zero_not_mem_shifted_spectrum :
    0 ∉ iterationDepthSpectrumAt (1 : Fin 2) emptyLanguage epsilonLanguage := by
  rintro ⟨m, _, hm⟩
  omega

private theorem shifted_depth_law_fails :
    ¬ depthNoGapArena.Law shiftedDepthOriginRealization := by
  intro law
  exact zero_not_mem_shifted_spectrum
    (law (Fin 0) emptyLanguage epsilonLanguage 1 one_mem_shifted_spectrum 0 (by decide))

private theorem depth_law_holds : depthNoGapArena.Law depthOriginRealization :=
  depth_no_gap_bridge.equivalence.mp (@result)

private theorem depth_law_variation : FiniteLawVariation depthNoGapArena :=
  ⟨depthOriginRealization, shiftedDepthOriginRealization,
    depth_law_holds, shifted_depth_law_fails⟩

private theorem depth_slot_sensitivity : FiniteSlotSensitivity depthNoGapArena := by
  constructor
  · intro i
    cases i
    refine ⟨depthOriginRealization, shiftedDepthOriginRealization, ?_, ?_, ?_⟩
    · intro j hj
      cases j
      exact (hj rfl).elim
    · intro j
      exact Fin.elim0 j
    · exact ⟨fun _ => shifted_depth_law_fails, fun _ => depth_law_holds⟩
  · intro i
    exact Fin.elim0 i

register_information_template cutRealization

register_information_theorem result in depthNoGapArena
  readout via (@cutRealization (Fin 2) (Fin 2) (instDecidableEqFin 2)
    (fun origin : Fin 2 => origin))
  primitives depthOriginRealization.toPrimitiveBundle realization depth_no_gap_bridge
  variation depth_law_variation sensitivity depth_slot_sensitivity
  escape from (closedSourceZero) escape continues (open)

#print axioms depth_no_gap_bridge
#print axioms shifted_depth_law_fails
#print axioms depth_slot_sensitivity

end D5.S3.ConceptDynamics.InformationEscape.HughesIterationDepthNoGapRegistration
