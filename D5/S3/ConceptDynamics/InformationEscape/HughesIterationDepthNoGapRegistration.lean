/- GID: D5/S3/ConceptDynamics/InformationEscape/HughesIterationDepthNoGapRegistration
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/InformationEscape/HughesIterationDepthNoGapRegistration
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A two-origin coordinate registers no-gap with a shifted counterfactual. -/

import D5.S1.Words.HughesIterationDepthNoGap
import D5.S3.ConceptDynamics.InformationEscape.RegistrationTemplates
import D5.S3.ConceptDynamics.RegistrationWitnesses


set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.InformationEscape.HughesIterationDepthNoGapRegistration

open D5.S1.Words.HughesIterationDepthNoGap
open LeanInformationAudit
open RegistrationTemplates

def depthOriginTemplate (f : Fin 2 → Fin 2) :
    PrimitiveRealization (cutSignature (Fin 2) (Fin 2)) :=
  ⟨fun _ => f, Fin.elim0⟩

/-- The identity readout keeps the published zero-based depth coordinate. -/
def depthOriginRealization :
    PrimitiveRealization (cutSignature (Fin 2) (Fin 2)) :=
  depthOriginTemplate (fun origin => origin)

/-- The counterfactual readout shifts every requested origin to coordinate one. -/
private def shiftedDepthOriginRealization :
    PrimitiveRealization (cutSignature (Fin 2) (Fin 2)) :=
  depthOriginTemplate (fun _ => (1 : Fin 2))

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

private def emptyLanguage : D5.S1.Words.HughesIterationDepthNoGap.Language (Fin 0) := ∅

private def epsilonLanguage : D5.S1.Words.HughesIterationDepthNoGap.Language (Fin 0) := {[]}

theorem depth_law_variation : FiniteLawVariation depthNoGapArena :=
    by
  refine ⟨depthOriginRealization, shiftedDepthOriginRealization, ?_, ?_⟩
  · simpa [depthNoGapArena, depthOriginRealization, depthOriginTemplate] using (@result)
  · intro law
    have epsilon_has_depth_zero :
        hasIterationDepth emptyLanguage epsilonLanguage [] 0 := by
      refine ⟨⟨1, by decide, ?_⟩, ?_⟩
      · simp [fixedDegreeIterate, epsilonLanguage]
      · omega
    have one_mem_shifted_spectrum :
        1 ∈ iterationDepthSpectrumAt (1 : Fin 2) emptyLanguage epsilonLanguage :=
      ⟨0, ⟨[], epsilon_has_depth_zero⟩, by decide⟩
    have zero_not_mem_shifted_spectrum :
        0 ∉ iterationDepthSpectrumAt (1 : Fin 2) emptyLanguage epsilonLanguage := by
      rintro ⟨m, _, hm⟩
      omega
    exact zero_not_mem_shifted_spectrum
      (law (Fin 0) emptyLanguage epsilonLanguage 1 one_mem_shifted_spectrum 0 (by decide))

theorem depth_slot_sensitivity : FiniteSlotSensitivity depthNoGapArena := by
  constructor
  · intro i
    cases i
    refine ⟨depthOriginRealization, shiftedDepthOriginRealization, ?_, ?_, ?_⟩
    · intro j hj
      cases j
      exact (hj rfl).elim
    · intro j
      exact Fin.elim0 j
    · constructor
      · intro _ shiftedLaw
        have epsilon_has_depth_zero :
            hasIterationDepth emptyLanguage epsilonLanguage [] 0 := by
          refine ⟨⟨1, by decide, ?_⟩, ?_⟩
          · simp [fixedDegreeIterate, epsilonLanguage]
          · omega
        have one_mem_shifted_spectrum :
            1 ∈ iterationDepthSpectrumAt (1 : Fin 2) emptyLanguage epsilonLanguage :=
          ⟨0, ⟨[], epsilon_has_depth_zero⟩, by decide⟩
        have zero_not_mem_shifted_spectrum :
            0 ∉ iterationDepthSpectrumAt (1 : Fin 2) emptyLanguage epsilonLanguage := by
          rintro ⟨m, _, hm⟩
          omega
        exact zero_not_mem_shifted_spectrum
          (shiftedLaw (Fin 0) emptyLanguage epsilonLanguage 1 one_mem_shifted_spectrum 0 (by decide))
      · intro _
        simpa [depthNoGapArena, depthOriginRealization, depthOriginTemplate]
          using (@result)
  · intro i
    exact Fin.elim0 i





#print axioms depth_law_variation
#print axioms depth_slot_sensitivity

end D5.S3.ConceptDynamics.InformationEscape.HughesIterationDepthNoGapRegistration
