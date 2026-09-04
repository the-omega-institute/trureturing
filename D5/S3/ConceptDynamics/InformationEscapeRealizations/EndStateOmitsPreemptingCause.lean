/- GID: D5/S3/ConceptDynamics/InformationEscapeRealizations/EndStateOmitsPreemptingCause
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/InformationEscapeRealizations/EndStateOmitsPreemptingCause
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The two preemption traces realize endpoint and cause laws with a five-class kernel. -/

import D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause

/- Library-search audit trail (2026-09-04): exact repository hits for both source
   readouts, ordered-preemption predicate, named traces, coded ADMIT bridge, and bundle
   compiler are reused. No deposited realization or five-class certificate was found. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.InformationEscapeRealizations.EndStateOmitsPreemptingCause

open D5.S3.ConceptDynamics.InformationEscape
open D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause
open D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause

/-- Concrete endpoint, active-cause, and ordered-preemption readouts with named anchors. -/
def endStateOmitsPreemptingCauseRealization : PrimitiveRealization preemptionSignature where
  readout
    | .cutEnd => endState
    | .cutCause => activeCause
    | .admitAThenB => fun trace =>
        decide (IsOrderedPreemption trace .shooterA .shooterB)
    | .admitBThenA => fun trace =>
        decide (IsOrderedPreemption trace .shooterB .shooterA)
  anchor
    | .aThenB => aThenB
    | .bThenA => bThenA

/-- The frozen preemption theorem is equivalent to its object-bound realization law. -/
theorem end_state_omits_preempting_cause_realization :
    LegacyPrimitiveRealization endStateOmitsPreemptingCauseArena
      EndStateOmitsPreemptingCauseStatement endStateOmitsPreemptingCauseRealization := by
  refine ⟨?_⟩
  constructor
  · rintro ⟨hAB, hBA, hEnd, hCause, hFactor⟩
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · exact (admit_readout_eq_true_iff
        (fun trace => IsOrderedPreemption trace .shooterA .shooterB) aThenB).2 hAB
    · exact (admit_readout_eq_true_iff
        (fun trace => IsOrderedPreemption trace .shooterB .shooterA) bThenA).2 hBA
    · exact hEnd
    · exact hCause
    · exact hFactor
  · rintro ⟨hAB, hBA, hEnd, hCause, hFactor⟩
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · exact (admit_readout_eq_true_iff
        (fun trace => IsOrderedPreemption trace .shooterA .shooterB) aThenB).1 hAB
    · exact (admit_readout_eq_true_iff
        (fun trace => IsOrderedPreemption trace .shooterB .shooterA) bThenA).1 hBA
    · exact hEnd
    · exact hCause
    · exact hFactor

/-- The full readout-and-anchor signature induces the five census kernel classes. -/
theorem end_state_omits_preempting_cause_partition_count :
    (Finset.univ.image (fun trace : PreemptionTrace =>
      (endState trace, activeCause trace,
        decide (IsOrderedPreemption trace .shooterA .shooterB),
        decide (IsOrderedPreemption trace .shooterB .shooterA),
        decide (trace = aThenB), decide (trace = bThenA)))).card = 5 := by
  decide

/-- The private traces `AB,BA` are separated by the compiled primitive bundle. -/
theorem end_state_omits_preempting_cause_private_pair :
    ¬ endStateOmitsPreemptingCauseRealization.toPrimitiveBundle.agrees aThenB bThenA := by
  decide

example : endStateOmitsPreemptingCauseArena.toArena.Nondegenerate := by decide

end D5.S3.ConceptDynamics.InformationEscapeRealizations.EndStateOmitsPreemptingCause
