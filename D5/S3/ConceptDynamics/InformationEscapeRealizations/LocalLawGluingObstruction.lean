/- GID: D5/S3/ConceptDynamics/InformationEscapeRealizations/LocalLawGluingObstruction
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/InformationEscapeRealizations/LocalLawGluingObstruction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Three pulled-back local laws realize the gluing obstruction with four kernel classes. -/

import D5.S3.ConceptDynamics.InformationEscapeArenas.LocalLawGluingObstruction

/- Library-search audit trail (2026-09-04): the source relations, frozen theorem,
   Boolean ADMIT bridge, and typed bundle compiler are exact repository hits and
   reused. No existing legacy realization or gluing partition certificate was found. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.InformationEscapeRealizations.LocalLawGluingObstruction

open D5.S3.ConceptDynamics.InformationEscape
open D5.S3.ConceptDynamics.InformationEscapeArenas.LocalLawGluingObstruction

/-- The three pair laws pulled back along the projections of a global-state attempt. -/
def localLawGluingRealization : PrimitiveRealization localLawGluingSignature where
  readout
    | .admit01 => fun state => decide (state.1 = state.2.1)
    | .admit12 => fun state => decide (state.2.1 = state.2.2)
    | .admit02 => fun state => decide (state.1 ≠ state.2.2)
  anchor := fun i => Fin.elim0 i

/-- The frozen gluing statement is equivalent to its object-bound ADMIT law. -/
theorem compatible_local_laws_can_lack_global_state_realization :
    LegacyPrimitiveRealization localLawGluingArena LocalLawGluingStatement
      localLawGluingRealization := by
  refine ⟨?_⟩
  constructor
  · intro _source
    change
      (forall b : Bool,
        (∃ state : Bool × Bool × Bool,
          decide (state.1 = state.2.1) = true /\ state.2.1 = b) <->
        (∃ state : Bool × Bool × Bool,
          decide (state.2.1 = state.2.2) = true /\ state.2.1 = b)) /\
      (forall b : Bool,
        (∃ state : Bool × Bool × Bool,
          decide (state.1 = state.2.1) = true /\ state.1 = b) <->
        (∃ state : Bool × Bool × Bool,
          decide (state.1 ≠ state.2.2) = true /\ state.1 = b)) /\
      (forall b : Bool,
        (∃ state : Bool × Bool × Bool,
          decide (state.2.1 = state.2.2) = true /\ state.2.2 = b) <->
        (∃ state : Bool × Bool × Bool,
          decide (state.1 ≠ state.2.2) = true /\ state.2.2 = b)) /\
      ¬ ∃ state : Bool × Bool × Bool,
        decide (state.1 = state.2.1) = true /\
        decide (state.2.1 = state.2.2) = true /\
        decide (state.1 ≠ state.2.2) = true
    decide
  · intro hLaw
    constructor
    · refine ⟨?_, ?_, ?_⟩
      · ext bit
        cases bit <;> simp [sameLaw]
      · ext bit
        cases bit <;> simp [sameLaw, differentLaw]
      · ext bit
        cases bit <;> simp [sameLaw, differentLaw]
    · rintro ⟨state, h01, h12, h02⟩
      apply hLaw.2.2.2
      refine ⟨state, ?_, ?_, ?_⟩
      · simpa [localLawGluingRealization] using
          (admit_readout_eq_true_iff
            (fun s : Bool × Bool × Bool => s.1 = s.2.1) state).2 h01
      · simpa [localLawGluingRealization] using
          (admit_readout_eq_true_iff
            (fun s : Bool × Bool × Bool => s.2.1 = s.2.2) state).2 h12
      · simpa [localLawGluingRealization] using
          (admit_readout_eq_true_iff
            (fun s : Bool × Bool × Bool => s.1 ≠ s.2.2) state).2 h02

/-- The three ADMIT bits induce exactly the four census kernel classes. -/
theorem compatible_local_laws_can_lack_global_state_partition_count :
    (Finset.univ.image (fun state : Bool × Bool × Bool =>
      (localLawGluingRealization.readout .admit01 state,
        localLawGluingRealization.readout .admit12 state,
        localLawGluingRealization.readout .admit02 state))).card = 4 := by
  decide

/-- The private census pair `000,001` is separated by the outer ADMIT slot. -/
theorem compatible_local_laws_can_lack_global_state_private_pair :
    ¬ localLawGluingRealization.toPrimitiveBundle.agrees
      (false, false, false) (false, false, true) := by
  decide

example : localLawGluingArena.toArena.Nondegenerate := by decide

end D5.S3.ConceptDynamics.InformationEscapeRealizations.LocalLawGluingObstruction
