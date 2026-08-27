/- GID: D5/S3/ConceptDynamics/Information/MarginalActionEntropyCausalContrast
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Information/MarginalActionEntropyCausalContrast
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Equal marginal action entropy does not identify internal causal control. -/

import D5.S3.ConceptDynamics.Information.EqualEntropyTargetValueContrast

/- Library-search audit trail (2026-08-27):
   * Exact repository hits `conceptLaw` and `pushforward` provide the canonical
     finite readout law and deterministic image law; both are imported.
   * `equal_entropy_target_value_contrast` supplies the exact entropy
     calculation for the uniform Boolean-coordinate witness and is applied.
   * Repository and pinned-Mathlib searches found no theorem combining equal
     action entropy with the two intervention-law clauses. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Information.MarginalActionEntropyCausalContrast

open D5.S3.ConceptDynamics.Information.EqualEntropyTargetValueContrast
open D5.S3.ConceptDynamics.Information.RefinementEntropyMonotonicity
open D5.S3.Entropy.Forgetting.CapacityMonotone
open D5.S3.Entropy.MaxEntropy

/-- For a uniform hidden bit and an independent uniform noise bit, copying the
noise or copying the hidden bit gives the same marginal action entropy. Only
the latter action law changes when the hidden bit is intervened upon. -/
theorem marginal_action_entropy_causal_contrast :
    let stateLaw : Bool × Bool -> Real := fun _ => 1 / 4
    let externalModel : Bool × Bool -> Bool := Prod.snd
    let internalModel : Bool × Bool -> Bool := Prod.fst
    let noiseLaw : Bool -> Real := fun _ => 1 / 2
    let interventionLaw (model : Bool × Bool -> Bool) (state : Bool) :
        Bool -> Real := pushforward (fun noise => model (state, noise)) noiseLaw
    shannonEntropy (conceptLaw stateLaw externalModel) =
        shannonEntropy (conceptLaw stateLaw internalModel) ∧
      interventionLaw externalModel false = interventionLaw externalModel true ∧
      interventionLaw internalModel false ≠ interventionLaw internalModel true := by
  dsimp only
  have entropyFacts := equal_entropy_target_value_contrast
  dsimp only at entropyFacts
  refine ⟨entropyFacts.2.1.trans entropyFacts.1.symm, rfl, ?_⟩
  intro lawsEqual
  have atFalse := congrFun lawsEqual false
  norm_num [pushforward, Fintype.sum_bool] at atFalse

#print axioms marginal_action_entropy_causal_contrast

end D5.S3.ConceptDynamics.Information.MarginalActionEntropyCausalContrast
