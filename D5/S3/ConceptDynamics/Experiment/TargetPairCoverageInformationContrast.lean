/- GID: D5/S3/ConceptDynamics/Experiment/TargetPairCoverageInformationContrast
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Experiment/TargetPairCoverageInformationContrast
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Finite target-pair cover is structural; positive model information can miss it. -/

import D5.S3.ConceptDynamics.Interventions.TargetRelativePairUniverse
import D5.S3.ConceptDynamics.Communication.TranslationLossMonotonicity

/- Library-search audit trail (2026-08-25):
   * Exact repository hit `target_relative_pair_universe` states the target-disagreement
     pair-cover criterion for an arbitrary intervention type. It is applied directly to
     the subtype of a finite selected experiment set.
   * Exact family hits `readoutTargetLaw` and `mutualInformation` construct the statistical
     law and its information cost; neither is redeclared here.
   * `ExperimentValueIsKernelReduction.experiment_value_is_kernel_reduction` gives an
     adjacent large-output-alphabet contrast, but its large experiment is constant and
     therefore does not supply the source's positive-information clause.
   * Pinned Mathlib supplies `Sym2.fromRel`, finite product sums, and `Real.log_pos`, but no
     theorem combines finite target-pair cover with the information contrast below.
   * Local `loogle` and `leansearch` executables are absent. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.ConceptDynamics.Experiment.TargetPairCoverageInformationContrast

open D5.S3.ConceptDynamics.Communication.TranslationLossMonotonicity
open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.Interventions.TargetRelativePairUniverse
open D5.S3.Divergence.ChainRule
open D5.S3.Divergence.ClassicalDPI
open D5.S3.Entropy.Forgetting.CapacityMonotone
open D5.S3.Entropy.MutualInformation

universe u v w

/-- A finite experiment package identifies a target exactly when its separation sets cover
all target-disagreement pairs. Independently, positive mutual information about the full
model does not imply that structural criterion: a one-bit nuisance readout can distinguish
two same-target models while leaving a target-distinct pair indistinguishable. -/
theorem target_pair_coverage_and_information_contrast :
    (∀ {n : Nat} {Experiment : Type u} {Response : Type v} {Target : Type w}
        [DecidableEq Experiment] (selected : Finset Experiment)
        (readout : Experiment → Fin n → Response) (target : Fin n → Target),
      (∀ i j, target i ≠ target j →
          ∃ experiment : {candidate // candidate ∈ selected},
            readout experiment.1 i ≠ readout experiment.1 j) ↔
        Sym2.fromRel (r := fun i j => target i ≠ target j)
            ⟨fun _ _ different => different.symm⟩ ⊆
          ⋃ experiment : {candidate // candidate ∈ selected},
            Sym2.fromRel
              (r := fun i j => readout experiment.1 i ≠ readout experiment.1 j)
              ⟨fun _ _ different => different.symm⟩) ∧
      (let mass : Bool × Bool → ℝ :=
          fun model => if model.1 = false then (1 : ℝ) / 2 else 0
       let experiment : Concept (Bool × Bool) Bool := Prod.snd
       let target : Concept (Bool × Bool) Bool := Prod.fst
       mutualInformation (readoutTargetLaw mass experiment id) = Real.log 2 ∧
         experiment (false, false) ≠ experiment (false, true) ∧
         target (false, false) = target (false, true) ∧
         experiment (false, false) = experiment (true, false) ∧
         target (false, false) ≠ target (true, false) ∧
         ¬ ∃ recover : Bool → Bool, target = recover ∘ experiment) := by
  constructor
  · intro n Experiment Response Target _ selected readout target
    exact target_relative_pair_universe
      (fun experiment : {candidate // candidate ∈ selected} =>
        readout experiment.1) target
  · dsimp only
    refine ⟨?_, by decide, rfl, rfl, by decide, ?_⟩
    · norm_num [mutualInformation, klDivergence, marginal, readoutTargetLaw,
        pushforward, Fintype.sum_prod_type, Finset.sum_boole]
      ring
    · rintro ⟨recover, factorization⟩
      have atFalse := congrFun factorization (false, false)
      have atTrue := congrFun factorization (true, false)
      exact Bool.false_ne_true (atFalse.trans atTrue.symm)

#print axioms target_pair_coverage_and_information_contrast

end D5.S3.ConceptDynamics.Experiment.TargetPairCoverageInformationContrast
