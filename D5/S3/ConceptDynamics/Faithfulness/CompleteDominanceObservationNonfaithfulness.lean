/- GID: D5/S3/ConceptDynamics/Faithfulness/CompleteDominanceObservationNonfaithfulness
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Faithfulness/CompleteDominanceObservationNonfaithfulness
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Complete dominance requires an observation profile that is not faithful. -/

import D5.S3.ConceptDynamics.Faithfulness.JointFaithfulnessLeibnizCriterion
import Mathlib.Data.Sym.Sym2

/- Library-search audit trail (2026-09-04):
   * D5 searches for complete dominance combined with observation
     noninjectivity found no exact owner. `FixedObservationDominanceAsymmetry`
     uses the same realized unordered-genotype carrier but proves asymmetry.
   * The body-shape search for the indexed profile found `jointReadout` in
     `JointFaithfulnessLeibnizCriterion`; this module imports and applies that
     canonical construction instead of redeclaring it.
   * Loogle and LeanSearch found the generic Mathlib results
     `Function.not_injective_iff`, `Set.injOn_pair`, and `Sym2.eq_iff`, but no
     theorem combining realization, complete dominance, and observation
     language relativity. The proof applies the first and third results. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Faithfulness.CompleteDominanceObservationNonfaithfulness

open D5.S3.ConceptDynamics.Faithfulness.JointFaithfulnessLeibnizCriterion

universe u v w z t

/-- If two distinct realized genotypes have the same joint profile under a
complete-dominance observation language, that profile is not injective on the
three relevant states. No coordinate already in the language can recover every
genotype, while a predicate on the internal state can distinguish the latent
pair; complete dominance is therefore relative to the chosen language. -/
theorem complete_dominance_observation_nonfaithfulness
    {Allele : Type u} {Context : Type v} {State : Type w} {I : Type z}
    (Output : I -> Type t)
    (realization : Sym2 Allele -> Context -> State)
    (readout : forall i, State -> Output i)
    (a b : Allele) (context : Context)
    (realizationsDistinct :
      realization s(a, a) context ≠ realization s(a, b) context)
    (completeDominance :
      jointReadout readout (realization s(a, a) context) =
          jointReadout readout (realization s(a, b) context) /\
        jointReadout readout (realization s(a, b) context) ≠
          jointReadout readout (realization s(b, b) context)) :
    Not (Set.InjOn (jointReadout readout)
        {realization s(a, a) context, realization s(a, b) context,
          realization s(b, b) context}) /\
      (forall i, Not (Function.Injective
        (fun genotype => readout i (realization genotype context)))) /\
      (exists distinguishingReadout : State -> Prop,
        distinguishingReadout (realization s(a, a) context) ≠
          distinguishingReadout (realization s(a, b) context)) := by
  have allelesDistinct : a ≠ b := by
    intro equalAlleles
    subst b
    exact completeDominance.2 rfl
  constructor
  · intro profileInjective
    apply realizationsDistinct
    exact profileInjective (by simp) (by simp) completeDominance.1
  constructor
  · intro i
    rw [Function.not_injective_iff]
    refine Exists.intro s(a, a) <| Exists.intro s(a, b) ?_
    constructor
    · exact congrFun completeDominance.1 i
    · intro genotypeEquality
      rcases Sym2.eq_iff.mp genotypeEquality with direct | swapped
      · exact allelesDistinct direct.2
      · exact allelesDistinct swapped.1
  · refine Exists.intro
      (fun state => state = realization s(a, a) context) ?_
    intro propositionEquality
    apply realizationsDistinct
    exact (Eq.mp propositionEquality rfl).symm

#print axioms complete_dominance_observation_nonfaithfulness

end D5.S3.ConceptDynamics.Faithfulness.CompleteDominanceObservationNonfaithfulness
