/- GID: D5/S3/ConceptDynamics/RefinementGeometry/FixedObservationDominanceAsymmetry
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/RefinementGeometry/FixedObservationDominanceAsymmetry
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Complete dominance is asymmetric for a fixed indexed observation language. -/

import D5.S3.ConceptDynamics.Faithfulness.JointFaithfulnessLeibnizCriterion
import Mathlib.Data.Sym.Sym2

/- Library-search audit trail (2026-08-26):
   * Searches for fixed-observation dominance, asymmetry, and the conjunction
     shapes `aa = ab /\ ab != bb` and `bb = ab /\ ab != aa` found no exact D5
     theorem on realized unordered genotypes.
   * The exact current-tree hit `jointReadout` is the canonical dependent
     observation profile and is imported instead of being redeclared.
   * The exact pinned-Mathlib hit `Sym2.eq_swap` identifies the two presentations
     of the unordered heterozygote. Mathlib has no theorem combining that carrier
     with the source's profile-defined dominance relation. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.RefinementGeometry.FixedObservationDominanceAsymmetry

open D5.S3.ConceptDynamics.Faithfulness.JointFaithfulnessLeibnizCriterion

universe u v w z t

/-- For a deterministic realization of unordered diploid genotypes, construct
complete dominance from the joint profile of a fixed observation language.
Dominance of one allele over another excludes dominance in the reverse
direction because both directions use the same heterozygous genotype. -/
theorem fixed_observation_dominance_asymmetric
    {Allele : Type u} {Context : Type v} {State : Type w} {I : Type z}
    (Output : I -> Type t)
    (realization : Sym2 Allele -> Context -> State)
    (readout : forall i, State -> Output i)
    (a b : Allele) (context : Context) :
    let profile := jointReadout readout
    let dominates := fun left right : Allele =>
      profile (realization s(left, left) context) =
          profile (realization s(left, right) context) ∧
        profile (realization s(left, right) context) ≠
          profile (realization s(right, right) context)
    dominates a b -> Not (dominates b a) := by
  dsimp only
  intro aDominatesB bDominatesA
  apply aDominatesB.2
  calc
    jointReadout readout (realization s(a, b) context) =
        jointReadout readout (realization s(b, a) context) :=
      congrArg
        (fun genotype => jointReadout readout (realization genotype context))
        (Sym2.eq_swap (a := a) (b := b))
    _ = jointReadout readout (realization s(b, b) context) :=
      bDominatesA.1.symm

#print axioms fixed_observation_dominance_asymmetric

end D5.S3.ConceptDynamics.RefinementGeometry.FixedObservationDominanceAsymmetry
