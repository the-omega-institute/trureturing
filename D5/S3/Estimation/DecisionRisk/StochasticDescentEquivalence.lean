/- GID: D5/S3/Estimation/DecisionRisk/StochasticDescentEquivalence
   generality: G
   mirror-B: D5/B/S3/Estimation/DecisionRisk/StochasticDescentEquivalence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Stochastic descent, lumpability, and observed-law factorization are equivalent. -/

import Mathlib.Data.List.TFAE
import Mathlib.Probability.ProbabilityMassFunction.Constructions

/- Library-search audit trail (2026-08-25):
   * The adjacent frozen D5 theorem
     `strongly_lumpable_iff_exact_quotient_kernel` starts from real-valued
     observed rows and factors over all of the codomain. It neither pushes a
     state kernel through the readout nor constructs a kernel on its effective
     image, so it is not an exact bind.
   * Repository body-shape searches for PMF laws on `Set.range`, subtype PMFs,
     and PMF maps through `Set.mem_range_self` found no duplicate construction.
   * Exact pinned-Mathlib hits `Set.rangeFactorization`, `Set.rangeSplitting`,
     `Set.apply_rangeSplitting`, `PMF.map_comp`, and `List.TFAE` supply the
     canonical effective-image maps, probability pushforward, and equivalence
     packaging. No library theorem packages all three clauses below. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Estimation.DecisionRisk.StochasticDescentEquivalence

/-- For a discrete Markov transition law, exact descent to the effective
readout image, strong lumpability, and factorization of the one-step observed
law through the current readout are equivalent. -/
theorem stochastic_descent_equivalence
    {X B : Type*} (q : X -> B) (K : X -> PMF X) :
    List.TFAE [
      ∃ quotientKernel : Set.range q -> PMF (Set.range q),
        ∀ x, (K x).map q =
          (quotientKernel (Set.rangeFactorization q x)).map Subtype.val,
      ∀ x y, q x = q y -> (K x).map q = (K y).map q,
      ∃ observedTransition : Set.range q -> PMF B,
        ∀ x, (K x).map q =
          observedTransition (Set.rangeFactorization q x)] := by
  classical
  tfae_have 1 -> 2 := by
    rintro ⟨quotientKernel, descends⟩ x y sameReadout
    have sameEffectiveReadout :
        Set.rangeFactorization q x = Set.rangeFactorization q y :=
      (Set.rangeFactorization_eq_rangeFactorization_iff x y).2 sameReadout
    rw [descends x, descends y, sameEffectiveReadout]
  tfae_have 2 -> 1 := by
    intro lumpable
    let quotientKernel : Set.range q -> PMF (Set.range q) := fun readout =>
      (K (Set.rangeSplitting q readout)).map (Set.rangeFactorization q)
    refine ⟨quotientKernel, ?_⟩
    intro x
    have representativeReadout :
        q (Set.rangeSplitting q (Set.rangeFactorization q x)) = q x := by
      simpa using Set.apply_rangeSplitting q (Set.rangeFactorization q x)
    have sameObservedLaw :=
      lumpable (Set.rangeSplitting q (Set.rangeFactorization q x)) x
        representativeReadout
    calc
      (K x).map q =
          (K (Set.rangeSplitting q (Set.rangeFactorization q x))).map q :=
        sameObservedLaw.symm
      _ = ((K (Set.rangeSplitting q (Set.rangeFactorization q x))).map
            (Set.rangeFactorization q)).map Subtype.val := by
        rw [PMF.map_comp]
        rfl
      _ = (quotientKernel (Set.rangeFactorization q x)).map Subtype.val := rfl
  tfae_have 2 -> 3 := by
    intro lumpable
    let observedTransition : Set.range q -> PMF B := fun readout =>
      (K (Set.rangeSplitting q readout)).map q
    refine ⟨observedTransition, ?_⟩
    intro x
    have representativeReadout :
        q (Set.rangeSplitting q (Set.rangeFactorization q x)) = q x := by
      simpa using Set.apply_rangeSplitting q (Set.rangeFactorization q x)
    exact (lumpable
      (Set.rangeSplitting q (Set.rangeFactorization q x)) x
      representativeReadout).symm
  tfae_have 3 -> 2 := by
    rintro ⟨observedTransition, factors⟩ x y sameReadout
    have sameEffectiveReadout :
        Set.rangeFactorization q x = Set.rangeFactorization q y :=
      (Set.rangeFactorization_eq_rangeFactorization_iff x y).2 sameReadout
    rw [factors x, factors y, sameEffectiveReadout]
  tfae_finish

#print axioms stochastic_descent_equivalence

end D5.S3.Estimation.DecisionRisk.StochasticDescentEquivalence
