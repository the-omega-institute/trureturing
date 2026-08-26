/- GID: D5/S3/Observer/ProbabilisticClosure/TransitiveInvariantDistribution
   generality: G
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TransitiveInvariantDistribution
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A transitive action admits exactly the uniform invariant probability mass function. -/

import Mathlib.Algebra.Group.Action.Pretransitive
import Mathlib.Probability.Distributions.Uniform

/- Library-search audit trail (2026-08-26):
   * Exact pinned-Mathlib hits `MulAction.exists_smul_eq` and
     `PMF.uniformOfFintype_apply` supply transitivity and the uniform point
     mass; both are applied directly.
   * Repository and pinned-Mathlib searches found no theorem packaging the
     existence, uniqueness, invariance, and pointwise cardinality clauses.
   * The source assumes a finite group, but the proof only needs a group
     acting transitively on a finite nonempty carrier, so no finiteness
     hypothesis on the acting group is imposed. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Observer.ProbabilisticClosure.TransitiveInvariantDistribution

/-- On a finite nonempty carrier with a transitive group action, the uniform
probability mass function is the unique invariant law, and every invariant law
has point mass equal to the reciprocal of the carrier cardinality. -/
theorem transitive_invariant_distribution_unique_uniform
    {G A : Type*} [Group G] [Fintype A] [Nonempty A]
    [MulAction G A] [MulAction.IsPretransitive G A] :
    (ExistsUnique fun mu : PMF A =>
      forall g : G, forall a : A, mu (g • a) = mu a) /\
      forall mu : PMF A,
        (forall g : G, forall a : A, mu (g • a) = mu a) ->
          forall a : A, mu a = (Fintype.card A : ENNReal)⁻¹ := by
  classical
  have invariant_eq_uniform (mu : PMF A)
      (hinvariant : forall g : G, forall a : A, mu (g • a) = mu a) :
      mu = PMF.uniformOfFintype A := by
    apply PMF.ext
    intro a
    have hconstant : forall b : A, mu b = mu a := by
      intro b
      obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G a b
      rw [← hg, hinvariant]
    have hsum :
        (∑ b : A, mu b) =
          ∑ b : A, PMF.uniformOfFintype A b := by
      have hmu : (∑ b : A, mu b) = 1 := by
        simpa only [tsum_fintype] using mu.tsum_coe
      have huniform : (∑ b : A, PMF.uniformOfFintype A b) = 1 := by
        simpa only [tsum_fintype] using (PMF.uniformOfFintype A).tsum_coe
      exact hmu.trans huniform.symm
    have hcard_mul :
        (Fintype.card A : ENNReal) * mu a =
          (Fintype.card A : ENNReal) * PMF.uniformOfFintype A a := by
      calc
        (Fintype.card A : ENNReal) * mu a = ∑ _b : A, mu a := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        _ = ∑ b : A, mu b := by
          apply Finset.sum_congr rfl
          intro b _
          exact (hconstant b).symm
        _ = ∑ b : A, PMF.uniformOfFintype A b := hsum
        _ = ∑ _b : A, PMF.uniformOfFintype A a := by
          apply Finset.sum_congr rfl
          intro b _
          simp only [PMF.uniformOfFintype_apply]
        _ = (Fintype.card A : ENNReal) * PMF.uniformOfFintype A a := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact (ENNReal.mul_right_inj
      (by exact_mod_cast Fintype.card_ne_zero)
      (ENNReal.natCast_ne_top (Fintype.card A))).mp hcard_mul
  constructor
  · refine ⟨PMF.uniformOfFintype A, ?_, ?_⟩
    · intro g a
      simp only [PMF.uniformOfFintype_apply]
    · intro mu hinvariant
      exact invariant_eq_uniform mu hinvariant
  · intro mu hinvariant a
    rw [invariant_eq_uniform mu hinvariant, PMF.uniformOfFintype_apply]

#print axioms transitive_invariant_distribution_unique_uniform

end D5.S3.Observer.ProbabilisticClosure.TransitiveInvariantDistribution
