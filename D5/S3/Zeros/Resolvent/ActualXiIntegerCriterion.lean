/- GID: D5/S3/Zeros/Resolvent/ActualXiIntegerCriterion
   generality: I
   mirror-B: D5/B/S3/Zeros/Resolvent/ActualXiIntegerCriterion
   mirror-E: none(waiver:actual-analytic-zero-source)
   anchors: []
   utility: none
   digest: RH failure produces a finite integer negative actual xi Hankel direction. -/

import D5.S3.Zeros.Resolvent.ActualXiDictionary
import D5.S3.Zeros.ActualZeroGeometry
import D5.S3.Constants.Moments.CountableHankelIntegerWitness

/-!
The spectrum is the complete actual positive-height zero family and keeps its
analytic multiplicities. Only the failure of standard Mathlib RH is assumed
for the negative witness. The universal all-degree sign assertion remains unproved.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace D5.S3.Zeros.Resolvent.ActualXiIntegerCriterion

open Complex D5.S3.Weil.ZeroSum
open D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds
open ActualXiFoldedSpectrum ActualXiHankelDictionary
open D5.S3.Constants.Moments.CountableHankelNegativeWitness
open scoped BigOperators ComplexConjugate

private theorem node_ne_zero (n : PositiveZero) : node n ≠ 0 :=
  inv_ne_zero (pow_ne_zero _ (gamma_ne_zero n))

private theorem weight_ne_zero (n : PositiveZero) : weight n ≠ 0 := by
  rw [weight_node]
  apply div_ne_zero
  · exact mul_ne_zero (mul_ne_zero (by norm_num)
      (by exact_mod_cast ne_of_gt (actualData.multiplicity_pos n)))
      (pow_ne_zero _ (node_ne_zero n))
  · exact node_denominator_ne_zero n

private theorem node_large_finite (r : ℝ) (hr : 0 < r) :
    {n : PositiveZero | r ≤ ‖node n‖}.Finite := by
  have hF : {n : ℕ | ‖actualData.gamma n‖ ≤ r⁻¹}.Finite :=
    actualData.locallyFinite r⁻¹
  have hpre := hF.preimage (f := fun n : PositiveZero => (n : ℕ)) Subtype.val_injective.injOn
  apply hpre.subset
  intro n hn
  change ‖actualData.gamma n‖ ≤ r⁻¹
  have hg := gamma_norm_gt_one n
  have hgp : 0 < ‖actualData.gamma n‖ ^ 2 := by positivity
  have hm : r * ‖actualData.gamma n‖ ^ 2 ≤ 1 := by
    have h := hn
    rw [Set.mem_ofPred_eq, node_norm, inv_eq_one_div] at h
    exact (le_div_iff₀ hgp).mp h
  rw [inv_eq_one_div]
  apply (le_div_iff₀ hr).mpr
  have hg2 : ‖actualData.gamma n‖ ≤ ‖actualData.gamma n‖ ^ 2 := by nlinarith
  exact (mul_le_mul_of_nonneg_right hg2 hr.le).trans (by nlinarith [hm])

private theorem rh_failure_nonreal (hRH : ¬ RiemannHypothesis) :
    ∃ n : PositiveZero, conj (node n) ≠ node n := by
  classical
  have hfail : ¬ ∀ n : ℕ, (actualData.zero n).re = (1 : ℝ) / 2 := by
    intro hall
    apply hRH
    apply D5.S3.Zeros.ActualZeroGeometry.rh_iff_nontrivial_zeros_on_line.mpr
    intro rho hrho
    obtain ⟨n, hn⟩ := actualData.zero_exhaustive (by exact hrho)
    rw [← hn]
    exact hall n
  push Not at hfail
  obtain ⟨n, hn⟩ := hfail
  have him : (actualData.zero n).im ≠ 0 := by
    intro h
    have := actual_ordinate_sq_gt_one n
    rw [h] at this
    norm_num at this
  have target (k : PositiveZero) (hk : (actualData.zero k).re ≠ (1 : ℝ) / 2) :
      conj (node k) ≠ node k := by
    intro heq
    apply hk
    apply (node_real_iff k).mp
    have h := congrArg Complex.im heq
    simp only [Complex.conj_im] at h
    linarith
  rcases lt_or_gt_of_ne him with hnneg | hnpos
  · let k : PositiveZero := ⟨actualData.conjugation n, by
      simpa only [actualData.zero_conjugation, Complex.conj_im] using neg_pos.mpr hnneg⟩
    refine ⟨k, target k ?_⟩
    simpa only [k, actualData.zero_conjugation, Complex.conj_re] using hn
  · exact ⟨⟨n, hnpos⟩, target ⟨n, hnpos⟩ hn⟩

/-- Failure of Mathlib RH gives a finite integer direction with strictly
negative unshifted actual xi derivative Hankel form. -/
theorem actual_xi_integer_negative_of_not_rh (hRH : ¬ RiemannHypothesis) :
    ∃ N : ℕ, ∃ u : Fin (N + 1) → ℤ,
      (∑ a : Fin (N + 1), ∑ b : Fin (N + 1),
        (u a : ℝ) * (u b : ℝ) * xiCoefficient ((a : ℕ) + (b : ℕ))) < 0 := by
  obtain ⟨n, hn⟩ := rh_failure_nonreal hRH
  obtain ⟨N, u, hu⟩ := exists_integer_negative node weight conjugation
    (fun i => (node_norm_lt_one i).le) node_injective node_conjugation weight_conjugation
    weight_norm_summable node_large_finite n hn (weight_ne_zero n)
  refine ⟨N, u, ?_⟩
  have hid := actual_xi_hankel_identity N 0 (fun a => (u a : ℝ))
  simp only [mul_zero, zero_add, pow_zero, one_mul, Complex.ofReal_intCast] at hid
  rw [hid]
  exact hu

/-- RH is equivalent to nonnegativity in every degree for every integer
coefficient vector. This does not assert either side unconditionally. -/
theorem rh_iff_actual_xi_integer_hankel_nonnegative :
    RiemannHypothesis ↔ ∀ (N : ℕ) (u : Fin (N + 1) → ℤ),
      0 ≤ ∑ a : Fin (N + 1), ∑ b : Fin (N + 1),
        (u a : ℝ) * (u b : ℝ) * xiCoefficient ((a : ℕ) + (b : ℕ)) := by
  constructor
  · intro hRH N u
    simpa only [mul_zero, zero_add] using
      actual_xi_hankel_nonnegative_of_rh hRH N 0 (fun a => (u a : ℝ))
  · intro hpos
    by_contra hRH
    obtain ⟨N, u, hu⟩ := actual_xi_integer_negative_of_not_rh hRH
    exact (not_lt_of_ge (hpos N u)) hu

end D5.S3.Zeros.Resolvent.ActualXiIntegerCriterion
