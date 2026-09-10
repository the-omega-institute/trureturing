/- GID: D5/S3/Weil/ZetaBridge/WeilGammaLogarithmicSeed
   generality: I
   mirror-B: D5/B/S3/Weil/ZetaBridge/WeilGammaLogarithmicSeed
   mirror-E: none(waiver:Gamma-realization-and-form-domain-transport)
   anchors: []
   utility: none
   digest: Evaluate the actual cutoff polynomial seed's singular Gamma remainder by finite endpoint powers, proving integrability and removing the lower-endpoint singularity. -/

import D5.S3.Weil.ZetaBridge.WeilMellinPrimeIntertwining
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The logarithmic Gamma remainder of the actual polynomial Mellin seed

The preceding prime identity reduces the arithmetic action to E(log(t)h).
The forward Gamma calculation leaves the specific integral

  integral_u^lambda t * (h(t)-h(u)) / (t^2-u^2) dt.

Here h is exactly the existing `cutPolynomialSeed`, and lambda=exp(a).
The theorem evaluates that integral, including its integrability, with no
quadrature or supplied integral identity. The integrand's value at t=u is
irrelevant: the proof identifies it with a continuous polynomial on (u,lambda].

The singular Gamma multiplier, the full forward-action identity and the
unbounded-form error estimate are separate paper results in the existing RH
volume. This theorem does not assert those operator/domain identifications,
a small full residual, a spectral gap or an Xi limit.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace D5.S3.Weil.ZetaBridge.WeilGammaLogarithmicSeed

open MeasureTheory Set
open scoped BigOperators
open D5.S3.Weil.ZetaBridge.WeilMellinPrimeIntertwining

private def regularRemainder (d : ℕ) (A : ℕ → ℂ) (u t : ℝ) : ℂ :=
  ∑ r ∈ Finset.range d, A r * ∑ j ∈ Finset.range r,
    (t : ℂ) ^ (2 * j + 1) * (u : ℂ) ^ (2 * (r - 1 - j))

private theorem monomial_quotient (r : ℕ) {u t : ℝ} (hu : 0 < u) (hut : u < t) :
    (t : ℂ) * ((t : ℂ) ^ (2 * r) - (u : ℂ) ^ (2 * r)) /
        ((t : ℂ) ^ 2 - (u : ℂ) ^ 2) =
      ∑ j ∈ Finset.range r,
        (t : ℂ) ^ (2 * j + 1) * (u : ℂ) ^ (2 * (r - 1 - j)) := by
  have hdR : t ^ 2 - u ^ 2 ≠ 0 := by
    have ht : 0 < t := hu.trans hut
    nlinarith
  have hd : (t : ℂ) ^ 2 - (u : ℂ) ^ 2 ≠ 0 := by exact_mod_cast hdR
  have hg : (∑ j ∈ Finset.range r,
      (t : ℂ) ^ (2 * j) * (u : ℂ) ^ (2 * (r - 1 - j))) *
      ((t : ℂ) ^ 2 - (u : ℂ) ^ 2) =
      (t : ℂ) ^ (2 * r) - (u : ℂ) ^ (2 * r) := by
    simpa only [pow_mul] using
      (Commute.all ((t : ℂ) ^ 2) ((u : ℂ) ^ 2)).geom_sum₂_mul r
  calc
    _ = (t : ℂ) * ∑ j ∈ Finset.range r,
        (t : ℂ) ^ (2 * j) * (u : ℂ) ^ (2 * (r - 1 - j)) := by
      rw [← hg]
      field_simp [hd]
      <;> ring
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [pow_succ]
      ring

private theorem integrand_eq_regular (a : ℝ) (d : ℕ) (A : ℕ → ℂ)
    {u t : ℝ} (hu : 0 < u) (hul : u ≤ Real.exp a)
    (hut : u < t) (htl : t ≤ Real.exp a) :
    (t : ℂ) * (cutPolynomialSeed a d A t - cutPolynomialSeed a d A u) /
        ((t : ℂ) ^ 2 - (u : ℂ) ^ 2) = regularRemainder d A u t := by
  rw [cutPolynomialSeed, if_pos htl, cutPolynomialSeed, if_pos hul,
    ← Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_div]
  unfold regularRemainder
  apply Finset.sum_congr rfl
  intro r _
  calc
    _ = A r * ((t : ℂ) * ((t : ℂ) ^ (2 * r) - (u : ℂ) ^ (2 * r)) /
        ((t : ℂ) ^ 2 - (u : ℂ) ^ 2)) := by ring
    _ = _ := by rw [monomial_quotient r hu hut]

private theorem integral_complex_nat_power (u v : ℝ) (n : ℕ) :
    (∫ t : ℝ in u..v, (t : ℂ) ^ n) =
      ((v : ℂ) ^ (n + 1) - (u : ℂ) ^ (n + 1)) / ((n + 1 : ℕ) : ℂ) := by
  simp_rw [← Complex.ofReal_pow]
  rw [intervalIntegral.integral_ofReal, integral_pow]
  push_cast
  <;> rfl

/-- The actual singular Gamma remainder of the previously owned polynomial
seed is integrable and has a complete finite endpoint evaluation. No boundary
moment is set to zero. Degree zero and the degenerate interval are included. -/
theorem gamma_logarithmic_seed_remainder (a : ℝ) (d : ℕ) (A : ℕ → ℂ)
    (u : ℝ) (hu : 0 < u) (hul : u ≤ Real.exp a) :
    IntervalIntegrable
      (fun t : ℝ => (t : ℂ) *
        (cutPolynomialSeed a d A t - cutPolynomialSeed a d A u) /
          ((t : ℂ) ^ 2 - (u : ℂ) ^ 2)) volume u (Real.exp a) ∧
    (∫ t : ℝ in u..Real.exp a, (t : ℂ) *
      (cutPolynomialSeed a d A t - cutPolynomialSeed a d A u) /
        ((t : ℂ) ^ 2 - (u : ℂ) ^ 2)) =
      ∑ r ∈ Finset.range d, A r * ∑ j ∈ Finset.range r,
        (((Real.exp a : ℝ) : ℂ) ^ (2 * j + 2) - (u : ℂ) ^ (2 * j + 2)) /
          ((2 * j + 2 : ℕ) : ℂ) * (u : ℂ) ^ (2 * (r - 1 - j)) := by
  have hc : Continuous (regularRemainder d A u) := by
    unfold regularRemainder
    fun_prop
  have hi := hc.intervalIntegrable (μ := volume) u (Real.exp a)
  have hae : regularRemainder d A u =ᵐ[volume.restrict (uIoc u (Real.exp a))]
      (fun t : ℝ => (t : ℂ) *
        (cutPolynomialSeed a d A t - cutPolynomialSeed a d A u) /
          ((t : ℂ) ^ 2 - (u : ℂ) ^ 2)) := by
    rw [uIoc_of_le hul]
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact (integrand_eq_regular a d A hu hul ht.1 ht.2).symm
  refine ⟨hi.congr_ae hae, ?_⟩
  calc
    _ = ∫ t : ℝ in u..Real.exp a, regularRemainder d A u t :=
      intervalIntegral.integral_congr_ae'
        (Filter.Eventually.of_forall (fun t ht => integrand_eq_regular a d A hu hul ht.1 ht.2))
        (Filter.Eventually.of_forall (fun t ht => by
          exact False.elim ((not_lt_of_ge hul) (ht.1.trans_le ht.2))))
    _ = _ := by
      unfold regularRemainder
      rw [intervalIntegral.integral_finsetSum (fun r _ =>
        (show Continuous (fun t : ℝ => A r * ∑ j ∈ Finset.range r,
          (t : ℂ) ^ (2 * j + 1) * (u : ℂ) ^ (2 * (r - 1 - j))) by fun_prop).intervalIntegrable _ _)]
      apply Finset.sum_congr rfl
      intro r _
      rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_finsetSum (fun j _ =>
          (show Continuous (fun t : ℝ => (t : ℂ) ^ (2 * j + 1) *
            (u : ℂ) ^ (2 * (r - 1 - j))) by fun_prop).intervalIntegrable _ _)]
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      rw [intervalIntegral.integral_mul_const, integral_complex_nat_power]

#print axioms gamma_logarithmic_seed_remainder

end D5.S3.Weil.ZetaBridge.WeilGammaLogarithmicSeed
