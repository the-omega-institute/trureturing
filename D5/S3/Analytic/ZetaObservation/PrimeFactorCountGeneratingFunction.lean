/- GID: D5/S3/Analytic/ZetaObservation/PrimeFactorCountGeneratingFunction
   generality: I
   mirror-B: D5/B/S3/Analytic/ZetaObservation/PrimeFactorCountGeneratingFunction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Distinct-prime PGF has a convergent Euler product, with 0 and 1 audited. -/
/- Library-search audit trail (2026-08-25):
   * `PrimeFactorCountMoments.primeFactorCount` is reused as the unique FPOD omega.
   * `prime_support_bits_independent_bernoulli` supplies the independent support bits.
   * `primeEvidence_summable` and `multipliable_one_add_of_summable` prove convergence.
   * `iIndepFun.integral_fun_prod_eq_prod_integral` proves every finite product identity.
   * `tendsto_integral_filter_of_dominated_convergence` passes to the infinite product.
   * `PMF.integral_eq_tsum`, `ProbabilityTheory.moment`, `Real.rpow`, and `ENNReal.tsum`
     were inspected; the PMF theorem and `Real.rpow` are used, while moment and ENNReal
     summation are not the right interfaces for this probability generating function.
   * Searches of D5 and pinned Mathlib found no existing zeta-law prime-support PGF. -/

import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import D5.S3.Analytic.ZetaObservation.PrimeFactorCountMoments

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Analytic.ZetaObservation.PrimeFactorCountGeneratingFunction

open scoped BigOperators ENNReal
open MeasureTheory ProbabilityTheory
open D5.S3.Analytic.ZetaGibbs
open D5.S3.Analytic.ZetaEntropyPlane.PrimeEvidenceSharpThreshold
open D5.S3.Analytic.ZetaObservation.MultiplicativeComplexityActivation
open D5.S3.Analytic.ZetaObservation.PrimeSupportBernoulliIndependence
open D5.S3.Analytic.ZetaObservation.PrimeFactorCountMoments

noncomputable section

/-!
This module proves fallback layer (b): the full distinct-prime PGF, including convergence of its
Euler product. The source gives no explicit convergence domain for the multiplicity-counting PGF.
That second formula remains open rather than being silently replaced by a chosen sufficient domain.

Primality load audit: convergence uses no prime-distribution theorem beyond the already proved
summability of `primeEvidence`; the same argument works for any summable real family. The finite
expectation factorization uses mutual independence. In this zeta model that independence comes
from unique factorization through the imported prime-coordinate theorem, so primality is
load-bearing there but not in the abstract finite-product argument.

Hypothesis and degeneration audit: `1 < s` constructs `zetaDist` and supplies summability. The
bounds `0 <= z` and `z <= 1` are both used for the dominated-convergence bound and match the source
domain. They are not claimed to be the maximal analytic domain. Empty finite prime sets give the
constant product one; singleton sets reduce to the imported Bernoulli marginal. At `z = 1` the PGF
is total mass one. At `z = 0`, Mathlib's totalized omega also vanishes at zero, but the zeta mass of
zero is zero, leaving exactly the mass of `N = 1`. There are no public typeclass hypotheses.
-/

/-- The probability generating function of the distinct-prime count under the zeta law. -/
def primeFactorCountPGF (s : Real) (hs : 1 < s) (z : Real) : Real :=
  integral (zetaDist s hs).toMeasure fun n => z ^ primeFactorCount n

/-- The one-prime Euler factor in the distinct-prime probability generating function. -/
def primeFactorCountEulerFactor (s z : Real) (p : Nat.Primes) : Real :=
  1 - (1 - z) * primeEvidence s p

private def supportPGFCoordinate (z : Real) (p : Nat.Primes) (n : Nat) : Real :=
  if 0 < n.factorization p.1 then z else 1

/-- The Euler factors are multipliable; only summability of the parameter family is needed. -/
theorem prime_factor_count_euler_factors_multipliable (s z : Real) (hs : 1 < s) :
    Multipliable (primeFactorCountEulerFactor s z) := by
  have hscaled : Summable (fun p : Nat.Primes => (z - 1) * primeEvidence s p) :=
    (primeEvidence_summable s hs).mul_left (z - 1)
  have hproduct : Multipliable (fun p : Nat.Primes => 1 + (z - 1) * primeEvidence s p) :=
    multipliable_one_add_of_summable hscaled.norm
  exact hproduct.congr fun p => by
    simp only [primeFactorCountEulerFactor]
    ring

#print axioms prime_factor_count_euler_factors_multipliable

private theorem support_pgf_coordinate_integral
    (s z : Real) (hs : 1 < s) (p : Nat.Primes) :
    integral (zetaDist s hs).toMeasure (supportPGFCoordinate z p) =
      primeFactorCountEulerFactor s z p := by
  let parameter : unitInterval :=
    ⟨primeEvidence s p, (primeEvidence_pos s p).le,
      Real.rpow_le_one_of_one_le_of_nonpos
        (by exact_mod_cast p.2.one_lt.le) (by linarith)⟩
  have hlaw := (prime_support_bits_independent_bernoulli s hs).1 p
  have hintegral := hlaw.integral_comp
    (f := fun bit : Bool => if bit then z else 1)
    (by fun_prop)
  have htransport :
      integral (zetaDist s hs).toMeasure (supportPGFCoordinate z p) =
        integral (bernoulliMeasure true false parameter)
          (fun bit : Bool => if bit then z else 1) := by
    rw [show supportPGFCoordinate z p =
        (fun bit : Bool => if bit then z else 1) ∘
          (fun n : Nat => decide (0 < n.factorization p.1)) by
      funext n
      simp [supportPGFCoordinate]]
    simpa only [parameter, primeEvidence] using hintegral
  rw [htransport, integral_bernoulliMeasure]
  norm_num [parameter, primeFactorCountEulerFactor]
  ring

private theorem finite_support_pgf_integral
    (s z : Real) (hs : 1 < s) (P : Finset Nat.Primes) :
    integral (zetaDist s hs).toMeasure
        (fun n => ∏ p ∈ P, supportPGFCoordinate z p n) =
      ∏ p ∈ P, primeFactorCountEulerFactor s z p := by
  let X : P → Nat → Real := fun p n => supportPGFCoordinate z p.1 n
  have hbits := (prime_support_bits_independent_bernoulli s hs).2.restrict P
  have hX : iIndepFun X (zetaDist s hs).toMeasure := by
    have hcomp := hbits.comp
      (fun (_ : P) (bit : Bool) => if bit then z else 1)
      (fun _ => Measurable.of_discrete)
    convert hcomp using 1
    funext p n
    simp [X, supportPGFCoordinate]
  have hfinite := hX.integral_fun_prod_eq_prod_integral (fun _ => by fun_prop)
  rw [show (fun n => ∏ p ∈ P, supportPGFCoordinate z p n) =
      fun n => ∏ p : P, X p n by
    funext n
    exact (Finset.prod_coe_sort P fun p => supportPGFCoordinate z p n).symm]
  rw [hfinite]
  change (∏ p : P, integral (zetaDist s hs).toMeasure
      (supportPGFCoordinate z p.1)) = _
  calc
    (∏ p : P, integral (zetaDist s hs).toMeasure
        (supportPGFCoordinate z p.1)) =
        ∏ p ∈ P, integral (zetaDist s hs).toMeasure
          (supportPGFCoordinate z p) := by
      exact Finset.prod_coe_sort P
        (fun p : Nat.Primes =>
          integral (zetaDist s hs).toMeasure (supportPGFCoordinate z p))
    _ = ∏ p ∈ P, primeFactorCountEulerFactor s z p := by
      apply Finset.prod_congr rfl
      intro p hp
      exact support_pgf_coordinate_integral s z hs p

private theorem support_pgf_coordinate_hasProd
    (z : Real) (hz : 0 <= z) (n : Nat) :
    HasProd (fun p : Nat.Primes => supportPGFCoordinate z p n)
      (z ^ primeFactorCount n) := by
  let support : Finset Nat.Primes := (occupied_prime_modes_finite n).toFinset
  have houtside : forall p : Nat.Primes, p ∉ support → supportPGFCoordinate z p n = 1 := by
    intro p hp
    have hzero : primeOccupancy p n = 0 := by
      by_contra hne
      exact hp (by simpa [support] using hne)
    have hfactor : n.factorization p.1 = 0 := by
      simpa [primeOccupancy] using hzero
    simp [supportPGFCoordinate, hfactor]
  have hsum :
      ∑ p ∈ support, primeSupportIndicator p n =
        ∑' p : Nat.Primes, primeSupportIndicator p n := by
    rw [tsum_eq_sum (s := support)]
    intro p hp
    have hzero : primeOccupancy p n = 0 := by
      by_contra hne
      exact hp (by simpa [support] using hne)
    have hfactor : n.factorization p.1 = 0 := by
      simpa [primeOccupancy] using hzero
    simp [primeSupportIndicator, hfactor]
  have hprod :
      ∏ p ∈ support, supportPGFCoordinate z p n = z ^ primeFactorCount n := by
    calc
      ∏ p ∈ support, supportPGFCoordinate z p n =
          ∏ p ∈ support, z ^ primeSupportIndicator p n := by
        apply Finset.prod_congr rfl
        intro p hp
        simp [supportPGFCoordinate, primeSupportIndicator]
      _ = z ^ (∑ p ∈ support, primeSupportIndicator p n) := by
        symm
        exact Real.rpow_sum_of_nonneg hz
          (fun p hp => by
            unfold primeSupportIndicator
            split <;> norm_num)
      _ = z ^ (∑' p : Nat.Primes, primeSupportIndicator p n) := by rw [hsum]
      _ = z ^ primeFactorCount n := by rw [← primeFactorCount_eq_tsum_support]
  rw [← hprod]
  exact hasProd_prod_of_ne_finset_one houtside

private theorem finite_support_pgf_norm_le_one
    (z : Real) (hz0 : 0 <= z) (hz1 : z <= 1) (P : Finset Nat.Primes) (n : Nat) :
    ‖∏ p ∈ P, supportPGFCoordinate z p n‖ <= 1 := by
  rw [Real.norm_eq_abs, abs_of_nonneg]
  · exact Finset.prod_le_one
      (fun p hp => by
        unfold supportPGFCoordinate
        split <;> linarith)
      (fun p hp => by
        unfold supportPGFCoordinate
        split <;> linarith)
  · exact Finset.prod_nonneg fun p hp => by
      unfold supportPGFCoordinate
      split <;> linarith

/-- For `0 <= z <= 1`, the distinct-prime PGF is its convergent prime Euler product. -/
theorem prime_factor_count_pgf_euler_product
    (s z : Real) (hs : 1 < s) (hz0 : 0 <= z) (hz1 : z <= 1) :
    primeFactorCountPGF s hs z =
      (∏' p : Nat.Primes, primeFactorCountEulerFactor s z p) := by
  let truncation : Finset Nat.Primes → Nat → Real :=
    fun P n => ∏ p ∈ P, supportPGFCoordinate z p n
  have hmeas : Filter.Eventually
      (fun P => AEStronglyMeasurable (truncation P) (zetaDist s hs).toMeasure)
      (Filter.atTop : Filter (Finset Nat.Primes)) := by
    filter_upwards with P
    fun_prop
  have hbound : Filter.Eventually
      (fun P => ∀ᵐ n ∂(zetaDist s hs).toMeasure, ‖truncation P n‖ <= (1 : Real))
      (Filter.atTop : Filter (Finset Nat.Primes)) := by
    filter_upwards with P
    filter_upwards with n
    exact finite_support_pgf_norm_le_one z hz0 hz1 P n
  have hlimit : ∀ᵐ n ∂(zetaDist s hs).toMeasure,
      Filter.Tendsto (fun P : Finset Nat.Primes => truncation P n) Filter.atTop
        (nhds (z ^ primeFactorCount n)) := by
    filter_upwards with n
    exact support_pgf_coordinate_hasProd z hz0 n
  have hintegral := tendsto_integral_filter_of_dominated_convergence
    (F := truncation) (f := fun n => z ^ primeFactorCount n) (fun _ => (1 : Real))
    hmeas hbound (integrable_const 1) hlimit
  have hintegral' :
      Filter.Tendsto
        (fun P : Finset Nat.Primes =>
          ∏ p ∈ P, primeFactorCountEulerFactor s z p)
        Filter.atTop (nhds (primeFactorCountPGF s hs z)) := by
    simpa only [truncation, finite_support_pgf_integral, primeFactorCountPGF] using hintegral
  have hproduct := (prime_factor_count_euler_factors_multipliable s z hs).hasProd
  exact tendsto_nhds_unique hintegral' hproduct

#print axioms prime_factor_count_pgf_euler_product

/-- At `z = 1`, the distinct-prime PGF is the total probability one. -/
theorem prime_factor_count_pgf_at_one (s : Real) (hs : 1 < s) :
    primeFactorCountPGF s hs 1 = 1 := by
  simp [primeFactorCountPGF]

#print axioms prime_factor_count_pgf_at_one

/-- At `z = 0`, the distinct-prime PGF is exactly the zeta-law mass of `N = 1`. -/
theorem prime_factor_count_pgf_at_zero (s : Real) (hs : 1 < s) :
    primeFactorCountPGF s hs 0 = (zetaDist s hs 1).toReal := by
  have hintegrable : Integrable (fun n : Nat => (0 : Real) ^ primeFactorCount n)
      (zetaDist s hs).toMeasure := by
    apply (integrable_const (1 : Real)).mono Measurable.of_discrete.aestronglyMeasurable
    filter_upwards with n
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.zero_rpow_nonneg _)]
    simpa using Real.zero_rpow_le_one (primeFactorCount n)
  rw [primeFactorCountPGF, PMF.integral_eq_tsum _ _ hintegrable]
  rw [tsum_eq_single 1]
  · simp [primeFactorCount]
  · intro n hn
    by_cases hnzero : n = 0
    · subst n
      simp [zeta_dist_apply, weight_zero s (by linarith)]
    · have hnlarge : 1 < n := by omega
      have hcount : primeFactorCount n ≠ 0 := by
        change (ArithmeticFunction.cardDistinctFactors n : Real) ≠ 0
        exact_mod_cast (ArithmeticFunction.cardDistinctFactors_pos.mpr hnlarge).ne'
      simp [Real.zero_rpow hcount]

#print axioms prime_factor_count_pgf_at_zero

end

end D5.S3.Analytic.ZetaObservation.PrimeFactorCountGeneratingFunction
