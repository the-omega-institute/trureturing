/- GID: D5/S3/Analytic/Boundary/ZetaPrimeProductCommonBoundary
   generality: I
   mirror-B: D5/B/S3/Analytic/Boundary/ZetaPrimeProductCommonBoundary
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The zeta partition, prime product, entropy, and sensitivity share boundary one. -/

import D5.S3.Analytic.PrimeProducts.FiniteMarginalGlobalSupportContrast
import D5.S3.Analytic.Zeta.PrimeMarginalEntropy

/- Library-search audit trail (2026-08-26):
   * Repository search found the canonical `partitionFunction`,
     `activationProbability`, `exponentProduct`, and local prime entropy formula,
     but no theorem packaging their common convergence boundary.
   * `finite_marginals_and_global_support_contrast` supplies the measure-zero
     finite-support half for `0 < s <= 1`; the converse below applies the first
     Borel-Cantelli lemma to the same canonical activation events.
   * Exact pinned-Mathlib hits `Real.summable_nat_rpow` and
     `Nat.Primes.summable_rpow` identify the integer and prime p-series
     thresholds. `Real.log_natCast_le_rpow_div` supplies the logarithm-squared
     comparison needed for the Fisher summands.
   * No pinned theorem states the combined boundary. Loogle and LeanSearch were
     unavailable in this worker image. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped ENNReal BigOperators

noncomputable section

namespace D5.S3.Analytic.Boundary.ZetaPrimeProductCommonBoundary

open Filter MeasureTheory ProbabilityTheory Set
open D5.S3.Analytic.ZetaGibbs
open D5.S3.Analytic.Zeta.ZetaEntropy
open D5.S3.Analytic.Zeta.PrimeMarginalEntropy
open D5.S3.Analytic.PrimeProducts.FiniteMarginalGlobalSupportContrast

private lemma activation_nonneg (s : Real) (p : Nat.Primes) :
    0 <= activationProbability s p :=
  Real.rpow_nonneg (by positivity) _

private lemma activation_lt_one (s : Real) (hs : 0 < s) (p : Nat.Primes) :
    activationProbability s p < 1 := by
  apply Real.rpow_lt_one_of_one_lt_of_neg
  · exact_mod_cast p.property.one_lt
  · linarith

private lemma exponent_success_ne_zero (s : Real) (hs : 0 < s)
    (p : Nat.Primes) : exponentSuccess s hs p ≠ 0 := by
  apply ne_of_gt
  change 0 < 1 - activationProbability s p
  exact sub_pos.mpr (activation_lt_one s hs p)

private lemma exponent_product_activation (s : Real) (hs : 0 < s)
    (p : Nat.Primes) :
    exponentProduct s hs (activationEvent p) =
      ENNReal.ofReal (activationProbability s p) := by
  calc
    exponentProduct s hs (activationEvent p) =
        (exponentProduct s hs).map (fun exponents => exponents p) ({0}ᶜ) := by
      exact (Measure.map_apply (by fun_prop)
        (measurableSet_singleton 0).compl).symm
    _ = exponentMeasure s hs p ({0}ᶜ) := by
      rw [exponentProduct, Measure.infinitePi_map_eval]
    _ = ENNReal.ofReal (activationProbability s p) := by
      have hq_nonneg := activation_nonneg s p
      have hq_le := (activation_lt_one s hs p).le
      rw [prob_compl_eq_one_sub (measurableSet_singleton 0)]
      rw [exponentMeasure, geometricMeasure_singleton
        (exponent_success_ne_zero s hs p)]
      change 1 - ENNReal.ofReal
        ((1 - (1 - activationProbability s p)) ^ 0 *
          (1 - activationProbability s p)) = _
      rw [pow_zero, one_mul, <- ENNReal.ofReal_one,
        <- ENNReal.ofReal_sub 1 (sub_nonneg.mpr hq_le)]
      congr 1
      ring

private lemma partition_finite_iff (s : Real) :
    partitionFunction s ≠ ∞ <-> 1 < s := by
  constructor
  · intro finitePartition
    have nonnegative : forall n : Nat, 0 <= (n : Real) ^ (-s) :=
      fun n => Real.rpow_nonneg n.cast_nonneg _
    have finiteNNReal : Summable
        (fun n : Nat => Real.toNNReal ((n : Real) ^ (-s))) := by
      apply ENNReal.tsum_coe_ne_top_iff_summable.mp
      simpa only [partitionFunction, weight, ENNReal.ofReal] using finitePartition
    have finiteReal : Summable (fun n : Nat => (n : Real) ^ (-s)) := by
      have coerced := NNReal.summable_coe.mpr finiteNNReal
      simpa only [Real.coe_toNNReal _ (nonnegative _)] using coerced
    have exponentBound := Real.summable_nat_rpow.mp finiteReal
    linarith
  · exact partition_function_ne_top s

private lemma activation_summable_iff (s : Real) :
    Summable (fun p : Nat.Primes => activationProbability s p) <-> 1 < s := by
  rw [show (fun p : Nat.Primes => activationProbability s p) =
      fun p : Nat.Primes => (p : Real) ^ (-s) by rfl,
    Nat.Primes.summable_rpow]
  constructor <;> intro bound <;> linarith

private lemma finite_support_full_of_one_lt (s : Real) (hs : 0 < s)
    (hone : 1 < s) :
    exponentProduct s hs
      {exponents | (Function.support exponents).Finite} = 1 := by
  have activationSummable :
      Summable (fun p : Nat.Primes => activationProbability s p) :=
    (activation_summable_iff s).2 hone
  let masses : Nat.Primes -> NNReal := fun p =>
    Real.toNNReal (activationProbability s p)
  have massesSummable : Summable masses := activationSummable.toNNReal
  have finiteMassTsum : (∑' p, (masses p : ENNReal)) ≠ ∞ :=
    ENNReal.tsum_coe_ne_top_iff_summable.mpr massesSummable
  have finiteEventTsum :
      (∑' p, exponentProduct s hs (activationEvent p)) ≠ ∞ := by
    rw [show (∑' p, exponentProduct s hs (activationEvent p)) =
        ∑' p, (masses p : ENNReal) by
      apply tsum_congr
      intro p
      rw [exponent_product_activation]
      rfl]
    exact finiteMassTsum
  have finiteActivations :
      ∀ᵐ exponents ∂exponentProduct s hs,
        {p | exponents ∈ activationEvent p}.Finite :=
    ae_finite_setOf_mem finiteEventTsum
  have finiteSupport :
      ∀ᵐ exponents ∂exponentProduct s hs,
        (Function.support exponents).Finite := by
    filter_upwards [finiteActivations] with exponents finiteSet
    change {p | exponents p ≠ 0}.Finite
    simpa only [activationEvent, Set.mem_preimage, Set.mem_compl_iff,
      Set.mem_singleton_iff] using finiteSet
  apply le_antisymm
  · calc
      exponentProduct s hs
          {exponents | (Function.support exponents).Finite} <=
          exponentProduct s hs Set.univ := measure_mono (subset_univ _)
      _ = 1 := measure_univ
  calc
    1 = exponentProduct s hs Set.univ := (measure_univ).symm
    _ <= exponentProduct s hs
        {exponents | (Function.support exponents).Finite} := by
      apply measure_mono_ae
      filter_upwards [finiteSupport] with exponents supportFinite
      exact fun _ => supportFinite

private lemma finite_support_full_iff (s : Real) (hs : 0 < s) :
    exponentProduct s hs
      {exponents | (Function.support exponents).Finite} = 1 <-> 1 < s := by
  constructor
  · intro fullSupport
    by_contra notAbove
    have supportZero :=
      (finite_marginals_and_global_support_contrast s hs).2.2.2
        (le_of_not_gt notAbove)
    rw [fullSupport] at supportZero
    exact one_ne_zero supportZero
  · exact finite_support_full_of_one_lt s hs

private lemma entropy_summable_iff (s : Real) (hs : 0 < s) :
    Summable (fun p : Nat.Primes =>
      -Real.log (1 - (p.1 : Real) ^ (-s)) +
        s * Real.log p.1 *
          ((p.1 : Real) ^ (-s) / (1 - (p.1 : Real) ^ (-s)))) <->
      1 < s := by
  constructor
  · intro entropySummable
    have activationSummable :
        Summable (fun p : Nat.Primes => activationProbability s p) := by
      apply Summable.of_nonneg_of_le (activation_nonneg s)
      · intro p
        let q : Real := activationProbability s p
        have hq0 : 0 < q := Real.rpow_pos_of_pos (by
          exact_mod_cast p.property.pos) _
        have hq1 : q < 1 := activation_lt_one s hs p
        have hneglog : q <= -Real.log (1 - q) := by
          have hlog := Real.log_le_sub_one_of_pos (sub_pos.mpr hq1)
          linarith
        have hsecond :
            0 <= s * Real.log p.1 * (q / (1 - q)) := by
          exact mul_nonneg
            (mul_nonneg hs.le (Real.log_pos (by
              exact_mod_cast p.property.one_lt)).le)
            (div_nonneg hq0.le (sub_pos.mpr hq1).le)
        dsimp [q, activationProbability] at hneglog hsecond ⊢
        exact hneglog.trans (le_add_of_nonneg_right hsecond)
      · exact entropySummable
    exact (activation_summable_iff s).1 activationSummable
  · intro hone
    have localEntropySummable := summable_primeExponent_entropy s hone
    apply localEntropySummable.congr
    intro p
    exact primeExponent_entropy_eq s hone p

private lemma summable_log_sq_weight (s : Real) (hone : 1 < s) :
    Summable (fun n : Nat => Real.log n ^ 2 * (n : Real) ^ (-s)) := by
  let epsilon := (s - 1) / 4
  have hepsilon : 0 < epsilon := by
    dsimp [epsilon]
    linarith
  have hexponent : 2 * epsilon - s < -1 := by
    dsimp [epsilon]
    linarith
  have majorSummable :
      Summable (fun n : Nat =>
        epsilon⁻¹ ^ 2 * (n : Real) ^ (2 * epsilon - s)) :=
    (Real.summable_nat_rpow.mpr hexponent).mul_left (epsilon⁻¹ ^ 2)
  apply Summable.of_nonneg_of_le
    (fun n => mul_nonneg (sq_nonneg _) (Real.rpow_nonneg n.cast_nonneg _))
    (fun n => ?_) majorSummable
  rcases n.eq_zero_or_pos with rfl | hn
  · simp [Real.zero_rpow (by linarith : -s ≠ 0),
      Real.zero_rpow (by linarith : 2 * epsilon - s ≠ 0)]
  · have hnR : 0 < (n : Real) := by exact_mod_cast hn
    have hlog : Real.log n <= (n : Real) ^ epsilon / epsilon :=
      Real.log_natCast_le_rpow_div n hepsilon
    have hsquare : Real.log n ^ 2 <= ((n : Real) ^ epsilon / epsilon) ^ 2 :=
      (sq_le_sq₀ (Real.log_natCast_nonneg n)
        (div_nonneg (Real.rpow_nonneg n.cast_nonneg _) hepsilon.le)).2 hlog
    calc
      Real.log n ^ 2 * (n : Real) ^ (-s) <=
          ((n : Real) ^ epsilon / epsilon) ^ 2 * (n : Real) ^ (-s) :=
        mul_le_mul_of_nonneg_right hsquare
          (Real.rpow_nonneg n.cast_nonneg _)
      _ = epsilon⁻¹ ^ 2 * (n : Real) ^ (2 * epsilon - s) := by
        rw [div_pow]
        calc
          ((n : Real) ^ epsilon) ^ 2 / epsilon ^ 2 * (n : Real) ^ (-s) =
              epsilon⁻¹ ^ 2 *
                (((n : Real) ^ epsilon) ^ 2 * (n : Real) ^ (-s)) := by ring_nf
          _ = epsilon⁻¹ ^ 2 * (n : Real) ^ (2 * epsilon - s) := by
            congr 1
            rw [<- Real.rpow_natCast, <- Real.rpow_mul hnR.le,
              <- Real.rpow_add hnR]
            congr 1
            ring

private lemma fisher_summable_iff (s : Real) (hs : 0 < s) :
    Summable (fun p : Nat.Primes =>
      Real.log p.1 ^ 2 *
        ((p.1 : Real) ^ (-s) / (1 - (p.1 : Real) ^ (-s)) ^ 2)) <->
      1 < s := by
  constructor
  · intro fisherSummable
    have activationSummable :
        Summable (fun p : Nat.Primes => activationProbability s p) := by
      let scale : Real := (Real.log 2 ^ 2)⁻¹
      have scaledFisher := fisherSummable.mul_left scale
      apply Summable.of_nonneg_of_le (activation_nonneg s)
      · intro p
        let q : Real := activationProbability s p
        have hq0 : 0 < q := Real.rpow_pos_of_pos (by
          exact_mod_cast p.property.pos) _
        have hq1 : q < 1 := activation_lt_one s hs p
        have hpTwo : (2 : Real) <= p.1 := by exact_mod_cast p.property.two_le
        have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
        have hlogP : 0 < Real.log p.1 :=
          Real.log_pos (by exact_mod_cast p.property.one_lt)
        have hlogs : Real.log 2 <= Real.log p.1 :=
          Real.log_le_log (by norm_num) hpTwo
        have hlogSquares : Real.log 2 ^ 2 <= Real.log p.1 ^ 2 :=
          (sq_le_sq₀ hlogTwo.le hlogP.le).2 hlogs
        have hdenPos : 0 < (1 - q) ^ 2 := sq_pos_of_pos (sub_pos.mpr hq1)
        have hqDiv : q <= q / (1 - q) ^ 2 := by
          rw [le_div_iff₀ hdenPos]
          have hqOne : q <= 1 := hq1.le
          nlinarith [mul_nonpos_of_nonneg_of_nonpos hq0.le (sub_nonpos.mpr hqOne)]
        have hscaledBound :
            Real.log 2 ^ 2 * q <=
              Real.log p.1 ^ 2 * (q / (1 - q) ^ 2) := by
          calc
            Real.log 2 ^ 2 * q <= Real.log p.1 ^ 2 * q :=
              mul_le_mul_of_nonneg_right hlogSquares hq0.le
            _ <= Real.log p.1 ^ 2 * (q / (1 - q) ^ 2) :=
              mul_le_mul_of_nonneg_left hqDiv (sq_nonneg _)
        dsimp [scale, q, activationProbability] at hscaledBound ⊢
        calc
          (p.1 : Real) ^ (-s) =
              (Real.log 2 ^ 2)⁻¹ *
                (Real.log 2 ^ 2 * (p.1 : Real) ^ (-s)) := by
            field_simp [ne_of_gt (sq_pos_of_pos hlogTwo)]
          _ <= (Real.log 2 ^ 2)⁻¹ *
              (Real.log p.1 ^ 2 *
                ((p.1 : Real) ^ (-s) /
                  (1 - (p.1 : Real) ^ (-s)) ^ 2)) :=
            mul_le_mul_of_nonneg_left hscaledBound
              (inv_nonneg.mpr (sq_nonneg _))
      · exact scaledFisher
    exact (activation_summable_iff s).1 activationSummable
  · intro hone
    have logSquareSummable : Summable (fun p : Nat.Primes =>
        Real.log p.1 ^ 2 * (p.1 : Real) ^ (-s)) := by
      have primeCoeInjective : Function.Injective
          (fun p : Nat.Primes => (p : Nat)) := Subtype.coe_injective
      change Summable
        ((fun n : Nat => Real.log (n : Real) ^ 2 * (n : Real) ^ (-s)) ∘
          fun p : Nat.Primes => (p : Nat))
      exact (summable_log_sq_weight s hone).comp_injective primeCoeInjective
    have majorSummable := logSquareSummable.mul_left 4
    apply Summable.of_nonneg_of_le
      (fun p => mul_nonneg (sq_nonneg _)
        (div_nonneg (Real.rpow_nonneg (by positivity) _)
          (sq_nonneg _)))
      (fun p => ?_) majorSummable
    let q : Real := (p.1 : Real) ^ (-s)
    have hpR : 1 < (p.1 : Real) := by exact_mod_cast p.property.one_lt
    have hq0 : 0 < q := Real.rpow_pos_of_pos (by positivity) _
    have hq1 : q < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg hpR (by linarith)
    have hqHalf : q <= (2 : Real)⁻¹ := by
      calc
        q <= (p.1 : Real) ^ (-1 : Real) :=
          Real.rpow_le_rpow_of_exponent_le hpR.le (by linarith)
        _ = (p.1 : Real)⁻¹ := Real.rpow_neg_one _
        _ <= (2 : Real)⁻¹ :=
          inv_anti₀ (by norm_num) (by exact_mod_cast p.property.two_le)
    have hfraction : q / (1 - q) ^ 2 <= 4 * q := by
      have hdenHalf : (1 : Real) / 2 <= 1 - q := by
        norm_num at hqHalf ⊢
        linarith
      have hdenSquare : (1 : Real) / 4 <= (1 - q) ^ 2 := by
        nlinarith [sq_nonneg ((1 - q) - (1 : Real) / 2)]
      rw [div_le_iff₀ (sq_pos_of_pos (sub_pos.mpr hq1))]
      nlinarith [mul_le_mul_of_nonneg_left hdenSquare hq0.le]
    dsimp [q] at hfraction ⊢
    calc
      Real.log p.1 ^ 2 *
          ((p.1 : Real) ^ (-s) / (1 - (p.1 : Real) ^ (-s)) ^ 2) <=
          Real.log p.1 ^ 2 * (4 * (p.1 : Real) ^ (-s)) :=
        mul_le_mul_of_nonneg_left hfraction (sq_nonneg _)
      _ = 4 * (Real.log p.1 ^ 2 * (p.1 : Real) ^ (-s)) := by ring

/-- For every positive real parameter, five concrete source properties cross
their boundary at the same point `s = 1`: finiteness of the zeta partition,
summability of prime activations, almost-sure gluing to finite-support integer
profiles, summability of prime entropy, and summability of Fisher sensitivity. -/
theorem zeta_prime_product_common_boundary (s : Real) (hs : 0 < s) :
    (partitionFunction s ≠ ∞ <-> 1 < s) /\
    (Summable (fun p : Nat.Primes => activationProbability s p) <-> 1 < s) /\
    (exponentProduct s hs
        {exponents | (Function.support exponents).Finite} = 1 <-> 1 < s) /\
    (Summable (fun p : Nat.Primes =>
        -Real.log (1 - (p.1 : Real) ^ (-s)) +
          s * Real.log p.1 *
            ((p.1 : Real) ^ (-s) / (1 - (p.1 : Real) ^ (-s)))) <->
      1 < s) /\
    (Summable (fun p : Nat.Primes =>
        Real.log p.1 ^ 2 *
          ((p.1 : Real) ^ (-s) / (1 - (p.1 : Real) ^ (-s)) ^ 2)) <->
      1 < s) := by
  exact ⟨partition_finite_iff s, activation_summable_iff s,
    finite_support_full_iff s hs, entropy_summable_iff s hs,
    fisher_summable_iff s hs⟩

#print axioms zeta_prime_product_common_boundary

end D5.S3.Analytic.Boundary.ZetaPrimeProductCommonBoundary
