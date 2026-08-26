/- GID: D5/S3/Analytic/PrimeProducts/PrimePrecisionEntropyContraction
   generality: I
   mirror-B: D5/B/S3/Analytic/PrimeProducts/PrimePrecisionEntropyContraction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Each added prime-exponent digit contracts the unresolved channel entropy exactly. -/

import D5.S3.Analytic.PrimeProducts.GeometricResidualMemorylessness
import D5.S3.Analytic.Zeta.PrimeMarginalEntropy

/- Search audit (2026-08-26):
   * D5 contains the canonical prime-exponent PMF, its countable entropy, and
     geometric residual memorylessness, but no exact precision-step entropy
     contraction theorem.
   * Pinned Mathlib contains the geometric measure, PMF filtering and mapping,
     and the required measure identities, but no packaged conditional-tail
     entropy contraction result.
   * Body-shape searches for a tail-filtered and translated prime PMF found no
     D5 definition. This module uses `PMF.filter` and `PMF.map` directly and
     introduces no `def` or `abbrev`. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped ENNReal ProbabilityTheory

noncomputable section

namespace D5.S3.Analytic.PrimeProducts.PrimePrecisionEntropyContraction

open D5.S3.Analytic.PrimeProducts.GeometricResidualMemorylessness
open D5.S3.Analytic.Zeta.PrimeMarginalEntropy
open D5.S3.Analytic.Zeta.ZetaEntropy
open MeasureTheory ProbabilityTheory Set

private lemma prime_ratio_pos (s : Real) (p : Nat.Primes) :
    0 < (p.1 : Real) ^ (-s) :=
  Real.rpow_pos_of_pos (by exact_mod_cast p.2.pos) _

private lemma prime_ratio_lt_one (s : Real) (hs : 1 < s) (p : Nat.Primes) :
    (p.1 : Real) ^ (-s) < 1 :=
  Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast p.2.one_lt) (by linarith)

private lemma prime_tail_witness (s : Real) (hs : 1 < s) (p : Nat.Primes)
    (precision : Nat) :
    ∃ value ∈ Set.Ici precision,
      value ∈ (primeExponentPMF s hs p).support := by
  refine ⟨precision, Set.mem_Ici.mpr le_rfl, ?_⟩
  rw [PMF.mem_support_iff]
  intro hzero
  have hpositive : 0 < pmfReal (primeExponentPMF s hs p) precision := by
    rw [primeExponentPMF_apply]
    exact mul_pos (sub_pos.mpr (prime_ratio_lt_one s hs p))
      (Real.rpow_pos_of_pos (by exact_mod_cast p.2.pos) _)
  rw [pmfReal, hzero, ENNReal.toReal_zero] at hpositive
  exact (lt_irrefl 0) hpositive

private lemma geometric_tail_probability (success : unitInterval)
    (success_ne_zero : success ≠ 0) (precision : Nat) :
    geometricMeasure success (Set.Ici precision) =
      ENNReal.ofReal ((1 - success : Real) ^ precision) := by
  rw [← compl_Iio, prob_compl_eq_one_sub (measurableSet_Iio : MeasurableSet (Iio precision))]
  rw [geometricMeasure_eq success_ne_zero,
    Measure.sum_apply _ (MeasurableSet.of_discrete (s := Iio precision))]
  simp only [Measure.smul_apply, smul_eq_mul]
  rw [tsum_eq_sum (s := Finset.range precision)]
  · simp_rw [Measure.dirac_apply' _ MeasurableSet.of_discrete]
    have indicator_sum :
        (∑ n ∈ Finset.range precision,
            ENNReal.ofReal ((1 - success : Real) ^ n * success) *
              (Iio precision).indicator 1 n) =
          ∑ n ∈ Finset.range precision,
            ENNReal.ofReal ((1 - success : Real) ^ n * success) := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [Set.indicator_of_mem]
      · exact mul_one _
      · exact Finset.mem_range.mp hn
    rw [indicator_sum, ← ENNReal.ofReal_sum_of_nonneg]
    · have finite_mass_nonneg :
          0 ≤ ∑ n ∈ Finset.range precision,
            (1 - success : Real) ^ n * success :=
        Finset.sum_nonneg fun n _ => geometricMeasure_nonneg success n
      rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub 1 finite_mass_nonneg]
      congr 1
      have geometric_sum := geom_sum_mul_neg (1 - success : Real) precision
      rw [← Finset.sum_mul]
      linarith
    · intro n _
      exact geometricMeasure_nonneg success n
  · intro n hn
    rw [Finset.mem_range, not_lt] at hn
    simp [Measure.dirac_apply' _ MeasurableSet.of_discrete, hn]

private lemma prime_channel_measure_eq_geometric
    (s : Real) (hs : 1 < s) (p : Nat.Primes) :
    (primeExponentPMF s hs p).toMeasure =
      geometricMeasure
        (⟨1 - (p.1 : Real) ^ (-s),
          ⟨by linarith [prime_ratio_lt_one s hs p],
            by linarith [prime_ratio_pos s p]⟩⟩ : unitInterval) := by
  apply Measure.ext_of_singleton
  intro value
  rw [PMF.toMeasure_apply_singleton _ _ MeasurableSet.of_discrete]
  rw [geometricMeasure_singleton]
  · rw [← ENNReal.toReal_eq_toReal_iff'
      ((primeExponentPMF s hs p).apply_ne_top value) ENNReal.ofReal_ne_top]
    change pmfReal (primeExponentPMF s hs p) value =
      (ENNReal.ofReal
        ((1 - (1 - (p.1 : Real) ^ (-s))) ^ value *
          (1 - (p.1 : Real) ^ (-s)))).toReal
    rw [primeExponentPMF_apply, ENNReal.toReal_ofReal]
    · have hpow :
          (p.1 : Real) ^ (-(value : Real) * s) =
            ((p.1 : Real) ^ (-s)) ^ value := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
        congr 1
        ring
      rw [hpow]
      ring
    · exact mul_nonneg (pow_nonneg (by linarith [prime_ratio_pos s p]) value)
        (by linarith [prime_ratio_lt_one s hs p])
  · intro hzero
    have hvalue := congrArg Subtype.val hzero
    dsimp only at hvalue
    exact (sub_pos.mpr (prime_ratio_lt_one s hs p)).ne' (by simpa using hvalue)

private lemma filtered_toMeasure_eq_cond (channel : PMF Nat) (tail : Set Nat)
    (witness : ∃ value ∈ tail, value ∈ channel.support) :
    (channel.filter tail witness).toMeasure = channel.toMeasure[|tail] := by
  apply Measure.ext_of_singleton
  intro value
  rw [PMF.toMeasure_apply_singleton _ _ MeasurableSet.of_discrete]
  rw [PMF.filter_apply, cond_apply' MeasurableSet.of_discrete]
  rw [PMF.toMeasure_apply_eq_tsum]
  by_cases hvalue : value ∈ tail
  · rw [Set.indicator_of_mem hvalue]
    have hintersection : tail ∩ ({value} : Set Nat) = {value} := by
      ext candidate
      simp only [Set.mem_inter_iff, Set.mem_singleton_iff]
      constructor
      · exact fun h => h.2
      · intro h
        subst candidate
        exact ⟨hvalue, rfl⟩
    rw [hintersection,
      PMF.toMeasure_apply_singleton _ _ MeasurableSet.of_discrete]
    ac_rfl
  · rw [Set.indicator_of_notMem hvalue]
    have hintersection : tail ∩ ({value} : Set Nat) = ∅ :=
      Set.inter_singleton_eq_empty.mpr hvalue
    rw [hintersection, measure_empty]
    simp

private lemma prime_residual_law_eq
    (s : Real) (hs : 1 < s) (p : Nat.Primes) (precision : Nat) :
    ((primeExponentPMF s hs p).filter (Set.Ici precision)
        (prime_tail_witness s hs p precision)).map
      (fun value : Nat => value - precision) =
        primeExponentPMF s hs p := by
  apply PMF.toMeasure_injective
  rw [← PMF.toMeasure_map (fun value : Nat => value - precision) _
    (measurable_of_countable _)]
  rw [filtered_toMeasure_eq_cond]
  rw [prime_channel_measure_eq_geometric]
  exact geometric_residual_memoryless
    (⟨1 - (p.1 : Real) ^ (-s),
      ⟨by linarith [prime_ratio_lt_one s hs p],
        by linarith [prime_ratio_pos s p]⟩⟩ : unitInterval)
    (by
      intro hzero
      have hvalue := congrArg Subtype.val hzero
      dsimp only at hvalue
      exact (sub_pos.mpr (prime_ratio_lt_one s hs p)).ne' (by simpa using hvalue))
    (by
      intro hone
      have hvalue := congrArg Subtype.val hone
      dsimp only at hvalue
      norm_num at hvalue
      have hqzero : (p.1 : Real) ^ (-s) = 0 := by linarith
      exact (prime_ratio_pos s p).ne' hqzero)
    precision

private lemma prime_tail_probability_toReal
    (s : Real) (hs : 1 < s) (p : Nat.Primes) (precision : Nat) :
    ((primeExponentPMF s hs p).toMeasure (Set.Ici precision)).toReal =
      ((p.1 : Real) ^ (-s)) ^ precision := by
  rw [prime_channel_measure_eq_geometric]
  rw [geometric_tail_probability]
  · change (ENNReal.ofReal
      ((1 - (1 - (p.1 : Real) ^ (-s))) ^ precision)).toReal = _
    rw [show 1 - (1 - (p.1 : Real) ^ (-s)) = (p.1 : Real) ^ (-s) by ring]
    rw [ENNReal.toReal_ofReal (pow_nonneg (prime_ratio_pos s p).le precision)]
  · intro hzero
    have hvalue := congrArg Subtype.val hzero
    dsimp only at hvalue
    exact (sub_pos.mpr (prime_ratio_lt_one s hs p)).ne' (by simpa using hvalue)

private lemma prime_residual_entropy_formula
    (s : Real) (hs : 1 < s) (p : Nat.Primes) (precision : Nat) :
    ((primeExponentPMF s hs p).toMeasure (Set.Ici precision)).toReal *
        countableEntropy
          (((primeExponentPMF s hs p).filter (Set.Ici precision)
              (prime_tail_witness s hs p precision)).map
            (fun value : Nat => value - precision)) =
      ((p.1 : Real) ^ (-s)) ^ precision *
        countableEntropy (primeExponentPMF s hs p) := by
  rw [prime_tail_probability_toReal, prime_residual_law_eq]

/-- For the canonical prime-exponent channel, the unresolved entropy before
and after one added precision layer has the exact geometric form, and the
successor value is the predecessor value multiplied by `p ^ (-s)`. -/
theorem prime_precision_entropy_contraction
    (s : Real) (hs : 1 < s) (p : Nat.Primes) (k : Nat) :
    let channel := primeExponentPMF s hs p
    let residualLaw := fun precision =>
      (channel.filter (Set.Ici precision)
          (prime_tail_witness s hs p precision)).map
        (fun value : Nat => value - precision)
    let residualEntropy := fun precision =>
      (channel.toMeasure (Set.Ici precision)).toReal *
        countableEntropy (residualLaw precision)
    residualEntropy k =
        ((p.1 : Real) ^ (-s)) ^ k * countableEntropy channel ∧
      residualEntropy (k + 1) =
        ((p.1 : Real) ^ (-s)) ^ (k + 1) * countableEntropy channel ∧
      residualEntropy (k + 1) =
        (p.1 : Real) ^ (-s) * residualEntropy k := by
  dsimp only
  refine ⟨prime_residual_entropy_formula s hs p k,
    prime_residual_entropy_formula s hs p (k + 1), ?_⟩
  rw [prime_residual_entropy_formula s hs p (k + 1),
    prime_residual_entropy_formula s hs p k, pow_succ]
  ring

#print axioms prime_precision_entropy_contraction

end D5.S3.Analytic.PrimeProducts.PrimePrecisionEntropyContraction
