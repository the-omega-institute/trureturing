/- GID: D5/S3/Analytic/ZetaObservation/MinimalSufficientRelation
   generality: I
   mirror-B: D5/B/S3/Analytic/ZetaObservation/MinimalSufficientRelation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Equal-size positive zeta samples have constant ratio exactly at equal products. -/
/- Library-search audit trail (2026-08-25):
   * Repository phrase searches for minimal sufficiency and likelihood ratios found no equivalent.
   * Shape searches for finite zeta likelihood products found only unrelated sample products.
   * The specified Zeta, ZetaObservation, and posterior modules were inspected declaration by
     declaration; `zetaDist`, `pmfReal`, and `zeta_real_apply` are reused as the family SSOT.
   * Pinned Mathlib Probability and MeasureTheory searches found no sufficient-statistic API.
   * Mathlib `llr` is a Radon--Nikodym log ratio, not parameter independence of sample likelihoods.
   * `Real.list_prod_map_rpow`, `Real.div_rpow`, and `ENNReal.tsum_lt_tsum` were exact hits.
   * The Lean search script and Loogle returned no theorem equivalent to the requested criterion. -/

import D5.S3.Analytic.Zeta.ZetaEntropy

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Analytic.ZetaObservation.MinimalSufficientRelation

open scoped BigOperators ENNReal
open D5.S3.Analytic.ZetaGibbs
open D5.S3.Analytic.Zeta.ZetaEntropy

noncomputable section

/-!
The source family is exactly the repository zeta Gibbs PMF on natural numbers. Its intended sample
space is the positive integers; natural-number lists are retained here so the failure at zero can
be stated as a concrete theorem. The equal-length hypothesis is explicit because otherwise the
two powers of the partition function do not cancel.

`zetaRatioParameterIndependent n m` means equality of the likelihood ratio at every pair of
admissible inverse temperatures. The main theorem is the likelihood-ratio characterization of the
minimal sufficient relation. The logarithmic theorem then identifies the same relation with total
logarithmic energy without introducing a second probability family or partition function.

Degeneration and hypothesis audit: the empty and singleton samples are covered; one contributes
zero logarithmic energy; permutations give the same statistic; separate zero counterexamples show
that both nonzeroness assumptions are used; unequal lengths retain normalization; and the ratio for
samples `[2]` and `[1]` differs at inverse temperatures two and three.
-/

/-- The admissible inverse-temperature domain of the normalized zeta Gibbs family. -/
abbrev ZetaParameter := {s : Real // 1 < s}

/-- The multiplicative statistic of a finite natural-number sample. -/
def sampleProduct (sample : List Nat) : Nat := sample.prod

/-- The total logarithmic energy of a finite natural-number sample. -/
def totalLogEnergy (sample : List Nat) : Real :=
  (sample.map fun n => Real.log n).sum

/-- The iid joint likelihood under the repository zeta Gibbs PMF. -/
def zetaSampleLikelihood (parameter : ZetaParameter) (sample : List Nat) : Real :=
  (sample.map (pmfReal (zetaDist parameter.1 parameter.2))).prod

/-- The likelihood ratio of two samples, allowing unequal lengths for the necessity audit. -/
def zetaLikelihoodRatio
    (parameter : ZetaParameter) (numerator denominator : List Nat) : Real :=
  zetaSampleLikelihood parameter numerator / zetaSampleLikelihood parameter denominator

/-- The sample likelihood ratio is constant throughout the admissible zeta parameter domain. -/
def zetaRatioParameterIndependent (numerator denominator : List Nat) : Prop :=
  ∀ first second : ZetaParameter,
    zetaLikelihoodRatio first numerator denominator =
      zetaLikelihoodRatio second numerator denominator

/-- A joint zeta likelihood is the product weight times one normalization per sample entry. -/
theorem zeta_sample_likelihood_eq (parameter : ZetaParameter) (sample : List Nat) :
    zetaSampleLikelihood parameter sample =
      (sampleProduct sample : Real) ^ (-parameter.1) *
        (partitionFunction parameter.1).toReal⁻¹ ^ sample.length := by
  induction sample with
  | nil => simp [zetaSampleLikelihood, sampleProduct]
  | cons head tail inductionHypothesis =>
      change
        pmfReal (zetaDist parameter.1 parameter.2) head *
            zetaSampleLikelihood parameter tail = _
      rw [zeta_real_apply parameter.1 parameter.2 head, inductionHypothesis]
      simp only [sampleProduct, List.prod_cons, Nat.cast_mul, List.length_cons, pow_succ]
      rw [Real.mul_rpow (by positivity) (by positivity)]
      ring

#print axioms zeta_sample_likelihood_eq

/-- Equal sample sizes cancel the partition function and leave a power of the product ratio. -/
theorem zeta_likelihood_ratio_eq_product_ratio_rpow
    (parameter : ZetaParameter) (numerator denominator : List Nat)
    (equalSize : numerator.length = denominator.length) :
    zetaLikelihoodRatio parameter numerator denominator =
      ((sampleProduct denominator : Real) / sampleProduct numerator) ^ parameter.1 := by
  have normalization_ne_zero :
      (partitionFunction parameter.1).toReal⁻¹ ^ denominator.length ≠ 0 :=
    pow_ne_zero _ (inv_ne_zero (partition_toReal_pos parameter.1 parameter.2).ne')
  rw [zetaLikelihoodRatio, zeta_sample_likelihood_eq, zeta_sample_likelihood_eq, equalSize,
    mul_div_mul_right _ _ normalization_ne_zero]
  rw [Real.rpow_neg (by positivity) parameter.1,
    Real.rpow_neg (by positivity) parameter.1, inv_div_inv]
  exact (Real.div_rpow (by positivity) (by positivity) parameter.1).symm

#print axioms zeta_likelihood_ratio_eq_product_ratio_rpow

/-- For equal-size positive samples, parameter independence is exactly equality of products. -/
theorem sample_product_is_minimal_sufficient_relation
    (numerator denominator : List Nat)
    (numeratorNonzero : ∀ n ∈ numerator, n ≠ 0)
    (denominatorNonzero : ∀ n ∈ denominator, n ≠ 0)
    (equalSize : numerator.length = denominator.length) :
    zetaRatioParameterIndependent numerator denominator ↔
      sampleProduct numerator = sampleProduct denominator := by
  have numeratorProductNonzero : sampleProduct numerator ≠ 0 := by
    apply List.prod_ne_zero
    intro zeroMem
    exact (numeratorNonzero 0 zeroMem) rfl
  have denominatorProductNonzero : sampleProduct denominator ≠ 0 := by
    apply List.prod_ne_zero
    intro zeroMem
    exact (denominatorNonzero 0 zeroMem) rfl
  have numeratorProductPos : 0 < (sampleProduct numerator : Real) := by
    exact_mod_cast Nat.pos_of_ne_zero numeratorProductNonzero
  have denominatorProductPos : 0 < (sampleProduct denominator : Real) := by
    exact_mod_cast Nat.pos_of_ne_zero denominatorProductNonzero
  constructor
  · intro independent
    have atTwoThree := independent
      (⟨2, by norm_num⟩ : ZetaParameter) (⟨3, by norm_num⟩ : ZetaParameter)
    rw [zeta_likelihood_ratio_eq_product_ratio_rpow _ _ _ equalSize,
      zeta_likelihood_ratio_eq_product_ratio_rpow _ _ _ equalSize] at atTwoThree
    change
      ((sampleProduct denominator : Real) / sampleProduct numerator) ^ (2 : Real) =
        ((sampleProduct denominator : Real) / sampleProduct numerator) ^ (3 : Real)
      at atTwoThree
    simp only [Real.rpow_ofNat] at atTwoThree
    have ratioPos :
        0 < (sampleProduct denominator : Real) / sampleProduct numerator :=
      div_pos denominatorProductPos numeratorProductPos
    have ratioSquaredPos :
        0 < ((sampleProduct denominator : Real) / sampleProduct numerator) ^ 2 :=
      pow_pos ratioPos _
    have ratioEqOne :
        (sampleProduct denominator : Real) / sampleProduct numerator = 1 := by
      nlinarith
    have castProductsEqual :
        (sampleProduct denominator : Real) = sampleProduct numerator :=
      (div_eq_one_iff_eq numeratorProductPos.ne').mp ratioEqOne
    exact_mod_cast castProductsEqual.symm
  · intro productsEqual first second
    rw [zeta_likelihood_ratio_eq_product_ratio_rpow _ _ _ equalSize,
      zeta_likelihood_ratio_eq_product_ratio_rpow _ _ _ equalSize, productsEqual]
    simp [denominatorProductPos.ne']

#print axioms sample_product_is_minimal_sufficient_relation

/-- For a nonzero sample, total log energy is the logarithm of its sample product. -/
theorem total_log_energy_eq_log_sample_product (sample : List Nat)
    (sampleNonzero : ∀ n ∈ sample, n ≠ 0) :
    totalLogEnergy sample = Real.log (sampleProduct sample) := by
  induction sample with
  | nil => simp [totalLogEnergy, sampleProduct]
  | cons head tail inductionHypothesis =>
      have headNonzero : head ≠ 0 := sampleNonzero head (by simp)
      have tailNonzero : ∀ n ∈ tail, n ≠ 0 := by
        intro n hn
        exact sampleNonzero n (by simp [hn])
      have tailProductNonzero : sampleProduct tail ≠ 0 := by
        apply List.prod_ne_zero
        intro zeroMem
        exact (tailNonzero 0 zeroMem) rfl
      calc
        totalLogEnergy (head :: tail) = Real.log head + totalLogEnergy tail := rfl
        _ = Real.log head + Real.log (sampleProduct tail) := by
          rw [inductionHypothesis tailNonzero]
        _ = Real.log ((head : Real) * sampleProduct tail) :=
          (Real.log_mul (Nat.cast_ne_zero.mpr headNonzero)
            (Nat.cast_ne_zero.mpr tailProductNonzero)).symm
        _ = Real.log (sampleProduct (head :: tail)) := by
          simp [sampleProduct]

#print axioms total_log_energy_eq_log_sample_product

/-- On nonzero samples, equality of products is equivalent to equality of total log energies. -/
theorem sample_product_eq_iff_total_log_energy_eq
    (first second : List Nat)
    (firstNonzero : ∀ n ∈ first, n ≠ 0)
    (secondNonzero : ∀ n ∈ second, n ≠ 0) :
    sampleProduct first = sampleProduct second ↔
      totalLogEnergy first = totalLogEnergy second := by
  have firstProductNonzero : sampleProduct first ≠ 0 := by
    apply List.prod_ne_zero
    intro zeroMem
    exact (firstNonzero 0 zeroMem) rfl
  have secondProductNonzero : sampleProduct second ≠ 0 := by
    apply List.prod_ne_zero
    intro zeroMem
    exact (secondNonzero 0 zeroMem) rfl
  have firstProductPos : 0 < (sampleProduct first : Real) := by
    exact_mod_cast Nat.pos_of_ne_zero firstProductNonzero
  have secondProductPos : 0 < (sampleProduct second : Real) := by
    exact_mod_cast Nat.pos_of_ne_zero secondProductNonzero
  rw [total_log_energy_eq_log_sample_product first firstNonzero,
    total_log_energy_eq_log_sample_product second secondNonzero]
  constructor
  · exact fun productsEqual => congrArg Real.log (by exact_mod_cast productsEqual)
  · intro logsEqual
    have castProductsEqual : (sampleProduct first : Real) = sampleProduct second :=
      Real.strictMonoOn_log.injOn firstProductPos secondProductPos logsEqual
    exact_mod_cast castProductsEqual

#print axioms sample_product_eq_iff_total_log_energy_eq

/-- Empty samples have product one, energy zero, and a parameter-independent ratio. -/
theorem empty_samples_parameter_independent :
    sampleProduct [] = 1 ∧ totalLogEnergy [] = 0 ∧ zetaRatioParameterIndependent [] [] := by
  refine ⟨rfl, rfl, ?_⟩
  intro first second
  simp [zetaLikelihoodRatio, zetaSampleLikelihood]

#print axioms empty_samples_parameter_independent

/-- For singleton positive samples, parameter independence reduces to equality of entries. -/
theorem singleton_parameter_independent_iff (n m : Nat) (hn : n ≠ 0) (hm : m ≠ 0) :
    zetaRatioParameterIndependent [n] [m] ↔ n = m := by
  simpa [sampleProduct] using
    sample_product_is_minimal_sufficient_relation [n] [m]
      (by simp [hn]) (by simp [hm]) (by simp)

#print axioms singleton_parameter_independent_iff

/-- Adjoining one contributes neither product weight nor logarithmic energy. -/
theorem one_entry_is_neutral (sample : List Nat) :
    sampleProduct (1 :: sample) = sampleProduct sample ∧
      totalLogEnergy (1 :: sample) = totalLogEnergy sample := by
  simp [sampleProduct, totalLogEnergy]

#print axioms one_entry_is_neutral

/-- Samples with the same multiset have a parameter-independent likelihood ratio. -/
theorem perm_samples_parameter_independent
    (numerator denominator : List Nat) (permutation : numerator.Perm denominator)
    (numeratorNonzero : ∀ n ∈ numerator, n ≠ 0) :
    zetaRatioParameterIndependent numerator denominator := by
  have denominatorNonzero : ∀ n ∈ denominator, n ≠ 0 := by
    intro n hn
    exact numeratorNonzero n (permutation.mem_iff.mpr hn)
  exact (sample_product_is_minimal_sufficient_relation numerator denominator
    numeratorNonzero denominatorNonzero permutation.length_eq).2 permutation.prod_eq

#print axioms perm_samples_parameter_independent

/-- The ratio for samples `[2]` and `[1]` differs at parameters two and three. -/
theorem likelihood_ratio_changes_between_two_and_three :
    zetaLikelihoodRatio (⟨2, by norm_num⟩ : ZetaParameter) [2] [1] ≠
      zetaLikelihoodRatio (⟨3, by norm_num⟩ : ZetaParameter) [2] [1] := by
  rw [zeta_likelihood_ratio_eq_product_ratio_rpow _ _ _ (by simp),
    zeta_likelihood_ratio_eq_product_ratio_rpow _ _ _ (by simp)]
  norm_num [sampleProduct, Real.rpow_natCast]

#print axioms likelihood_ratio_changes_between_two_and_three

/-- A zero in the numerator makes the ratio constantly zero despite unequal products. -/
theorem numerator_nonzero_is_necessary :
    ¬(∀ n ∈ [0], n ≠ 0) ∧ zetaRatioParameterIndependent [0] [1] ∧
      sampleProduct [0] ≠ sampleProduct [1] := by
  refine ⟨by simp, ?_, by simp [sampleProduct]⟩
  intro first second
  have firstPos : 0 < first.1 := lt_trans zero_lt_one first.2
  have secondPos : 0 < second.1 := lt_trans zero_lt_one second.2
  simp [zetaLikelihoodRatio, zetaSampleLikelihood, pmfReal, zeta_dist_apply,
    weight_zero first.1 firstPos, weight_zero second.1 secondPos]

#print axioms numerator_nonzero_is_necessary

/-- A zero in the denominator is totalized to a constantly zero ratio with unequal products. -/
theorem denominator_nonzero_is_necessary :
    ¬(∀ n ∈ [0], n ≠ 0) ∧ zetaRatioParameterIndependent [1] [0] ∧
      sampleProduct [1] ≠ sampleProduct [0] := by
  refine ⟨by simp, ?_, by simp [sampleProduct]⟩
  intro first second
  have firstPos : 0 < first.1 := lt_trans zero_lt_one first.2
  have secondPos : 0 < second.1 := lt_trans zero_lt_one second.2
  simp [zetaLikelihoodRatio, zetaSampleLikelihood, pmfReal, zeta_dist_apply,
    weight_zero first.1 firstPos, weight_zero second.1 secondPos]

#print axioms denominator_nonzero_is_necessary

private theorem partition_function_three_lt_two : partitionFunction 3 < partitionFunction 2 := by
  apply ENNReal.tsum_lt_tsum (partition_function_ne_top 3 (by norm_num))
  · intro n
    rw [weight, weight]
    apply ENNReal.ofReal_le_ofReal
    rcases n with _ | n
    · norm_num [Real.zero_rpow]
    · apply Real.rpow_le_rpow_of_exponent_le
      · exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
      · norm_num
  · change ENNReal.ofReal ((2 : Real) ^ (-(3 : Real))) <
      ENNReal.ofReal ((2 : Real) ^ (-(2 : Real)))
    rw [ENNReal.ofReal_lt_ofReal_iff
      (Real.rpow_pos_of_pos (by norm_num : (0 : Real) < 2) (-(2 : Real)))]
    exact Real.rpow_lt_rpow_of_exponent_lt
      (by norm_num : (1 : Real) < 2) (by norm_num : (-(3 : Real)) < -(2 : Real))

/-- Unequal sample lengths can have equal products while the normalization makes the ratio vary. -/
theorem equal_sample_size_is_necessary :
    sampleProduct [1] = sampleProduct [] ∧
      ¬zetaRatioParameterIndependent [1] [] := by
  refine ⟨by simp [sampleProduct], ?_⟩
  intro independent
  have atTwoThree := independent
    (⟨2, by norm_num⟩ : ZetaParameter) (⟨3, by norm_num⟩ : ZetaParameter)
  have inverseEqual :
      (partitionFunction 2).toReal⁻¹ = (partitionFunction 3).toReal⁻¹ := by
    simpa [zetaLikelihoodRatio, zeta_sample_likelihood_eq, sampleProduct] using atTwoThree
  have partitionToRealLt :
      (partitionFunction 3).toReal < (partitionFunction 2).toReal :=
    (ENNReal.toReal_lt_toReal
      (partition_function_ne_top 3 (by norm_num))
      (partition_function_ne_top 2 (by norm_num))).2 partition_function_three_lt_two
  have inverseLt :
      (partitionFunction 2).toReal⁻¹ < (partitionFunction 3).toReal⁻¹ :=
    (inv_lt_inv₀ (partition_toReal_pos 2 (by norm_num))
      (partition_toReal_pos 3 (by norm_num))).2 partitionToRealLt
  exact (ne_of_lt inverseLt) inverseEqual

#print axioms equal_sample_size_is_necessary

/-- At inverse temperature one the partition function diverges, so normalization is unavailable. -/
theorem inverse_temperature_bound_is_necessary :
    ¬(1 < (1 : Real)) ∧ partitionFunction 1 = ∞ := by
  exact ⟨by norm_num, weight_one_tsum_eq_top⟩

#print axioms inverse_temperature_bound_is_necessary

end

end D5.S3.Analytic.ZetaObservation.MinimalSufficientRelation
