/- GID: D5/S3/Arith/Robin/PriceRecord/ActualInventoryCollectiveSeparation
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/PriceRecord/ActualInventoryCollectiveSeparation
   mirror-E: none(waiver:exact-original-margin-separation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Arith/Robin/PriceRecord/ActualInventoryCollectiveSeparation.inventory_singletons_imply_collective; result=D5/S3/Arith/Robin/PriceRecord/ActualInventoryCollectiveSeparation.result; claim=D5/S3/Arith/Robin/PriceRecord/ActualInventoryCollectiveSeparation.inventory_singletons_imply_collective
   digest: An actual own-clock strict inventory defeats the collective Robin implication. -/

import D5.S3.Arith.Robin.PriceRecord.NonlinearPrimeExclusion
import D5.S3.Arith.Robin.PriceRecord.ActualInventoryTailBounds
import D5.S3.Arith.GoldenResource5040PriceInterval

/-! Exact rational estimates use the existing native atanh and gamma suppliers.
No external numerical certificate is a premise. The new finite separation uses
actual valuation layers, a positive original margin, and the same integer clock.
The universal implication, not RH, is the statement refuted below. -/

set_option autoImplicit false
set_option maxRecDepth 100000
noncomputable section
namespace D5.S3.Arith.Robin.PriceRecord.ActualInventoryCollectiveSeparation

open D5.S3.Arith.GoldenResourceOptimalInteger
open D5.S3.Arith.GoldenResource.GoldenResourceThresholdCriterion
open D5.S3.Arith.GoldenResourceObjectiveFactorization
open D5.S3.Arith.GoldenResource5040PriceInterval
open D5.S3.Arith.GoldenResource.GoldenSmallestMissingPrime
open D5.S3.Arith.GoldenResource.FirstLayerMarginalAntitone
open D5.S3.Arith.GoldenResource.GoldenResource5040EndpointComparison
open D5.S3.Arith.GoldenResource.RobinRationalBasis
open D5.S3.Arith.Robin.ActualTwoPriceDefect
open D5.S3.Arith.Robin.ActualGlobalBracketing
open D5.S3.Arith.Robin.ActualRobinInterval
open D5.S3.Arith.Robin.PriceRecord.ActualBalancedCutoff
open D5.S3.Arith.Robin.PriceRecord.NonlinearPrimeExclusion
open D5.S3.Weil.GronwallLowerEnvelope
open D5.S3.Arith.Robin.PriceRecord.ActualInventoryBounds
open scoped BigOperators

def witnessN : ℕ := 2021649740510400
def witnessM : ℕ := 6198089008491993412800
private abbrev L : ℝ := Real.log (witnessN : ℝ)
private abbrev f (x : ℝ) : ℝ := Real.log (Real.log x)

private theorem clock_bounds_raw :
    ((352426901 / 10000000) : ℝ) < Real.log 2021649740510400 ∧ Real.log 2021649740510400 <
        (44053363 / 1250000) := by
  refine rational_log_bounds 2021649740510400 (31588277195475 / 17592186044416) _ _ 50 8
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [atanhPartial, Finset.sum_range_succ]

private theorem clock_bounds : ((352426901 / 10000000) : ℝ) < L ∧ L < (44053363 / 1250000) :=
    clock_bounds_raw

private theorem m_clock_bounds :
    ((250892639 / 5000000) : ℝ) < Real.log 6198089008491993412800 ∧ Real.log
        6198089008491993412800 < (501785281 / 10000000) := by
  refine rational_log_bounds 6198089008491993412800 (96845140757687397075 /
      73786976294838206464) _ _ 72 8
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [atanhPartial, Finset.sum_range_succ]

private theorem log_literal_96 :
    ((39155871 / 10000000) : ℝ) < Real.log (250892639 / 5000000) ∧ Real.log (250892639 /
        5000000) < (19577937 / 5000000) := by
  refine rational_log_bounds (250892639 / 5000000) (250892639 / 160000000) _ _ 5 8
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [atanhPartial, Finset.sum_range_succ]

private theorem log_literal_97 :
    ((39155871 / 10000000) : ℝ) < Real.log (501785281 / 10000000) ∧ Real.log (501785281 /
        10000000) < (19577937 / 5000000) := by
  refine rational_log_bounds (501785281 / 10000000) (501785281 / 320000000) _ _ 5 8
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [atanhPartial, Finset.sum_range_succ]

private theorem m_log_clock_bounds :
    ((39155871 / 10000000) : ℝ) < Real.log (Real.log (6198089008491993412800 : ℝ)) ∧ Real.log
        (Real.log (6198089008491993412800 : ℝ)) < (19577937 / 5000000) := by
  exact log_interval_bounds (by norm_num) (m_clock_bounds).1 (m_clock_bounds).2 log_literal_96.1
      log_literal_97.2

private theorem log_literal_98 :
    ((13649651 / 10000000) : ℝ) < Real.log (39155871 / 10000000) ∧ Real.log (39155871 /
        10000000) < (6824827 / 5000000) := by
  refine rational_log_bounds (39155871 / 10000000) (39155871 / 20000000) _ _ 1 8
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [atanhPartial, Finset.sum_range_succ]

private theorem log_literal_99 :
    ((3412413 / 2500000) : ℝ) < Real.log (19577937 / 5000000) ∧ Real.log (19577937 / 5000000) <
        (2729931 / 2000000) := by
  refine rational_log_bounds (19577937 / 5000000) (19577937 / 10000000) _ _ 1 8
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [atanhPartial, Finset.sum_range_succ]

private theorem m_f_clock_bounds :
    ((13649651 / 10000000) : ℝ) < Real.log (Real.log (Real.log (6198089008491993412800 : ℝ))) ∧
        Real.log (Real.log (Real.log (6198089008491993412800 : ℝ))) < (2729931 / 2000000) := by
  exact log_interval_bounds (by norm_num) (m_log_clock_bounds).1 (m_log_clock_bounds).2
      log_literal_98.1 log_literal_99.2

private def support : Finset ℕ := {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31}

private def exponent (p : ℕ) : ℕ :=
  if p = 2 then 6 else if p = 3 then 3 else if p = 5 then 2 else if p = 7 then 2 else if p = 11
      then 1 else if p = 13 then 1 else if p = 17 then 1 else if p = 19 then 1 else if p = 23
      then 1 else if p = 29 then 1 else if p = 31 then 1 else 0

private theorem raw_factorization_N : witnessN.factorization = Finsupp.single 2 6 +
    Finsupp.single 3 3 + Finsupp.single 5 2 + Finsupp.single 7 2 + Finsupp.single 11 1 +
    Finsupp.single 13 1 + Finsupp.single 17 1 + Finsupp.single 19 1 + Finsupp.single 23 1 +
    Finsupp.single 29 1 + Finsupp.single 31 1 := by
  rw [show witnessN = 2 ^ 6 * 3 ^ 3 * 5 ^ 2 * 7 ^ 2 * 11 ^ 1 * 13 ^ 1 * 17 ^ 1 * 19 ^ 1 * 23 ^ 1
      * 29 ^ 1 * 31 ^ 1 by norm_num [witnessN]]
  rw [Nat.factorization_mul (by norm_num) (by norm_num)]
  rw [Nat.factorization_mul (by norm_num) (by norm_num)]
  rw [Nat.factorization_mul (by norm_num) (by norm_num)]
  rw [Nat.factorization_mul (by norm_num) (by norm_num)]
  rw [Nat.factorization_mul (by norm_num) (by norm_num)]
  rw [Nat.factorization_mul (by norm_num) (by norm_num)]
  rw [Nat.factorization_mul (by norm_num) (by norm_num)]
  rw [Nat.factorization_mul (by norm_num) (by norm_num)]
  rw [Nat.factorization_mul (by norm_num) (by norm_num)]
  rw [Nat.factorization_mul (by norm_num) (by norm_num)]
  rw [(by norm_num : Nat.Prime 2).factorization_pow, (by norm_num : Nat.Prime
      3).factorization_pow, (by norm_num : Nat.Prime 5).factorization_pow, (by norm_num :
      Nat.Prime 7).factorization_pow, (by norm_num : Nat.Prime 11).factorization_pow, (by
      norm_num : Nat.Prime 13).factorization_pow, (by norm_num : Nat.Prime
      17).factorization_pow, (by norm_num : Nat.Prime 19).factorization_pow, (by norm_num :
      Nat.Prime 23).factorization_pow, (by norm_num : Nat.Prime 29).factorization_pow, (by
      norm_num : Nat.Prime 31).factorization_pow]

private theorem factorization_N (p : ℕ) : witnessN.factorization p = exponent p := by
  rw [raw_factorization_N]
  simp only [Finsupp.add_apply, Finsupp.single_apply]
  by_cases h2 : p = 2
  · subst p
    norm_num [exponent]
  by_cases h3 : p = 3
  · subst p
    norm_num [exponent]
  by_cases h5 : p = 5
  · subst p
    norm_num [exponent]
  by_cases h7 : p = 7
  · subst p
    norm_num [exponent]
  by_cases h11 : p = 11
  · subst p
    norm_num [exponent]
  by_cases h13 : p = 13
  · subst p
    norm_num [exponent]
  by_cases h17 : p = 17
  · subst p
    norm_num [exponent]
  by_cases h19 : p = 19
  · subst p
    norm_num [exponent]
  by_cases h23 : p = 23
  · subst p
    norm_num [exponent]
  by_cases h29 : p = 29
  · subst p
    norm_num [exponent]
  by_cases h31 : p = 31
  · subst p
    norm_num [exponent]
  simp [exponent, eq_comm, h2, h3, h5, h7, h11, h13, h17, h19, h23, h29, h31]

private theorem support_N : witnessN.primeFactors = support := by
  classical
  ext p
  rw [← Nat.support_factorization, Finsupp.mem_support_iff, factorization_N]
  simp only [exponent, support, Finset.mem_insert, Finset.mem_singleton]
  split_ifs <;> simp_all

private theorem support_cover : Nat.primesLE 36 = support := by decide
private theorem support_floor : Nat.primesLE 34 = support := by decide

private theorem omitted_ge {p : ℕ} (hp : p.Prime) (hn : p ∉ support) : 37 ≤ p := by
  by_contra h
  have hm := Nat.mem_primesLE.mpr ⟨(by omega : p ≤ 36), hp⟩
  rw [support_cover] at hm
  exact hn hm

private theorem actual_cofactor {p : ℕ} (hp : p ∈ support) : 5040 < witnessN / p := by
  simp only [support, Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals norm_num [witnessN]

private theorem sigma_N : ArithmeticFunction.sigma 1 witnessN = 12508191424512000 := by
  rw [show witnessN = 2 ^ 6 * 3 ^ 3 * 5 ^ 2 * 7 ^ 2 * 11 ^ 1 * 13 ^ 1 * 17 ^ 1 * 19 ^ 1 * 23 ^ 1
      * 29 ^ 1 * 31 ^ 1 by norm_num [witnessN]]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2),
      ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 3),
      ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 5),
      ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 7),
      ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 11),
      ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 13),
      ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 17),
      ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 19),
      ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 23),
      ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 29),
      ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 31)]
  norm_num

private theorem sigma_M : ArithmeticFunction.sigma 1 witnessM = 42162011260556673024000 := by
  rw [show witnessM = 2 ^ 6 * 3 ^ 3 * 5 ^ 2 * 7 ^ 2 * 11 ^ 1 * 13 ^ 1 * 17 ^ 1 * 19 ^ 1 * 23 ^ 1
      * 29 ^ 1 * 31 ^ 1 * 37 ^ 1 * 41 ^ 1 * 43 ^ 1 * 47 ^ 1 by norm_num [witnessM]]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2),
      ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 3),
      ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 5),
      ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 7),
      ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 11),
      ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 13),
      ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 17),
      ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 19),
      ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 23),
      ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 29),
      ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 31),
      ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 37),
      ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 41),
      ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 43),
      ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 47)]
  norm_num

private theorem positive_clock : 16 < L := by
  have := clock_bounds.1
  norm_num at this ⊢
  linarith

private theorem price_positive : 0 < price L := price_pos (by have := positive_clock; linarith)

private theorem clock_product : (125 : ℝ) < L * Real.log L ∧ L * Real.log L < 126 := by
  have hn := clock_bounds
  have hl := (log_clock_bounds clock_bounds)
  constructor <;> nlinarith only [hn.1, hn.2, hl.1, hl.2]

private theorem threshold_2 :
    price L < goldenLayerMarginal 2 6 ∧
      goldenLayerMarginal 2 7 < price L := by
  apply layer_pair_of_clock_product clock_product
    (Real.log_pos (by norm_num : (1 : ℝ) < 2))
    gain_2_6_identity gain_2_7_identity
  · nlinarith only [log_prime_2.2, gain_2_6_bounds.1]
  · nlinarith only [log_prime_2.1, gain_2_7_bounds.2]
  · have h := gain_2_7_bounds.1
    linarith

private theorem threshold_3 :
    price L < goldenLayerMarginal 3 3 ∧
      goldenLayerMarginal 3 4 < price L := by
  apply layer_pair_of_clock_product clock_product
    (Real.log_pos (by norm_num : (1 : ℝ) < 3))
    gain_3_3_identity gain_3_4_identity
  · nlinarith only [log_prime_3.2, gain_3_3_bounds.1]
  · nlinarith only [log_prime_3.1, gain_3_4_bounds.2]
  · have h := gain_3_4_bounds.1
    linarith

private theorem threshold_5 :
    price L < goldenLayerMarginal 5 2 ∧
      goldenLayerMarginal 5 3 < price L := by
  apply layer_pair_of_clock_product clock_product
    (Real.log_pos (by norm_num : (1 : ℝ) < 5))
    gain_5_2_identity gain_5_3_identity
  · nlinarith only [log_prime_5.2, gain_5_2_bounds.1]
  · nlinarith only [log_prime_5.1, gain_5_3_bounds.2]
  · have h := gain_5_3_bounds.1
    linarith

private theorem threshold_7 :
    price L < goldenLayerMarginal 7 2 ∧
      goldenLayerMarginal 7 3 < price L := by
  apply layer_pair_of_clock_product clock_product
    (Real.log_pos (by norm_num : (1 : ℝ) < 7))
    gain_7_2_identity gain_7_3_identity
  · nlinarith only [log_prime_7.2, gain_7_2_bounds.1]
  · nlinarith only [log_prime_7.1, gain_7_3_bounds.2]
  · have h := gain_7_3_bounds.1
    linarith

private theorem threshold_11 :
    price L < goldenLayerMarginal 11 1 ∧
      goldenLayerMarginal 11 2 < price L := by
  apply layer_pair_of_clock_product clock_product
    (Real.log_pos (by norm_num : (1 : ℝ) < 11))
    gain_11_1_identity gain_11_2_identity
  · nlinarith only [log_prime_11.2, gain_11_1_bounds.1]
  · nlinarith only [log_prime_11.1, gain_11_2_bounds.2]
  · have h := gain_11_2_bounds.1
    linarith

private theorem threshold_13 :
    price L < goldenLayerMarginal 13 1 ∧
      goldenLayerMarginal 13 2 < price L := by
  apply layer_pair_of_clock_product clock_product
    (Real.log_pos (by norm_num : (1 : ℝ) < 13))
    gain_13_1_identity gain_13_2_identity
  · nlinarith only [log_prime_13.2, gain_13_1_bounds.1]
  · nlinarith only [log_prime_13.1, gain_13_2_bounds.2]
  · have h := gain_13_2_bounds.1
    linarith

private theorem threshold_17 :
    price L < goldenLayerMarginal 17 1 ∧
      goldenLayerMarginal 17 2 < price L := by
  apply layer_pair_of_clock_product clock_product
    (Real.log_pos (by norm_num : (1 : ℝ) < 17))
    gain_17_1_identity gain_17_2_identity
  · nlinarith only [log_prime_17.2, gain_17_1_bounds.1]
  · nlinarith only [log_prime_17.1, gain_17_2_bounds.2]
  · have h := gain_17_2_bounds.1
    linarith

private theorem threshold_19 :
    price L < goldenLayerMarginal 19 1 ∧
      goldenLayerMarginal 19 2 < price L := by
  apply layer_pair_of_clock_product clock_product
    (Real.log_pos (by norm_num : (1 : ℝ) < 19))
    gain_19_1_identity gain_19_2_identity
  · nlinarith only [log_prime_19.2, gain_19_1_bounds.1]
  · nlinarith only [log_prime_19.1, gain_19_2_bounds.2]
  · have h := gain_19_2_bounds.1
    linarith

private theorem threshold_23 :
    price L < goldenLayerMarginal 23 1 ∧
      goldenLayerMarginal 23 2 < price L := by
  apply layer_pair_of_clock_product clock_product
    (Real.log_pos (by norm_num : (1 : ℝ) < 23))
    gain_23_1_identity gain_23_2_identity
  · nlinarith only [log_prime_23.2, gain_23_1_bounds.1]
  · nlinarith only [log_prime_23.1, gain_23_2_bounds.2]
  · have h := gain_23_2_bounds.1
    linarith

private theorem threshold_29 :
    price L < goldenLayerMarginal 29 1 ∧
      goldenLayerMarginal 29 2 < price L := by
  apply layer_pair_of_clock_product clock_product
    (Real.log_pos (by norm_num : (1 : ℝ) < 29))
    gain_29_1_identity gain_29_2_identity
  · nlinarith only [log_prime_29.2, gain_29_1_bounds.1]
  · nlinarith only [log_prime_29.1, gain_29_2_bounds.2]
  · have h := gain_29_2_bounds.1
    linarith

private theorem threshold_31 :
    price L < goldenLayerMarginal 31 1 ∧
      goldenLayerMarginal 31 2 < price L := by
  apply layer_pair_of_clock_product clock_product
    (Real.log_pos (by norm_num : (1 : ℝ) < 31))
    gain_31_1_identity gain_31_2_identity
  · nlinarith only [log_prime_31.2, gain_31_1_bounds.1]
  · nlinarith only [log_prime_31.1, gain_31_2_bounds.2]
  · have h := gain_31_2_bounds.1
    linarith

private theorem tail_threshold : goldenLayerMarginal 37 1 < price L := by
  have ht := clock_product
  have hp := log_prime_37
  have hs := gain_37_1_bounds
  have hpos : 0 < L * Real.log L := by linarith only [ht.1]
  apply (mul_lt_mul_iff_left₀ (Real.log_pos (by norm_num : (1 : ℝ) < 37))).mp
  rw [gain_37_1_identity]
  change _ < 1 / (L * Real.log L) * Real.log 37
  rw [one_div_mul_eq_div, lt_div_iff₀ hpos]
  nlinarith only [ht.2, hp.1, hs.1, hs.2]

private theorem supported_rows {p : ℕ} (hp : p ∈ support) :
    price L < goldenLayerMarginal p (exponent p) ∧
      goldenLayerMarginal p (exponent p + 1) < price L := by
  simp only [support, Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals norm_num [exponent]
  all_goals first | exact threshold_2 | exact threshold_3 | exact threshold_5 |
    exact threshold_7 | exact threshold_11 | exact threshold_13 | exact threshold_17 |
    exact threshold_19 | exact threshold_23 | exact threshold_29 | exact threshold_31

private theorem boundary_rows {p : ℕ} (hp : p.Prime) :
    goldenLayerMarginal p (witnessN.factorization p + 1) < price L ∧
      (p ∣ witnessN → price L < goldenLayerMarginal p (witnessN.factorization p)) := by
  classical
  by_cases hm : p ∈ support
  · rw [factorization_N]
    exact ⟨(supported_rows hm).2, fun _ => (supported_rows hm).1⟩
  · have hfac : witnessN.factorization p = 0 := by
      apply Nat.factorization_eq_zero_of_not_dvd
      intro hd
      exact hm (support_N ▸ hp.mem_primeFactors hd (by norm_num [witnessN]))
    have hge := omitted_ge hp hm
    have hμ : goldenLayerMarginal p 1 ≤ goldenLayerMarginal 37 1 := by
      rcases eq_or_lt_of_le hge with rfl | hlt
      · exact le_rfl
      · exact
          (golden_layer_marginal_one_strictAnti
          (by norm_num : Nat.Prime 37) hp hlt).le
    refine ⟨by simpa [hfac] using hμ.trans_lt tail_threshold, ?_⟩
    intro hd
    exact (hm (support_N ▸ hp.mem_primeFactors hd (by norm_num [witnessN]))).elim

private theorem all_layers {p k : ℕ} (hp : p.Prime) (hk : 1 ≤ k) :
    (k ≤ witnessN.factorization p → price L < goldenLayerMarginal p k) ∧
      (witnessN.factorization p < k → goldenLayerMarginal p k < price L) := by
  have hb := boundary_rows hp
  constructor
  · intro he
    have hd : p ∣ witnessN := Nat.dvd_of_factorization_pos (by omega)
    have hl := hb.2 hd
    rcases eq_or_lt_of_le he with rfl | hlt
    · exact hl
    · exact hl.trans (golden_layer_strict_decrease hp hk hlt)
  · intro he
    rcases eq_or_lt_of_le (show witnessN.factorization p + 1 ≤ k by omega) with heq | hlt
    · simpa [← heq] using hb.1
    · exact (golden_layer_strict_decrease hp (by omega) hlt).trans hb.1

private theorem no_ties (p k : ℕ) (hp : p.Prime) (hk : 1 ≤ k) :
    price L ≠ goldenLayerMarginal p k := by
  by_cases he : k ≤ witnessN.factorization p
  · exact (all_layers hp hk).1 he |>.ne
  · exact ((all_layers hp hk).2 (by omega)).ne'

private theorem strict_identity : witnessN = strictInteger (price L) := by
  have hpos : strictInteger (price L) ≠ 0 := by
    have := strictInteger_pos price_positive
    omega
  apply Nat.factorization_inj (by norm_num [witnessN]) hpos
  ext p
  by_cases hp : p.Prime
  · apply le_antisymm
    · by_cases hz : witnessN.factorization p = 0
      · simp [hz]
      · exact (strict_layer_iff price_positive hp (by omega)).mpr
          ((all_layers hp (by omega)).1 le_rfl)
    · by_cases hz : (strictInteger (price L)).factorization p = 0
      · simp [hz]
      · have ha := (strict_layer_iff price_positive hp (by omega)).mp (le_refl ((strictInteger
          (price L)).factorization p))
        by_contra h
        have hb := (all_layers (k := (strictInteger (price L)).factorization p) hp (by omega)).2
            (by omega)
        linarith
  · simp [Nat.factorization_eq_zero_of_not_prime _ hp]

private theorem maximal_identity : witnessN = maximalInteger (price L) := by
  apply Nat.factorization_inj (by norm_num [witnessN]) (show maximalInteger (price L) ≠ 0 by
      have := (maximalInteger_spec price_positive).1; omega)
  ext p
  by_cases hp : p.Prime
  · apply le_antisymm
    · by_cases hz : witnessN.factorization p = 0
      · simp [hz]
      · exact (weak_layer_iff price_positive hp (by omega)).mpr
          (((all_layers hp (by omega)).1 le_rfl).le)
    · by_cases hz : (maximalInteger (price L)).factorization p = 0
      · simp [hz]
      · have ha := (weak_layer_iff price_positive hp (by omega)).mp (le_refl ((maximalInteger
          (price L)).factorization p))
        by_contra h
        have hb := (all_layers (k := (maximalInteger (price L)).factorization p) hp (by
            omega)).2 (by omega)
        linarith
  · simp [Nat.factorization_eq_zero_of_not_prime _ hp]

private theorem own_optimal : IsGoldenResourceOptimal (price L) witnessN := by
  apply (golden_resource_optimal_iff_layer_thresholds price_positive (by norm_num [witnessN])).mpr
  exact ⟨fun p hp => (boundary_rows hp).1.le, fun p hp hd => ((boundary_rows hp).2 hd).le⟩

private theorem unique_optimal {m : ℕ} (hm : 1 ≤ m)
    (hopt : IsGoldenResourceOptimal (price L) m) : m = witnessN := by
  have hmrows := (golden_resource_optimal_iff_layer_thresholds price_positive hm).mp hopt
  apply Nat.factorization_inj (show m ≠ 0 by omega) (by norm_num [witnessN])
  ext p
  by_cases hp : p.Prime
  · apply le_antisymm
    · by_contra h
      have hgt : witnessN.factorization p < m.factorization p := by omega
      have hd := Nat.dvd_of_factorization_pos (by omega : m.factorization p ≠ 0)
      have ha := hmrows.2 p hp hd
      have hb := (all_layers hp (by omega)).2 hgt
      linarith
    · by_contra h
      have hgt : m.factorization p + 1 ≤ witnessN.factorization p := by omega
      have ha := hmrows.1 p hp
      have hb := (all_layers hp (by omega)).1 hgt
      linarith
  · simp [Nat.factorization_eq_zero_of_not_prime _ hp]

private theorem strict_optimizer (m : ℕ) (hm : 1 ≤ m) (hne : m ≠ witnessN) :
    goldenResourceObjective (price L) m < goldenResourceObjective (price L) witnessN := by
  have hle := own_optimal m hm
  by_contra hn
  have he : goldenResourceObjective (price L) m = goldenResourceObjective (price L) witnessN :=
      by linarith
  have ho : IsGoldenResourceOptimal (price L) m := by
    intro k hk
    rw [he]
    exact own_optimal k hk
  exact hne (unique_optimal hm ho)

private theorem below_boundary : price L < boundaryPrice := by
  by_contra h
  have hd := strictInteger_dvd price_positive boundaryPrice_spec.1 (le_of_not_gt h)
  rw [← strict_identity] at hd
  have hlo := Nat.le_of_dvd (by have := strictInteger_pos boundaryPrice_spec.1; omega) hd
  have hhi := boundaryPrice_spec.2.1
  norm_num [witnessN] at hlo
  omega

private theorem W_step {n p : ℕ} (hn : 1 ≤ n) (hp : p.Prime) :
    W (n * p) - W n = goldenLayerMarginal p (n.factorization p + 1) * Real.log p := by
  have hd := golden_resource_objective_single_layer_delta 0 hn hp
  rw [golden_resource_sigma_identity 0 (by nlinarith [hp.one_lt] : 1 ≤ n * p),
    golden_resource_sigma_identity 0 hn] at hd
  simpa only [W, zero_mul, sub_zero] using hd

private theorem strict_insertion {x : ℝ} (hx : 1 < x)
    (hb : 0 < insertionBarrier L x) :
    Real.log (1 + 1 / x) < f (L + Real.log x) - f L := by
  have hL : 1 < L := by have := positive_clock; linarith
  have hL0 : 0 < L := by linarith
  have hx0 : 0 < x := by linarith
  have hlx := Real.log_pos hx
  have hy : 1 < L + Real.log x := by linarith
  have hc : 0 < 1 + 1 / x := by positivity
  change Real.log (1 + 1 / x) < Real.log (Real.log (L + Real.log x)) - Real.log (Real.log L)
  rw [← Real.log_div (Real.log_pos hy).ne' (Real.log_pos hL).ne',
    Real.log_lt_log_iff hc (div_pos (Real.log_pos hy) (Real.log_pos hL)),
    lt_div_iff₀ (Real.log_pos hL)]
  rw [← Real.log_rpow hL0,
    Real.log_lt_log_iff (Real.rpow_pos_of_pos hL0 _) (by linarith : 0 < L + Real.log x)]
  dsimp [insertionBarrier] at hb
  linarith only [hb]

private theorem barrier_slack : 0 < deletionBarrier L 31 ∧ 0 < insertionBarrier L 37 := by
  have hL : 1 < L := by have := positive_clock; linarith
  have h32 : 0 ≤ deletionBarrier L 32 := by
    apply (deletion_test hL (by norm_num) (by have := (gap32_clock clock_bounds).1; linarith)).mpr
    have hf := (f_clock_bounds clock_bounds)
    have hg := gap32_gain
    have hc := (gap32_f clock_bounds)
    norm_num at hg ⊢
    linarith only [hf.2, hg.1, hc.1]
  have h369 : 0 ≤ insertionBarrier L (369 / 10) := by
    apply (insertion_test hL (by norm_num)).mpr
    have hf := (f_clock_bounds clock_bounds)
    have hg := gap369_gain
    have hc := (gap369_f clock_bounds)
    norm_num at hg ⊢
    linarith only [hf.2, hg.2, hc.1]
  constructor
  · have hm := deletion_strictAnti hL (by norm_num : (31 : ℝ) ∈ Set.Ioi 1)
      (by norm_num : (32 : ℝ) ∈ Set.Ioi 1) (by norm_num : (31 : ℝ) < 32)
    linarith
  · have hm := insertion_strictMono hL (by norm_num : (369 / 10 : ℝ) ∈ Set.Ioi 1)
      (by norm_num : (37 : ℝ) ∈ Set.Ioi 1) (by norm_num : (369 / 10 : ℝ) < 37)
    linarith

private theorem actual_steps_2 :
    f L - f (L - Real.log 2) < goldenLayerMarginal 2 6 * Real.log 2 ∧
      goldenLayerMarginal 2 7 * Real.log 2 < f (L + Real.log 2) - f L := by
  rw [gain_2_6_identity, gain_2_7_identity]
  have hf := (f_clock_bounds clock_bounds)
  have hd := (delete_2_f clock_bounds)
  have hi := (insert_2_f clock_bounds)
  have he := gain_2_6_bounds
  have hn := gain_2_7_bounds
  constructor <;> linarith only [hf.1, hf.2, hd.1, hi.1, he.1, hn.2]

private theorem actual_steps_3 :
    f L - f (L - Real.log 3) < goldenLayerMarginal 3 3 * Real.log 3 ∧
      goldenLayerMarginal 3 4 * Real.log 3 < f (L + Real.log 3) - f L := by
  rw [gain_3_3_identity, gain_3_4_identity]
  have hf := (f_clock_bounds clock_bounds)
  have hd := (delete_3_f clock_bounds)
  have hi := (insert_3_f clock_bounds)
  have he := gain_3_3_bounds
  have hn := gain_3_4_bounds
  constructor <;> linarith only [hf.1, hf.2, hd.1, hi.1, he.1, hn.2]

private theorem actual_steps_5 :
    f L - f (L - Real.log 5) < goldenLayerMarginal 5 2 * Real.log 5 ∧
      goldenLayerMarginal 5 3 * Real.log 5 < f (L + Real.log 5) - f L := by
  rw [gain_5_2_identity, gain_5_3_identity]
  have hf := (f_clock_bounds clock_bounds)
  have hd := (delete_5_f clock_bounds)
  have hi := (insert_5_f clock_bounds)
  have he := gain_5_2_bounds
  have hn := gain_5_3_bounds
  constructor <;> linarith only [hf.1, hf.2, hd.1, hi.1, he.1, hn.2]

private theorem actual_steps_7 :
    f L - f (L - Real.log 7) < goldenLayerMarginal 7 2 * Real.log 7 ∧
      goldenLayerMarginal 7 3 * Real.log 7 < f (L + Real.log 7) - f L := by
  rw [gain_7_2_identity, gain_7_3_identity]
  have hf := (f_clock_bounds clock_bounds)
  have hd := (delete_7_f clock_bounds)
  have hi := (insert_7_f clock_bounds)
  have he := gain_7_2_bounds
  have hn := gain_7_3_bounds
  constructor <;> linarith only [hf.1, hf.2, hd.1, hi.1, he.1, hn.2]

private theorem actual_steps_11 :
    f L - f (L - Real.log 11) < goldenLayerMarginal 11 1 * Real.log 11 ∧
      goldenLayerMarginal 11 2 * Real.log 11 < f (L + Real.log 11) - f L := by
  rw [gain_11_1_identity, gain_11_2_identity]
  have hf := (f_clock_bounds clock_bounds)
  have hd := (delete_11_f clock_bounds)
  have hi := (insert_11_f clock_bounds)
  have he := gain_11_1_bounds
  have hn := gain_11_2_bounds
  constructor <;> linarith only [hf.1, hf.2, hd.1, hi.1, he.1, hn.2]

private theorem actual_steps_13 :
    f L - f (L - Real.log 13) < goldenLayerMarginal 13 1 * Real.log 13 ∧
      goldenLayerMarginal 13 2 * Real.log 13 < f (L + Real.log 13) - f L := by
  rw [gain_13_1_identity, gain_13_2_identity]
  have hf := (f_clock_bounds clock_bounds)
  have hd := (delete_13_f clock_bounds)
  have hi := (insert_13_f clock_bounds)
  have he := gain_13_1_bounds
  have hn := gain_13_2_bounds
  constructor <;> linarith only [hf.1, hf.2, hd.1, hi.1, he.1, hn.2]

private theorem actual_steps_17 :
    f L - f (L - Real.log 17) < goldenLayerMarginal 17 1 * Real.log 17 ∧
      goldenLayerMarginal 17 2 * Real.log 17 < f (L + Real.log 17) - f L := by
  rw [gain_17_1_identity, gain_17_2_identity]
  have hf := (f_clock_bounds clock_bounds)
  have hd := (delete_17_f clock_bounds)
  have hi := (insert_17_f clock_bounds)
  have he := gain_17_1_bounds
  have hn := gain_17_2_bounds
  constructor <;> linarith only [hf.1, hf.2, hd.1, hi.1, he.1, hn.2]

private theorem actual_steps_19 :
    f L - f (L - Real.log 19) < goldenLayerMarginal 19 1 * Real.log 19 ∧
      goldenLayerMarginal 19 2 * Real.log 19 < f (L + Real.log 19) - f L := by
  rw [gain_19_1_identity, gain_19_2_identity]
  have hf := (f_clock_bounds clock_bounds)
  have hd := (delete_19_f clock_bounds)
  have hi := (insert_19_f clock_bounds)
  have he := gain_19_1_bounds
  have hn := gain_19_2_bounds
  constructor <;> linarith only [hf.1, hf.2, hd.1, hi.1, he.1, hn.2]

private theorem actual_steps_23 :
    f L - f (L - Real.log 23) < goldenLayerMarginal 23 1 * Real.log 23 ∧
      goldenLayerMarginal 23 2 * Real.log 23 < f (L + Real.log 23) - f L := by
  rw [gain_23_1_identity, gain_23_2_identity]
  have hf := (f_clock_bounds clock_bounds)
  have hd := (delete_23_f clock_bounds)
  have hi := (insert_23_f clock_bounds)
  have he := gain_23_1_bounds
  have hn := gain_23_2_bounds
  constructor <;> linarith only [hf.1, hf.2, hd.1, hi.1, he.1, hn.2]

private theorem actual_steps_29 :
    f L - f (L - Real.log 29) < goldenLayerMarginal 29 1 * Real.log 29 ∧
      goldenLayerMarginal 29 2 * Real.log 29 < f (L + Real.log 29) - f L := by
  rw [gain_29_1_identity, gain_29_2_identity]
  have hf := (f_clock_bounds clock_bounds)
  have hd := (delete_29_f clock_bounds)
  have hi := (insert_29_f clock_bounds)
  have he := gain_29_1_bounds
  have hn := gain_29_2_bounds
  constructor <;> linarith only [hf.1, hf.2, hd.1, hi.1, he.1, hn.2]

private theorem actual_steps_31 :
    f L - f (L - Real.log 31) < goldenLayerMarginal 31 1 * Real.log 31 ∧
      goldenLayerMarginal 31 2 * Real.log 31 < f (L + Real.log 31) - f L := by
  rw [gain_31_1_identity, gain_31_2_identity]
  have hf := (f_clock_bounds clock_bounds)
  have hd := (delete_31_f clock_bounds)
  have hi := (insert_31_f clock_bounds)
  have he := gain_31_1_bounds
  have hn := gain_31_2_bounds
  constructor <;> linarith only [hf.1, hf.2, hd.1, hi.1, he.1, hn.2]

private theorem supported_step_slacks {p : ℕ} (hp : p ∈ support) :
    f L - f (L - Real.log p) < goldenLayerMarginal p (witnessN.factorization p) * Real.log p ∧
      goldenLayerMarginal p (witnessN.factorization p + 1) * Real.log p < f (L + Real.log p) - f
          L := by
  rw [factorization_N]
  simp only [support, Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals norm_num [exponent]
  all_goals first | exact actual_steps_2 | exact actual_steps_3 | exact actual_steps_5 |
    exact actual_steps_7 | exact actual_steps_11 | exact actual_steps_13 | exact actual_steps_17 |
    exact actual_steps_19 | exact actual_steps_23 | exact actual_steps_29 | exact actual_steps_31

private theorem deletion_comparisons (p : ℕ) (hp : p.Prime) (hd : p ∣ witnessN) :
    5040 < witnessN / p ∧ robinLogMargin witnessN < robinLogMargin (witnessN / p) := by
  have hm : p ∈ support := support_N ▸ hp.mem_primeFactors hd (by norm_num [witnessN])
  have hc := actual_cofactor hm
  have heq : witnessN / p * p = witnessN := Nat.div_mul_cancel hd
  have hfac : (witnessN / p).factorization p + 1 = witnessN.factorization p := by
    have hh := congrArg (fun m : ℕ => m.factorization p) heq
    simp only [Nat.factorization_mul (by omega : witnessN / p ≠ 0) hp.ne_zero,
      Finsupp.coe_add, Pi.add_apply, hp.factorization, Finsupp.single_eq_same] at hh
    exact hh
  have hw := W_step (by omega : 1 ≤ witnessN / p) hp
  rw [heq, hfac] at hw
  have hclock : Real.log (witnessN / p : ℕ) = L - Real.log p := by
    have hh := congrArg (fun n : ℕ => Real.log (n : ℝ)) heq
    rw [Nat.cast_mul, Real.log_mul (Nat.cast_pos.mpr (by omega : 0 < witnessN / p)).ne'
      (Nat.cast_pos.mpr hp.pos).ne'] at hh
    change _ = Real.log (witnessN : ℝ) - Real.log p
    linarith only [hh]
  refine ⟨hc, ?_⟩
  have hs := (supported_step_slacks hm).1
  rw [margin_eq_threshold_sub_W, margin_eq_threshold_sub_W, hclock]
  change Real.eulerMascheroniConstant + f L - W witnessN <
    Real.eulerMascheroniConstant + f (L - Real.log p) - W (witnessN / p)
  linarith only [hw, hs]

private theorem insertion_comparisons (p : ℕ) (hp : p.Prime) :
    robinLogMargin witnessN < robinLogMargin (witnessN * p) := by
  classical
  have hw := W_step (by norm_num [witnessN] : 1 ≤ witnessN) hp
  have hclock : Real.log (witnessN * p : ℕ) = L + Real.log p := by
    rw [Nat.cast_mul, Real.log_mul (by norm_num [witnessN]) (Nat.cast_pos.mpr hp.pos).ne']
  have hs : goldenLayerMarginal p (witnessN.factorization p + 1) * Real.log p <
      f (L + Real.log p) - f L := by
    by_cases hm : p ∈ support
    · exact (supported_step_slacks hm).2
    · have hge := omitted_ge hp hm
      have hreal : (37 : ℝ) ≤ p := by exact_mod_cast hge
      have hbp : 0 < insertionBarrier L p := by
        have hm := (insertion_strictMono (by have := positive_clock; linarith)).monotoneOn
          (by norm_num : (37 : ℝ) ∈ Set.Ioi 1)
          (by change (1 : ℝ) < p; exact_mod_cast hp.one_lt) hreal
        exact barrier_slack.2.trans_le hm
      have hf : witnessN.factorization p = 0 := Nat.factorization_eq_zero_of_not_dvd (by
        intro hd; exact hm (support_N ▸ hp.mem_primeFactors hd (by norm_num [witnessN])))
      rw [hf, zero_add, golden_layer_marginal_one_eq_log_one_add_inv hp,
        div_mul_cancel₀ _ hp.log_pos.ne']
      exact strict_insertion (by exact_mod_cast hp.one_lt) hbp
  rw [margin_eq_threshold_sub_W, margin_eq_threshold_sub_W, hclock]
  change Real.eulerMascheroniConstant + f L - W witnessN <
    Real.eulerMascheroniConstant + f (L + Real.log p) - W (witnessN * p)
  linarith only [hw, hs]

private theorem cutoff_bracket : price L < firstLayerPrice 34 ∧ firstLayerPrice 35 < price L := by
  have ht := clock_product
  have hpos : 0 < L * Real.log L := by linarith only [ht.1]
  constructor
  · have hp := log_prime_34
    have hg := gain_34_1_bounds
    change 1 / (L * Real.log L) < Real.log (1 + 1 / (34 : ℝ)) / Real.log 34
    apply (div_lt_div_iff₀ hpos (Real.log_pos (by norm_num : (1 : ℝ) < 34))).mpr
    norm_num at hg ⊢
    nlinarith only [ht.1, hp.2, hg.1]
  · have hp := log_prime_35
    have hg := gain_35_1_bounds
    change Real.log (1 + 1 / (35 : ℝ)) / Real.log 35 < 1 / (L * Real.log L)
    apply (div_lt_div_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 35)) hpos).mpr
    norm_num at hg ⊢
    nlinarith only [ht.2, hp.1, hg.1, hg.2]

private theorem same_cutoff_gap :
    ∃ z α β : ℝ, 11 < z ∧ 0 < L - z ∧ L - z < 1 / 2 ∧
      firstLayerPrice z = price L ∧
      (∀ t : ℝ, 1 < t → firstLayerPrice t = price L → t = z) ∧
      34 < z ∧ z < 35 ∧ ⌊z⌋₊ = 34 ∧
      witnessN.primeFactors = Nat.primesLE ⌊z⌋₊ ∧
      NonlinearPrimeGap witnessN z α β ∧ 31 < α ∧ β < 37 := by
  obtain ⟨z, hz, hzl, hhalf, hroot, hu⟩ := half_shift_cutoff (by have := positive_clock; linarith)
  have hz1 : 1 < z := by linarith
  have hz34 : 34 < z := by
    by_contra hn
    have hm := firstLayerPrice_strictAnti.antitoneOn hz1 (by norm_num : (1 : ℝ) < 34)
        (le_of_not_gt hn)
    rw [hroot] at hm
    linarith only [hm, cutoff_bracket.1]
  have hz35 : z < 35 := by
    by_contra hn
    have hm := firstLayerPrice_strictAnti.antitoneOn (by norm_num : (1 : ℝ) < 35) hz1
        (le_of_not_gt hn)
    rw [hroot] at hm
    linarith only [hm, cutoff_bracket.2]
  have hfloor : ⌊z⌋₊ = 34 := by
    apply (Nat.floor_eq_iff (by linarith : 0 ≤ z)).mpr
    constructor
    · exact hz34.le
    · norm_num
      exact hz35
  have hL1 : 1 < L := by have := positive_clock; linarith
  obtain ⟨α, β, hαlo, hαz, hLβ, hα, hβ, huα, huβ⟩ :=
    barrier_roots positive_clock hz (by linarith only [hzl]) hhalf hroot
  have hα1 : 1 < α := by have := positive_clock; linarith
  have hβ1 : 1 < β := by have := positive_clock; linarith
  have h31 : 31 < α := by
    by_contra hn
    have hm := (deletion_strictAnti hL1).antitoneOn hα1 (by norm_num : (1 : ℝ) < 31)
        (le_of_not_gt hn)
    rw [hα] at hm
    linarith only [barrier_slack.1, hm]
  have h37 : β < 37 := by
    by_contra hn
    have hm := (insertion_strictMono hL1).monotoneOn (by norm_num : (1 : ℝ) < 37) hβ1
        (le_of_not_gt hn)
    rw [hβ] at hm
    linarith only [barrier_slack.2, hm]
  have hgap : NonlinearPrimeGap witnessN z α β := by
    refine ⟨hαlo, hαz, by linarith only [hzl], hLβ, hα, hβ, huα, huβ, ?_⟩
    intro p hp hap
    have hp31 : (31 : ℝ) < p := h31.trans hap
    have hpn : 31 < p := by exact_mod_cast hp31
    have hnot : p ∉ support := by
      simp only [support, Finset.mem_insert, Finset.mem_singleton]
      omega
    have hge : (37 : ℝ) ≤ p := by exact_mod_cast omitted_ge hp hnot
    exact h37.le.trans hge
  refine ⟨z, α, β, hz, hzl, hhalf, hroot, hu, hz34, hz35, hfloor, ?_, hgap, h31, h37⟩
  rw [hfloor, support_N, support_floor]

private theorem original_margins :
    0 < robinLogMargin witnessN ∧ 0 < robinLogMargin witnessM ∧
      robinLogMargin witnessM < robinLogMargin witnessN := by
  have hg := eulerMascheroni_decimal_bounds
  have hn := (f_clock_bounds clock_bounds)
  have hm := m_f_clock_bounds
  have hwn := w_N_bounds_raw
  have hwm := w_M_bounds_raw
  have hwNid : W witnessN = Real.log (70225920 / 11350339 : ℝ) := by
    unfold W
    rw [sigma_N]
    congr 1
    norm_num [witnessN]
  have hwMid : W witnessM = Real.log (3074209873920 / 451928782799 : ℝ) := by
    unfold W
    rw [sigma_M]
    congr 1
    norm_num [witnessM]
  rw [← hwNid] at hwn
  rw [← hwMid] at hwm
  have hwN := hwn
  have hwM := hwm
  rw [margin_eq_threshold_sub_W, margin_eq_threshold_sub_W]
  change 0 < Real.eulerMascheroniConstant + f L - W witnessN ∧
    0 < Real.eulerMascheroniConstant + f (Real.log (witnessM : ℝ)) - W witnessM ∧
    Real.eulerMascheroniConstant + f (Real.log (witnessM : ℝ)) - W witnessM <
      Real.eulerMascheroniConstant + f L - W witnessN
  change _ < f (Real.log (witnessM : ℝ)) ∧ f (Real.log (witnessM : ℝ)) < _ at hm
  constructor
  · linarith only [hg.1, hn.1, hwN.2]
  constructor
  · linarith only [hg.1, hm.1, hwM.2]
  · linarith only [hm.2, hn.1, hwN.2, hwM.1]

private theorem exact_products :
    witnessN = 2 ^ 6 * 3 ^ 3 * 5 ^ 2 * 7 ^ 2 * 11 * 13 * 17 * 19 * 23 * 29 * 31 ∧
      55440 < witnessN ∧ 55440 ∣ witnessN ∧
      (37 * 41 * 43 * 47 : ℕ) = 3065857 ∧
      witnessM = witnessN * (37 * 41 * 43 * 47) ∧
      (1 + 1 / (37 : ℝ)) * (1 + 1 / 41) * (1 + 1 / 43) * (1 + 1 / 47) = 3370752 / 3065857 ∧
      (∀ p ∈ ({37, 41, 43, 47} : Finset ℕ), p.Prime ∧ ¬p ∣ witnessN) := by
  norm_num [witnessN, witnessM]


/-- The complete original own-clock inventory and singleton bundle. It has no
Robin failure or global original-margin minimum hypothesis. -/
structure OwnClockInventorySingletons (n : ℕ) (z α β : ℝ) : Prop where
  large : 55440 < n
  base : 55440 ∣ n
  clock : 16 < Real.log (n : ℝ)
  log_factorization : Real.log (n : ℝ) =
    n.factorization.sum (fun p e => (e : ℝ) * Real.log p)
  price_positive : 0 < price (Real.log n)
  below_boundary : price (Real.log n) < boundaryPrice
  optimal : IsGoldenResourceOptimal (price (Real.log n)) n
  unique : ∀ m : ℕ, 1 ≤ m → m ≠ n →
    goldenResourceObjective (price (Real.log n)) m <
      goldenResourceObjective (price (Real.log n)) n
  strict_inventory : n = strictInteger (price (Real.log n))
  maximal_inventory : n = maximalInteger (price (Real.log n))
  layers : ∀ p k : ℕ, p.Prime → 1 ≤ k →
    (k ≤ n.factorization p → price (Real.log n) < goldenLayerMarginal p k) ∧
      (n.factorization p < k → goldenLayerMarginal p k < price (Real.log n))
  no_ties : ∀ p k : ℕ, p.Prime → 1 ≤ k →
    price (Real.log n) ≠ goldenLayerMarginal p k
  cutoff_large : 11 < z
  half_shift_lower : 0 < Real.log n - z
  half_shift_upper : Real.log n - z < 1 / 2
  root : firstLayerPrice z = 1 / (Real.log n * Real.log (Real.log n))
  cutoff_unique : ∀ t : ℝ, 1 < t →
    firstLayerPrice t = 1 / (Real.log n * Real.log (Real.log n)) → t = z
  support : n.primeFactors = Nat.primesLE ⌊z⌋₊
  gap : NonlinearPrimeGap n z α β
  positive_margin : 0 < robinLogMargin n
  deletion : ∀ p : ℕ, p.Prime → p ∣ n →
    5040 < n / p ∧ robinLogMargin n < robinLogMargin (n / p)
  insertion : ∀ p : ℕ, p.Prime → robinLogMargin n < robinLogMargin (n * p)

/-- The proposed replacement of all fresh finite-product comparisons by the
complete strict inventory, literal nonlinear gap, and actual singleton tests. -/
def inventory_singletons_imply_collective : Prop :=
  ∀ (n : ℕ) (z α β : ℝ), OwnClockInventorySingletons n z α β →
    ∀ s : Finset ℕ, (∀ p ∈ s, p.Prime ∧ ¬p ∣ n) →
      robinLogMargin n ≤ robinLogMargin (n * ∏ p ∈ s, p)

/-- Exact original-integer separator. All clocks, cutoffs, roots and valuation
layers belong to this same N. Both original margins are strictly positive. -/
theorem actual_witness :
    ∃ z α β : ℝ, OwnClockInventorySingletons witnessN z α β ∧
      34 < z ∧ z < 35 ∧ ⌊z⌋₊ = 34 ∧ 31 < α ∧ β < 37 ∧
      witnessN = 2 ^ 6 * 3 ^ 3 * 5 ^ 2 * 7 ^ 2 * 11 * 13 * 17 * 19 * 23 * 29 * 31 ∧
      (37 * 41 * 43 * 47 : ℕ) = 3065857 ∧
      witnessM = witnessN * (37 * 41 * 43 * 47) ∧
      (1 + 1 / (37 : ℝ)) * (1 + 1 / 41) * (1 + 1 / 43) * (1 + 1 / 47) =
        3370752 / 3065857 ∧
      (∀ p ∈ ({37, 41, 43, 47} : Finset ℕ), p.Prime ∧ ¬p ∣ witnessN) ∧
      0 < robinLogMargin witnessM ∧
      robinLogMargin witnessM < robinLogMargin witnessN := by
  obtain ⟨z, α, β, hz, hzl, hhalf, hroot, hu, hz34, hz35, hfloor, hsupp, hgap, h31, h37⟩ :=
    same_cutoff_gap
  obtain ⟨hfac, hlarge, hbase, hprod, hM, hgain, hfresh⟩ := exact_products
  have hb : OwnClockInventorySingletons witnessN z α β := {
    large := hlarge
    base := hbase
    clock := positive_clock
    log_factorization := Real.log_nat_eq_sum_factorization witnessN
    price_positive := price_positive
    below_boundary := below_boundary
    optimal := own_optimal
    unique := strict_optimizer
    strict_inventory := strict_identity
    maximal_inventory := maximal_identity
    layers := fun p k hp hk => all_layers hp hk
    no_ties := no_ties
    cutoff_large := hz
    half_shift_lower := hzl
    half_shift_upper := hhalf
    root := hroot
    cutoff_unique := hu
    support := hsupp
    gap := hgap
    positive_margin := original_margins.1
    deletion := deletion_comparisons
    insertion := insertion_comparisons }
  exact ⟨z, α, β, hb, hz34, hz35, hfloor, h31, h37, hfac, hprod, hM, hgain, hfresh,
    original_margins.2.1, original_margins.2.2⟩

/-- Full inventory and every actual prime singleton comparison do not imply
all collective fresh-prime comparisons for the original Robin margin. -/
theorem result : ¬ inventory_singletons_imply_collective := by
  intro h
  obtain ⟨z, α, β, hb, _, _, _, _, _, _, _, hM, _, hfresh, _, himprove⟩ := actual_witness
  have hcomp := h witnessN z α β hb {37, 41, 43, 47} hfresh
  have hprod : (∏ p ∈ ({37, 41, 43, 47} : Finset ℕ), p) = 37 * 41 * 43 * 47 := by norm_num
  rw [hprod, ← hM] at hcomp
  exact (not_lt_of_ge hcomp) himprove

#print axioms actual_witness
#print axioms result

end D5.S3.Arith.Robin.PriceRecord.ActualInventoryCollectiveSeparation
