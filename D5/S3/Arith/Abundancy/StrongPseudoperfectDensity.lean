/- GID: D5/S3/Arith/Abundancy/StrongPseudoperfectDensity
   generality: G
   mirror-B: D5/B/S3/Arith/Abundancy/StrongPseudoperfectDensity
   mirror-E: none(waiver:analytic-estimate)
   anchors: [mathlib/module/Mathlib.NumberTheory.EulerProduct.Basic]
   utility: none
   digest: Complementary divisor subsets encode prime extensions. -/

import D5.S3.PrimeGaps.SmoothCovers
import Mathlib.Data.Finset.NatDivisors
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.PSeries
import Mathlib.Tactic

/-!
The target is McCormack--Zelinsky Question 43.
Admission basis: open-problem-resolution; utility: none.
Positivity follows the source's positive-integer convention.

Direct frozen dependencies:
* D5/S3/PrimeGaps/SmoothCovers.smooth_count_rankin
* D5/S3/PrimeGaps/SmoothCovers.eulerProduct_left_bound
* D5/S3/PrimeGaps/EulerProducts.eulerProduct_one_le

Declaration proof shapes and live consumers:
* complement_mem: bind-only; divisor_subset_decomposition.
* complement_twice: bind-only; divisor_subset_decomposition, divisor_subset_sum.
* complement_formula: bind-only; divisor_subset_decomposition, divisor_subset_sum.
* divisor_split: bind-only; divisor_subset_decomposition.
* divisor_subset_decomposition: bind-only; divisor_subset_sum.
* divisor_subset_sum: bind-only; prime_mem_codes.
* prime_mem_codes: bind-only; prime_fiber_card.
* prime_fiber_card: bind-only; extension_count_bound.
* omegaWeight_nonneg: bind-only; omegaWeight_prefix_le_product, count_envelope.
* omegaWeight_prefix_le_product: bind-only; omega_moment_bound.
* omega_local_square_bound: bind-only; omega_product_square_bound.
* correction_product_le: bind-only; omega_product_square_bound.
* omega_product_square_bound: bind-only; omega_moment_bound.
* eulerProduct_le_log: bind-only; omega_moment_bound.
* omega_moment_bound: bind-only; result.
* divisor_card_le_omega: bind-only; divisor_rpow_le_omega.
* divisor_rpow_le_omega: bind-only; bad_harmonic_bound.
* bad_harmonic_bound: bind-only; extension_count_bound.
* smooth_count_bound: bind-only; count_envelope.
* squareExceptions_bound: bind-only; count_envelope.
* four_class_count: bind-only; count_envelope.
* power_exp_limit: bind-only; envelope_limit.
* good_fiber_limit: bind-only; envelope_limit.
* envelope_limit: bind-only; result.
* extension_count_bound: bind-only; count_envelope.
* count_envelope: bind-only; result.
* result: bind-only; the named external open-problem resolution.
Definitions are the source predicate, its count, and private objects used by these proofs.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open Finset Real Filter
open LongGapsBetweenPrimes (eulerProduct eulerProduct_pos)
open scoped BigOperators Topology

namespace D5.S3.Arith.Abundancy.StrongPseudoperfectDensity

attribute [local instance] Classical.propDecidable

/-- A positive integer with a complementary-divisor-closed sum equal to twice itself. -/
def StronglyPseudoperfect (n : ℕ) : Prop :=
  0 < n ∧ ∃ S : Finset ℕ, S ⊆ n.divisors ∧
    (∀ d ∈ n.divisors, d ∈ S ↔ n / d ∈ S) ∧ ∑ d ∈ S, d = 2 * n

/-- The positive strongly pseudoperfect integers up to the given bound. -/
def spCount (X : ℕ) : ℕ := by
  classical
  exact ((Icc 1 X).filter StronglyPseudoperfect).card

private lemma complement_mem {n d : ℕ} (hd : d ∈ n.divisors) :
    n / d ∈ n.divisors := by
  obtain ⟨hd, hn⟩ := Nat.mem_divisors.mp hd
  exact Nat.mem_divisors.mpr ⟨Nat.div_dvd_of_dvd hd, hn⟩

private lemma complement_twice {n d : ℕ} (hd : d ∈ n.divisors) :
    n / (n / d) = d := by
  obtain ⟨hd, hn⟩ := Nat.mem_divisors.mp hd
  exact Nat.div_div_self hd hn

private lemma complement_formula {m d : ℕ} (hd : d ∣ m) (q : ℕ) :
    m * q / d = q * (m / d) := by
  rw [Nat.mul_comm m q, Nat.mul_div_assoc q hd]

private lemma divisor_split {m q d : ℕ} (hq : q.Prime)
    (hd : d ∈ (m * q).divisors) :
    d ∈ m.divisors ∨ ∃ e ∈ m.divisors, d = e * q := by
  rw [Nat.divisors_mul] at hd
  obtain ⟨e, he, k, hk, rfl⟩ := Finset.mem_mul.mp hd
  rw [hq.divisors, mem_insert, mem_singleton] at hk
  rcases hk with rfl | rfl
  · exact Or.inl (by simpa using he)
  · exact Or.inr ⟨e, he, rfl⟩

private lemma divisor_subset_decomposition {m q : ℕ} (hq : q.Prime)
    {S : Finset ℕ} (hS : S ⊆ (m * q).divisors)
    (hclosed : ∀ d ∈ (m * q).divisors, d ∈ S ↔ m * q / d ∈ S) :
    S = (S ∩ m.divisors) ∪ (S ∩ m.divisors).image (fun d => m * q / d) := by
  classical
  apply Finset.ext
  intro d
  constructor
  · intro hd
    rcases divisor_split hq (hS hd) with hdm | ⟨e, he, rfl⟩
    · exact mem_union_left _ (mem_inter.mpr ⟨hd, hdm⟩)
    · apply mem_union_right
      refine mem_image.mpr ⟨m / e, mem_inter.mpr ⟨?_, complement_mem he⟩, ?_⟩
      · have h := (hclosed (e * q) (hS hd)).mp hd
        simpa only [Nat.mul_div_mul_right _ _ hq.pos] using h
      · rw [complement_formula (Nat.div_dvd_of_dvd (Nat.dvd_of_mem_divisors he)),
          complement_twice he, Nat.mul_comm]
  · intro hd
    rcases mem_union.mp hd with hd | hd
    · exact (mem_inter.mp hd).1
    · obtain ⟨e, he, rfl⟩ := mem_image.mp hd
      exact (hclosed e (hS (mem_inter.mp he).1)).mp (mem_inter.mp he).1

private lemma divisor_subset_sum {m q : ℕ} (hq : q.Prime) (hqm : ¬ q ∣ m)
    {S : Finset ℕ} (hS : S ⊆ (m * q).divisors)
    (hclosed : ∀ d ∈ (m * q).divisors, d ∈ S ↔ m * q / d ∈ S) :
    (∑ d ∈ S, d) = (∑ d ∈ S ∩ m.divisors, d) +
      q * ∑ d ∈ S ∩ m.divisors, m / d := by
  classical
  let T := S ∩ m.divisors
  have hdis : Disjoint T (T.image (fun d => m * q / d)) := by
    apply disjoint_left.mpr
    intro d hd hi
    obtain ⟨e, he, rfl⟩ := mem_image.mp hi
    have hed := Nat.dvd_of_mem_divisors (mem_inter.mp he).2
    have hdd := Nat.dvd_of_mem_divisors (mem_inter.mp hd).2
    rw [complement_formula hed] at hdd
    exact hqm (dvd_trans (dvd_mul_right q (m / e)) hdd)
  have hinj : Set.InjOn (fun d => m * q / d) ↑T := by
    intro d hd e he hde
    have hdS := hS (mem_inter.mp hd).1
    have heS := hS (mem_inter.mp he).1
    simpa only [complement_twice hdS, complement_twice heS] using
      congrArg (fun k => m * q / k) hde
  calc
    _ = (∑ d ∈ T, d) + ∑ d ∈ T.image (fun d => m * q / d), d := by
      rw [divisor_subset_decomposition hq hS hclosed, sum_union hdis]
    _ = (∑ d ∈ T, d) + ∑ d ∈ T, q * (m / d) := by
      rw [sum_image hinj]
      congr 1
      apply sum_congr rfl
      intro d hd
      exact complement_formula (Nat.dvd_of_mem_divisors (mem_inter.mp hd).2) q
    _ = _ := by rw [mul_sum]

private def primeCodes (m : ℕ) : Finset ℕ := by
  classical
  exact m.divisors.powerset.image
    (fun T => (∑ d ∈ T, d) / (2 * m - ∑ d ∈ T, m / d))

private lemma prime_mem_codes {m q : ℕ} (hq : q.Prime) (hqm : ¬ q ∣ m)
    (hsp : StronglyPseudoperfect (m * q)) : q ∈ primeCodes m := by
  classical
  obtain ⟨hmq, S, hS, hclosed, hsum⟩ := hsp
  let T := S ∩ m.divisors
  let A := ∑ d ∈ T, d
  let B := ∑ d ∈ T, m / d
  have heq : A + q * B = 2 * (m * q) :=
    (divisor_subset_sum hq hqm hS hclosed).symm.trans hsum
  have hA : 0 < A := by
    by_contra! h
    have hT : T = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro d hd
      have hd0 := Nat.pos_of_mem_divisors (mem_inter.mp hd).2
      have hdA : d ≤ A := single_le_sum (f := fun d : ℕ => d) (fun _ _ => Nat.zero_le _) hd
      omega
    have hB : B = 0 := by simp [B, hT]
    rw [hB, mul_zero, add_zero] at heq
    omega
  have hB : B < 2 * m := by
    by_contra! h
    have hh := Nat.mul_le_mul_left q h
    nlinarith
  have hcode : q * (2 * m - B) = A := by
    have hh := Nat.sub_add_cancel hB.le
    nlinarith
  apply mem_image.mpr
  refine ⟨T, mem_powerset.mpr (inter_subset_right), ?_⟩
  change A / (2 * m - B) = q
  rw [← hcode, Nat.mul_div_cancel _ (Nat.sub_pos_of_lt hB)]

private lemma prime_fiber_card (m Q : ℕ) :
    ((Icc 1 Q).filter (fun q : ℕ => q.Prime ∧ ¬ q ∣ m ∧
      StronglyPseudoperfect (m * q))).card ≤ 2 ^ m.divisors.card := by
  classical
  calc
    _ ≤ (primeCodes m).card := card_le_card (by
      intro q hq
      obtain ⟨_, hp, hm, hs⟩ := mem_filter.mp hq
      exact prime_mem_codes hp hm hs)
    _ ≤ m.divisors.powerset.card := card_image_le
    _ = _ := card_powerset _

private def omegaWeight (n : ℕ) : ℝ :=
  (3 / 2 : ℝ) ^ ArithmeticFunction.cardFactors n / n

private lemma omegaWeight_nonneg (n : ℕ) : 0 ≤ omegaWeight n := by
  unfold omegaWeight
  positivity

private def omegaHom : ℕ →* ℝ where
  toFun := omegaWeight
  map_one' := by simp [omegaWeight]
  map_mul' m n := by
    by_cases hm : m = 0
    · simp [hm, omegaWeight]
    by_cases hn : n = 0
    · simp [hn, omegaWeight]
    simp only [omegaWeight, ArithmeticFunction.cardFactors_mul hm hn, pow_add,
      Nat.cast_mul, mul_div_mul_comm]

private lemma omegaWeight_prefix_le_product (N : ℕ) :
    (∑ n ∈ Icc 1 N, omegaWeight n) ≤
      ∏ p ∈ N.primesLE, (1 - (3 / 2 : ℝ) / p)⁻¹ := by
  have hprime {p : ℕ} (hp : p.Prime) : ‖omegaHom p‖ < 1 := by
    have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    change ‖(3 / 2 : ℝ) ^ ArithmeticFunction.cardFactors p / p‖ < 1
    rw [ArithmeticFunction.cardFactors_apply_prime hp, pow_one,
      Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact (div_lt_one (by linarith)).mpr (by linarith)
  have hs := (EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_geometric
    hprime (N + 1)).2
  have hmem (n : ℕ) (hn : n ∈ Icc 1 N) : n ∈ (N + 1).smoothNumbers := by
    obtain ⟨hn0, hnN⟩ := mem_Icc.mp hn
    exact Nat.mem_smoothNumbers_of_lt (by omega) (by omega)
  rw [← Finset.sum_subtype_of_mem _ hmem]
  refine (sum_le_hasSum _
    (fun (n : (N + 1).smoothNumbers) _ => omegaWeight_nonneg n) hs).trans_eq ?_
  apply prod_congr rfl
  intro p hp
  simp [omegaHom, omegaWeight, (Nat.mem_primesLE.mp hp).2]

private lemma omega_local_square_bound {p : ℝ} (hp : 2 ≤ p) :
    ((1 - (3 / 2 : ℝ) / p)⁻¹) ^ 2 ≤
      ((1 - 1 / p)⁻¹) ^ 3 * (1 + 4 / p ^ 2) := by
  have hp0 : 0 < p := by linarith
  have ht0 : 0 ≤ 1 / p := by positivity
  have ht : 1 / p ≤ (1 / 2 : ℝ) := by
    exact (div_le_div_iff₀ hp0 (by norm_num)).mpr (by linarith)
  have hu : 0 < 1 - 1 / p := by linarith
  have hv : 0 < 1 - (3 / 2 : ℝ) / p := by
    rw [div_eq_mul_one_div]
    linarith
  have hc : (1 - 1 / p) ^ 3 ≤
      (1 - (3 / 2 : ℝ) / p) ^ 2 * (1 + 4 / p ^ 2) := by
    have hprod := mul_nonneg
      (mul_nonneg (by linarith : 0 ≤ 1 - 2 * (1 / p))
        (by linarith : 0 ≤ 13 - 18 * (1 / p))) (sq_nonneg (1 / p))
    have heq : 4 / p ^ 2 = 4 * (1 / p) ^ 2 := by ring
    rw [heq, show (3 / 2 : ℝ) / p = (3 / 2 : ℝ) * (1 / p) by ring]
    nlinarith [hprod]
  rw [inv_pow, inv_pow, inv_mul_eq_div, ← one_div]
  apply (div_le_div_iff₀ (pow_pos hv 2) (pow_pos hu 3)).mpr
  nlinarith [hc]

private def correctionConstant : ℝ := exp (∑' n : ℕ, 4 / (n : ℝ) ^ 2)

private lemma correction_product_le (P : Finset ℕ) :
    (∏ p ∈ P, (1 + 4 / (p : ℝ) ^ 2)) ≤ correctionConstant := by
  have hs : Summable (fun n : ℕ => 4 / (n : ℝ) ^ 2) := by
    convert (Real.summable_nat_rpow.mpr (by norm_num : (-2 : ℝ) < -1)).mul_left
      (4 : ℝ) using 1
    ext n
    simp [Real.rpow_neg, Real.rpow_two, div_eq_mul_inv]
  calc
    _ ≤ ∏ p ∈ P, exp (4 / (p : ℝ) ^ 2) := by
      apply Finset.prod_le_prod₀
      · intro p hp
        positivity
      · intro p hp
        simpa [add_comm] using add_one_le_exp (4 / (p : ℝ) ^ 2)
    _ = exp (∑ p ∈ P, 4 / (p : ℝ) ^ 2) := (exp_sum _ _).symm
    _ ≤ correctionConstant := by
      apply exp_le_exp.mpr
      exact hs.sum_le_tsum P (fun n hn => by positivity)

private lemma omega_product_square_bound (N : ℕ) :
    (∏ p ∈ N.primesLE, (1 - (3 / 2 : ℝ) / p)⁻¹) ^ 2 ≤
      eulerProduct N 1 ^ 3 * correctionConstant := by
  calc
    _ = ∏ p ∈ N.primesLE, ((1 - (3 / 2 : ℝ) / p)⁻¹) ^ 2 :=
      (prod_pow _ _ _).symm
    _ ≤ ∏ p ∈ N.primesLE,
        ((1 - (1 : ℝ) / p)⁻¹) ^ 3 * (1 + 4 / (p : ℝ) ^ 2) := by
      apply Finset.prod_le_prod₀
      · intro p hp
        positivity
      · intro p hp
        apply omega_local_square_bound
        exact_mod_cast (Nat.mem_primesLE.mp hp).2.two_le
    _ = eulerProduct N 1 ^ 3 *
        ∏ p ∈ N.primesLE, (1 + 4 / (p : ℝ) ^ 2) := by
      rw [prod_mul_distrib, prod_pow]
      simp only [eulerProduct, rpow_neg_one, one_div]
    _ ≤ eulerProduct N 1 ^ 3 * correctionConstant :=
      mul_le_mul_of_nonneg_left (correction_product_le _) (by
        exact pow_nonneg ((eulerProduct_pos N (by norm_num)).le) _)

private lemma eulerProduct_le_log {N : ℕ} (hN : 3 ≤ N) :
    eulerProduct N 1 ≤ (2 * exp 6) * log N := by
  have hNR : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hL : 1 ≤ log (N : ℝ) := by
    apply (le_log_iff_exp_le (by linarith)).mpr
    exact exp_one_lt_three.le.trans hNR
  have h := LongGapsBetweenPrimes.eulerProduct_one_le (by omega : 2 ≤ N)
  nlinarith [exp_pos (6 : ℝ)]

private lemma omega_moment_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 3 ≤ N →
      (∑ n ∈ Icc 1 N, omegaWeight n) ≤ C * (log N) ^ (3 / 2 : ℝ) := by
  let K := 2 * exp (6 : ℝ)
  let C := Real.sqrt (K ^ 3 * correctionConstant)
  have hK : 0 < K := by dsimp [K]; positivity
  have hcor : 0 < correctionConstant := exp_pos _
  have hC : 0 < C := Real.sqrt_pos.mpr (mul_pos (pow_pos hK _) hcor)
  refine ⟨C, hC, fun N hN => ?_⟩
  have hNR : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hL : 0 < log (N : ℝ) := log_pos (by linarith)
  have hsum0 : 0 ≤ ∑ n ∈ Icc 1 N, omegaWeight n :=
    sum_nonneg (fun n hn => omegaWeight_nonneg n)
  have hsum := omegaWeight_prefix_le_product N
  have hprod := omega_product_square_bound N
  have hM := eulerProduct_le_log hN
  have hsq : (∑ n ∈ Icc 1 N, omegaWeight n) ^ 2 ≤
      K ^ 3 * correctionConstant * (log N) ^ 3 := by
    calc
      _ ≤ (∏ p ∈ N.primesLE, (1 - (3 / 2 : ℝ) / p)⁻¹) ^ 2 :=
        pow_le_pow_left₀ hsum0 hsum 2
      _ ≤ eulerProduct N 1 ^ 3 * correctionConstant := hprod
      _ ≤ (K * log N) ^ 3 * correctionConstant :=
        mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ ((eulerProduct_pos N (by norm_num)).le) hM 3) hcor.le
      _ = _ := by ring
  have hCp : C ^ 2 = K ^ 3 * correctionConstant :=
    Real.sq_sqrt (mul_nonneg (pow_nonneg hK.le _) hcor.le)
  have hLp : ((log (N : ℝ)) ^ (3 / 2 : ℝ)) ^ 2 = (log N) ^ 3 := by
    rw [← Real.rpow_mul_natCast hL.le]
    norm_num
  have hpos : 0 ≤ C * (log N) ^ (3 / 2 : ℝ) := by positivity
  have htarget : (C * (log N) ^ (3 / 2 : ℝ)) ^ 2 =
      K ^ 3 * correctionConstant * (log N) ^ 3 := by
    rw [mul_pow, hCp, hLp]
  nlinarith [sq_nonneg (C * (log N) ^ (3 / 2 : ℝ) -
    (∑ n ∈ Icc 1 N, omegaWeight n))]

private lemma divisor_card_le_omega {n : ℕ} (hn : n ≠ 0) :
    n.divisors.card ≤ 2 ^ ArithmeticFunction.cardFactors n := by
  rw [Nat.card_divisors hn, ArithmeticFunction.cardFactors_eq_sum_factorization,
    Finsupp.sum, Nat.support_factorization, ← prod_pow_eq_pow_sum]
  exact prod_le_prod (fun p hp => Nat.succ_le_of_lt (n.factorization p).lt_two_pow_self)

private lemma divisor_rpow_le_omega {n : ℕ} (hn : n ≠ 0) :
    (n.divisors.card : ℝ) ^ (4 / 7 : ℝ) ≤
      (3 / 2 : ℝ) ^ ArithmeticFunction.cardFactors n := by
  have h := divisor_card_le_omega hn
  have hR : (n.divisors.card : ℝ) ≤ (2 : ℝ) ^ ArithmeticFunction.cardFactors n := by
    exact_mod_cast h
  have h4 := pow_le_pow_left₀ (Nat.cast_nonneg n.divisors.card) hR 4
  have hbase : (2 : ℝ) ^ 4 ≤ (3 / 2 : ℝ) ^ 7 := by norm_num
  have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2 ^ 4) hbase
    (ArithmeticFunction.cardFactors n)
  apply (pow_le_pow_iff_left₀ (rpow_nonneg (Nat.cast_nonneg _) _)
    (by positivity : 0 ≤ (3 / 2 : ℝ) ^ ArithmeticFunction.cardFactors n)
    (by decide : 7 ≠ 0)).mp
  rw [← Real.rpow_mul_natCast (Nat.cast_nonneg _)]
  norm_num only [show (4 / 7 : ℝ) * (7 : ℕ) = 4 by norm_num, Real.rpow_natCast]
  have hp' : ((2 : ℝ) ^ ArithmeticFunction.cardFactors n) ^ 4 ≤
      ((3 / 2 : ℝ) ^ ArithmeticFunction.cardFactors n) ^ 7 := by
    calc
      _ = ((2 : ℝ) ^ 4) ^ ArithmeticFunction.cardFactors n := by
        simp only [← pow_mul, mul_comm]
      _ ≤ _ := hp
      _ = _ := by simp only [← pow_mul, mul_comm]
  simpa only [Real.rpow_ofNat] using h4.trans hp'

private lemma bad_harmonic_bound {X : ℕ} {L : ℝ} (hL : 0 < L) :
    (∑ n ∈ (Icc 1 X).filter (fun n => L ^ (15 / 16 : ℝ) < n.divisors.card),
      (1 : ℝ) / n) ≤
      L ^ (-15 / 28 : ℝ) * ∑ n ∈ Icc 1 X, omegaWeight n := by
  let S := (Icc 1 X).filter (fun n => L ^ (15 / 16 : ℝ) < n.divisors.card)
  have hpoint (n : ℕ) (hn : n ∈ S) :
      (1 : ℝ) / n ≤ L ^ (-15 / 28 : ℝ) * omegaWeight n := by
    obtain ⟨hnX, hnL⟩ := mem_filter.mp hn
    have hn0 : n ≠ 0 := by have := (mem_Icc.mp hnX).1; omega
    have ht := rpow_le_rpow (rpow_nonneg hL.le _) hnL.le (by norm_num : (0 : ℝ) ≤ 4 / 7)
    rw [← rpow_mul hL.le, show (15 / 16 : ℝ) * (4 / 7) = 15 / 28 by norm_num] at ht
    have hweight := ht.trans (divisor_rpow_le_omega hn0)
    have hmul := mul_le_mul_of_nonneg_left hweight
      (rpow_nonneg hL.le (-15 / 28))
    have hcancel : L ^ (-15 / 28 : ℝ) * L ^ (15 / 28 : ℝ) = 1 := by
      rw [← rpow_add hL]
      norm_num
    rw [hcancel] at hmul
    unfold omegaWeight
    rw [← mul_div_assoc]
    exact div_le_div_of_nonneg_right hmul (Nat.cast_nonneg n)
  calc
    _ ≤ ∑ n ∈ S, L ^ (-15 / 28 : ℝ) * omegaWeight n :=
      sum_le_sum hpoint
    _ ≤ ∑ n ∈ Icc 1 X, L ^ (-15 / 28 : ℝ) * omegaWeight n :=
      sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
        (fun n _ _ => mul_nonneg (rpow_nonneg hL.le _) (omegaWeight_nonneg n))
    _ = _ := (mul_sum _ _ _).symm

private lemma smooth_count_bound {X Y : ℕ} {z : ℝ} (hX : 0 < X)
    (hY : 2 ≤ Y) (hYz : (Y : ℝ) ≤ z) (hz : 2 ≤ log z) :
    (((Icc 1 X).filter (fun n => n ∈ (Y + 1).smoothNumbers)).card : ℝ) ≤
      X * exp (-log X / log z) *
        (exp 6 * (1 + log z) *
          exp (3 * LongGapsBetweenPrimes.smoothEulerConstant * exp 1)) := by
  classical
  have hz0 : 0 < log z := by linarith
  have ht : 0 ≤ (log z)⁻¹ := inv_nonneg.mpr hz0.le
  have ht' : (log z)⁻¹ ≤ 1 / 2 := by
    exact (inv_le_comm₀ hz0 (by norm_num)).mpr (by simpa using hz)
  have hσ : 0 < 1 - (log z)⁻¹ := by linarith
  have hX0 : (0 : ℝ) < X := by exact_mod_cast hX
  have hY0 : (0 : ℝ) < Y := by exact_mod_cast (by omega : 0 < Y)
  have hlog : log (Y : ℝ) ≤ log z := log_le_log hY0 hYz
  have hprod := LongGapsBetweenPrimes.eulerProduct_left_bound hY hYz ht ht'
  rw [inv_mul_cancel₀ (ne_of_gt hz0)] at hprod
  have hbase := LongGapsBetweenPrimes.eulerProduct_one_le hY
  have hprod' : LongGapsBetweenPrimes.eulerProduct Y (1 - (log z)⁻¹) ≤
      exp 6 * (1 + log z) *
        exp (3 * LongGapsBetweenPrimes.smoothEulerConstant * exp 1) := by
    apply hprod.trans
    apply mul_le_mul_of_nonneg_right _ (exp_pos _).le
    exact hbase.trans (mul_le_mul_of_nonneg_left
      (add_le_add le_rfl hlog) (exp_pos 6).le)
  have hr := LongGapsBetweenPrimes.smooth_count_rankin hσ
    ((Icc 1 X).filter (fun n => n ∈ (Y + 1).smoothNumbers))
    (filter_subset _ _) (fun n hn => (mem_filter.mp hn).2)
  have heq : (X : ℝ) ^ (1 - (log z)⁻¹) = X * exp (-log X / log z) := by
    rw [rpow_def_of_pos hX0]
    calc
      _ = exp (log (X : ℝ) + (-log X / log z)) := by congr 1; ring
      _ = _ := by rw [exp_add, exp_log hX0]
  rw [heq] at hr
  exact hr.trans (mul_le_mul_of_nonneg_left hprod' (by positivity))

private def squareExceptions (X Y : ℕ) : Finset ℕ := by
  classical
  exact (Ioc Y X).biUnion (fun q => (Ioc 0 X).filter (fun n => q ^ 2 ∣ n))

private lemma squareExceptions_bound (X Y : ℕ) :
    ((squareExceptions X Y).card : ℝ) ≤ 2 * (X : ℝ) / (Y + 1) := by
  classical
  have hI : Ioc Y X = Ioo Y (X + 1) := by
    ext q
    simp only [mem_Ioc, mem_Ioo]
    omega
  calc
    _ ≤ ∑ q ∈ Ioc Y X,
        (((Ioc 0 X).filter (fun n => q ^ 2 ∣ n)).card : ℝ) := by
      exact_mod_cast (card_biUnion_le (s := Ioc Y X)
        (t := fun q => (Ioc 0 X).filter (fun n => q ^ 2 ∣ n)))
    _ = ∑ q ∈ Ioc Y X, ((X / q ^ 2 : ℕ) : ℝ) := by
      simp only [Nat.Ioc_filter_dvd_card_eq_div]
    _ ≤ ∑ q ∈ Ioc Y X, (X : ℝ) / (q : ℝ) ^ 2 := by
      apply sum_le_sum
      intro q hq
      simpa only [Nat.cast_pow] using
        (Nat.cast_div_le (m := X) (n := q ^ 2) :
          ((X / q ^ 2 : ℕ) : ℝ) ≤ (X : ℝ) / (q ^ 2 : ℕ))
    _ = (X : ℝ) * ∑ q ∈ Ioo Y (X + 1), ((q : ℝ) ^ 2)⁻¹ := by
      rw [hI, mul_sum]
      simp only [div_eq_mul_inv]
    _ ≤ (X : ℝ) * (2 / (Y + 1)) :=
      mul_le_mul_of_nonneg_left (sum_Ioo_inv_sq_le Y (X + 1)) (Nat.cast_nonneg X)
    _ = _ := by ring

private def extensionPrimes (m Q : ℕ) : Finset ℕ := by
  classical
  exact (Icc 1 Q).filter (fun q => q.Prime ∧ ¬ q ∣ m ∧
    StronglyPseudoperfect (m * q))

private def extensionSet (X M : ℕ) : Finset ℕ := by
  classical
  exact (Icc 1 M).biUnion (fun m =>
    (extensionPrimes m (X / m)).image (fun q => m * q))

private lemma four_class_count (X Y : ℕ) :
    spCount X ≤ ((Icc 1 X).filter (fun n => n ∈ (Y + 1).smoothNumbers)).card +
      (squareExceptions X Y).card +
      ∑ m ∈ Icc 1 (X / (Y + 1)), (extensionPrimes m (X / m)).card := by
  classical
  let A := (Icc 1 X).filter (fun n => n ∈ (Y + 1).smoothNumbers)
  have hcover : (Icc 1 X).filter StronglyPseudoperfect ⊆
      (A ∪ squareExceptions X Y) ∪ extensionSet X (X / (Y + 1)) := by
    intro n hn
    obtain ⟨hnX, hsp⟩ := mem_filter.mp hn
    obtain ⟨hn1, hnX⟩ := mem_Icc.mp hnX
    by_cases hsm : n ∈ (Y + 1).smoothNumbers
    · exact mem_union_left _ (mem_union_left _
        (mem_filter.mpr ⟨mem_Icc.mpr ⟨hn1, hnX⟩, hsm⟩))
    have hns : ¬ ∀ q, q.Prime → q ∣ n → q < Y + 1 :=
      fun h => hsm (Nat.mem_smoothNumbers'.mpr h)
    push_neg at hns
    obtain ⟨q, hq, hqn, hYq⟩ := hns
    have hqX : q ≤ X := (Nat.le_of_dvd (by omega : 0 < n) hqn).trans hnX
    by_cases hs : q ^ 2 ∣ n
    · apply mem_union_left
      apply mem_union_right
      exact mem_biUnion.mpr ⟨q, mem_Ioc.mpr ⟨by omega, hqX⟩,
        mem_filter.mpr ⟨mem_Ioc.mpr ⟨by omega, hnX⟩, hs⟩⟩
    let m := n / q
    have hmul : m * q = n := Nat.div_mul_cancel hqn
    have hm0 : 0 < m := Nat.div_pos (Nat.le_of_dvd (by omega) hqn) hq.pos
    have hmM : m ≤ X / (Y + 1) := by
      apply (Nat.le_div_iff_mul_le (Nat.succ_pos Y)).mpr
      calc
        m * (Y + 1) ≤ m * q := Nat.mul_le_mul_left m hYq
        _ = n := hmul
        _ ≤ X := hnX
    have hqQ : q ≤ X / m := by
      apply (Nat.le_div_iff_mul_le hm0).mpr
      nlinarith [hmul]
    have hqm : ¬ q ∣ m := by
      intro hd
      apply hs
      simpa only [pow_two] using (Nat.dvd_div_iff_mul_dvd hqn).mp hd
    apply mem_union_right
    apply mem_biUnion.mpr
    refine ⟨m, mem_Icc.mpr ⟨hm0, hmM⟩, mem_image.mpr ⟨q, ?_, hmul⟩⟩
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨hq.one_le, hqQ⟩, hq, hqm,
      by simpa only [hmul] using hsp⟩
  calc
    spCount X ≤ ((A ∪ squareExceptions X Y) ∪
        extensionSet X (X / (Y + 1))).card := card_le_card hcover
    _ ≤ (A ∪ squareExceptions X Y).card +
        (extensionSet X (X / (Y + 1))).card := card_union_le _ _
    _ ≤ _ := add_le_add (card_union_le _ _) (card_biUnion_le.trans
      (sum_le_sum (fun m hm => card_image_le)))

private lemma power_exp_limit (c d : ℝ) (hd : 0 < d) :
    Tendsto (fun L : ℝ => L ^ c * exp (-(L ^ d))) atTop (𝓝 0) := by
  have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (c / d) 1
    (by norm_num)).comp (tendsto_rpow_atTop hd)
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL
  simp only [Function.comp_apply, neg_one_mul, ← rpow_mul hL.le]
  congr 2
  field_simp

private lemma good_fiber_limit :
    Tendsto (fun L : ℝ => exp (log 2 * L ^ (15 / 16 : ℝ) -
      L ^ (31 / 32 : ℝ))) atTop (𝓝 0) := by
  have hr : Tendsto (fun L : ℝ => log 2 * L ^ (-1 / 32 : ℝ)) atTop (𝓝 0) := by
    convert (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 32)).const_mul
      (log 2) using 1 <;> norm_num
  have he : Tendsto (fun L : ℝ => exp (-(1 / 2 : ℝ) * L ^ (31 / 32 : ℝ)))
      atTop (𝓝 0) := tendsto_exp_atBot.comp
    ((tendsto_const_mul_atBot_of_neg (by norm_num : -(1 / 2 : ℝ) < 0)).mpr
      (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 31 / 32)))
  apply squeeze_zero' (Eventually.of_forall (fun L => (exp_pos _).le)) ?_ he
  filter_upwards [eventually_gt_atTop (0 : ℝ), hr.eventually
    (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))] with L hL hrL
  apply exp_le_exp.mpr
  have hp : L ^ (15 / 16 : ℝ) = L ^ (-1 / 32 : ℝ) *
      L ^ (31 / 32 : ℝ) := by
    rw [← rpow_add hL]
    norm_num
  rw [hp]
  nlinarith [mul_le_mul_of_nonneg_right hrL.le
    (rpow_nonneg hL.le (31 / 32 : ℝ))]

private def smoothConstant : ℝ := exp 6 *
  exp (3 * LongGapsBetweenPrimes.smoothEulerConstant * exp 1)

private def densityEnvelope (C D L : ℝ) : ℝ :=
  smoothConstant * (1 + L ^ (31 / 32 : ℝ)) * exp (-(L ^ (1 / 32 : ℝ))) +
    2 * exp (-(L ^ (31 / 32 : ℝ))) +
    exp (log 2 * L ^ (15 / 16 : ℝ) - L ^ (31 / 32 : ℝ)) +
    C * D * L ^ (-1 / 224 : ℝ)

private lemma envelope_limit (C D : ℝ) :
    Tendsto (densityEnvelope C D) atTop (𝓝 0) := by
  have hs := ((power_exp_limit 0 (1 / 32) (by norm_num)).add
    (power_exp_limit (31 / 32) (1 / 32) (by norm_num))).const_mul smoothConstant
  have he := (power_exp_limit 0 (31 / 32) (by norm_num)).const_mul 2
  have hb := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 224)).const_mul
    (C * D)
  convert ((hs.add he).add good_fiber_limit).add hb using 1
  · ext L
    dsimp [densityEnvelope]
    norm_num
    ring
  · norm_num

private lemma extension_count_bound (X Y : ℕ) (L C : ℝ)
    (hL : 0 < L) (hY : 1 ≤ Y) (hC : 0 ≤ C)
    (hprime : ∀ t : ℝ, (Y : ℝ) + 1 ≤ t →
      (Nat.primeCounting ⌊t⌋₊ : ℝ) ≤ C * t / log t) :
    (∑ m ∈ Icc 1 (X / (Y + 1)),
      ((extensionPrimes m (X / m)).card : ℝ)) ≤
      ((X : ℝ) / (Y + 1)) * (2 : ℝ) ^ (L ^ (15 / 16 : ℝ)) +
      (C * X / log (Y + 1)) * L ^ (-15 / 28 : ℝ) *
        ∑ m ∈ Icc 1 X, omegaWeight m := by
  classical
  let M := X / (Y + 1)
  let A := (2 : ℝ) ^ (L ^ (15 / 16 : ℝ))
  let B := C * X / log ((Y : ℝ) + 1)
  have hA : 0 ≤ A := rpow_nonneg (by norm_num) _
  have hlog : 0 < log ((Y : ℝ) + 1) := log_pos (by exact_mod_cast (by omega : 1 < Y + 1))
  have hB : 0 ≤ B := div_nonneg (mul_nonneg hC (Nat.cast_nonneg X)) hlog.le
  have hpoint (m : ℕ) (hm : m ∈ Icc 1 M) :
      ((extensionPrimes m (X / m)).card : ℝ) ≤
        A + if L ^ (15 / 16 : ℝ) < m.divisors.card then B * (1 / m) else 0 := by
    have hm0 : 0 < m := (mem_Icc.mp hm).1
    have hmR : (0 : ℝ) < m := by exact_mod_cast hm0
    by_cases hbad : L ^ (15 / 16 : ℝ) < m.divisors.card
    · rw [if_pos hbad]
      have hmt : m * (Y + 1) ≤ X :=
        (Nat.le_div_iff_mul_le (Nat.succ_pos Y)).mp (mem_Icc.mp hm).2
      have ht : (Y : ℝ) + 1 ≤ (X : ℝ) / m := by
        apply (le_div_iff₀ hmR).mpr
        exact_mod_cast (by simpa [Nat.mul_comm] using hmt : (Y + 1) * m ≤ X)
      have hc : (extensionPrimes m (X / m)).card ≤ Nat.primeCounting (X / m) := by
        rw [← Nat.primesLE_card_eq_primeCounting]
        apply card_le_card
        intro q hq
        obtain ⟨hqQ, hp, _⟩ := mem_filter.mp hq
        exact Nat.mem_primesLE.mpr ⟨(mem_Icc.mp hqQ).2, hp⟩
      have hcount : ((extensionPrimes m (X / m)).card : ℝ) ≤
          C * ((X : ℝ) / m) / log ((X : ℝ) / m) := by
        apply (show ((extensionPrimes m (X / m)).card : ℝ) ≤
          Nat.primeCounting (X / m) by exact_mod_cast hc).trans
        simpa only [Nat.floor_div_eq_div] using hprime ((X : ℝ) / m) ht
      have hden := log_le_log (by positivity : (0 : ℝ) < (Y : ℝ) + 1) ht
      calc
        _ ≤ C * ((X : ℝ) / m) / log ((X : ℝ) / m) := hcount
        _ ≤ C * ((X : ℝ) / m) / log ((Y : ℝ) + 1) :=
          div_le_div_of_nonneg_left
            (mul_nonneg hC (div_nonneg (Nat.cast_nonneg X) hmR.le)) hlog hden
        _ = B * (1 / m) := by dsimp [B]; ring
        _ ≤ A + B * (1 / m) := le_add_of_nonneg_left hA
    · rw [if_neg hbad, add_zero]
      have hc : ((extensionPrimes m (X / m)).card : ℝ) ≤
          (2 : ℝ) ^ m.divisors.card := by
        exact_mod_cast prime_fiber_card m (X / m)
      apply hc.trans
      rw [← rpow_natCast]
      exact rpow_le_rpow_of_exponent_le (by norm_num) (le_of_not_gt hbad)
  have hsum : (∑ m ∈ Icc 1 M, ((extensionPrimes m (X / m)).card : ℝ)) ≤
      (M : ℝ) * A + B *
        ∑ m ∈ (Icc 1 M).filter (fun m => L ^ (15 / 16 : ℝ) < m.divisors.card),
          (1 : ℝ) / m := by
    calc
      _ ≤ ∑ m ∈ Icc 1 M,
          (A + if L ^ (15 / 16 : ℝ) < m.divisors.card then B * (1 / m) else 0) :=
        sum_le_sum hpoint
      _ = _ := by
        rw [sum_add_distrib, sum_ite]
        simp [← mul_sum, nsmul_eq_mul]
  have hMX : M ≤ X := Nat.div_le_self X (Y + 1)
  have hbad : (∑ m ∈ (Icc 1 M).filter
      (fun m => L ^ (15 / 16 : ℝ) < m.divisors.card), (1 : ℝ) / m) ≤
      L ^ (-15 / 28 : ℝ) * ∑ m ∈ Icc 1 X, omegaWeight m := by
    apply le_trans _ (bad_harmonic_bound hL)
    apply sum_le_sum_of_subset_of_nonneg
    · intro m hm
      obtain ⟨hmM, hb⟩ := mem_filter.mp hm
      exact mem_filter.mpr ⟨mem_Icc.mpr
        ⟨(mem_Icc.mp hmM).1, (mem_Icc.mp hmM).2.trans hMX⟩, hb⟩
    · intro m hm hmn
      positivity
  apply hsum.trans
  have hM : (M : ℝ) ≤ (X : ℝ) / (Y + 1) := by
    simpa only [M, Nat.cast_add, Nat.cast_one] using
      (Nat.cast_div_le (m := X) (n := Y + 1) :
        ((X / (Y + 1) : ℕ) : ℝ) ≤ (X : ℝ) / (Y + 1 : ℕ))
  simpa only [A, B, mul_assoc] using
    add_le_add (mul_le_mul_of_nonneg_right hM hA)
      (mul_le_mul_of_nonneg_left hbad hB)

private lemma count_envelope {X : ℕ} {C D : ℝ} (hX : 3 ≤ X)
    (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hscale : 2 ≤ (log (X : ℝ)) ^ (31 / 32 : ℝ))
    (hY : 2 ≤ ⌊exp ((log (X : ℝ)) ^ (31 / 32 : ℝ))⌋₊)
    (hmoment : (∑ n ∈ Icc 1 X, omegaWeight n) ≤
      D * (log X) ^ (3 / 2 : ℝ))
    (hprime : ∀ t : ℝ,
      (⌊exp ((log (X : ℝ)) ^ (31 / 32 : ℝ))⌋₊ : ℝ) + 1 ≤ t →
      (Nat.primeCounting ⌊t⌋₊ : ℝ) ≤ C * t / log t) :
    (spCount X : ℝ) / X ≤ densityEnvelope C D (log X) := by
  classical
  let L := log (X : ℝ)
  let z := exp (L ^ (31 / 32 : ℝ))
  let Y := ⌊z⌋₊
  have hX0 : (0 : ℝ) < X := by exact_mod_cast (by omega : 0 < X)
  have hL : 0 < L := log_pos (by exact_mod_cast (by omega : 1 < X))
  have hz : 0 < z := exp_pos _
  have hYz : (Y : ℝ) ≤ z := Nat.floor_le hz.le
  have hzY : z ≤ (Y : ℝ) + 1 := (Nat.lt_floor_add_one z).le
  have hlogz : log z = L ^ (31 / 32 : ℝ) := log_exp _
  have hlogY : L ^ (31 / 32 : ℝ) ≤ log ((Y : ℝ) + 1) := by
    rw [← hlogz]
    exact log_le_log hz hzY
  have hpow : L / L ^ (31 / 32 : ℝ) = L ^ (1 / 32 : ℝ) := by
    calc
      _ = L ^ (1 : ℝ) / L ^ (31 / 32 : ℝ) := by rw [rpow_one]
      _ = _ := by rw [← rpow_sub hL]; norm_num
  have hY' : 2 ≤ Y := hY
  have hsm := smooth_count_bound (Y := Y) (z := z) (by omega : 0 < X) hY' hYz
    (by simpa [hlogz] using hscale)
  have hsq := squareExceptions_bound X Y
  have hext := extension_count_bound X Y L C hL (by omega) hC hprime
  have hsm' : (((Icc 1 X).filter
      (fun n => n ∈ (Y + 1).smoothNumbers)).card : ℝ) ≤
      X * (smoothConstant * (1 + L ^ (31 / 32 : ℝ)) *
        exp (-(L ^ (1 / 32 : ℝ)))) := by
    have harg : -log (X : ℝ) / log z = -(L ^ (1 / 32 : ℝ)) := by
      change -L / log z = _
      rw [hlogz, neg_div, hpow]
    rw [harg, hlogz] at hsm
    simpa only [smoothConstant, mul_assoc, mul_comm, mul_left_comm] using hsm
  have hsq' : ((squareExceptions X Y).card : ℝ) ≤
      X * (2 * exp (-(L ^ (31 / 32 : ℝ)))) := by
    apply hsq.trans
    calc
      _ ≤ 2 * (X : ℝ) / z := div_le_div_of_nonneg_left (by positivity) hz hzY
      _ = _ := by rw [show z = exp (L ^ (31 / 32 : ℝ)) from rfl, exp_neg]; ring
  have hgood : (X : ℝ) / ((Y : ℝ) + 1) * (2 : ℝ) ^ (L ^ (15 / 16 : ℝ)) ≤
      X * exp (log 2 * L ^ (15 / 16 : ℝ) - L ^ (31 / 32 : ℝ)) := by
    calc
      _ ≤ (X : ℝ) / z * (2 : ℝ) ^ (L ^ (15 / 16 : ℝ)) := by gcongr
      _ = _ := by rw [rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), exp_sub]; ring
  have hbad : (C * X / log ((Y : ℝ) + 1)) * L ^ (-15 / 28 : ℝ) *
      (∑ n ∈ Icc 1 X, omegaWeight n) ≤ X * (C * D * L ^ (-1 / 224 : ℝ)) := by
    calc
      _ ≤ (C * X / L ^ (31 / 32 : ℝ)) * L ^ (-15 / 28 : ℝ) *
          (D * L ^ (3 / 2 : ℝ)) := by
        gcongr
        exact sum_nonneg (fun n _ => omegaWeight_nonneg n)
      _ = _ := by
        have hp : L ^ (-15 / 28 : ℝ) * L ^ (3 / 2 : ℝ) /
            L ^ (31 / 32 : ℝ) = L ^ (-1 / 224 : ℝ) := by
          rw [← rpow_add hL, ← rpow_sub hL]
          norm_num
        calc
          _ = X * (C * D * (L ^ (-15 / 28 : ℝ) * L ^ (3 / 2 : ℝ) /
              L ^ (31 / 32 : ℝ))) := by ring
          _ = _ := by rw [hp]
  apply (div_le_iff₀ hX0).mpr
  have hcount : (spCount X : ℝ) ≤
      (((Icc 1 X).filter (fun n => n ∈ (Y + 1).smoothNumbers)).card : ℝ) +
      (squareExceptions X Y).card + ∑ m ∈ Icc 1 (X / (Y + 1)),
        ((extensionPrimes m (X / m)).card : ℝ) := by
    exact_mod_cast four_class_count X Y
  calc
    _ ≤ _ := hcount
    _ ≤ X * (smoothConstant * (1 + L ^ (31 / 32 : ℝ)) *
          exp (-(L ^ (1 / 32 : ℝ)))) +
        X * (2 * exp (-(L ^ (31 / 32 : ℝ)))) +
        ((X : ℝ) / (Y + 1) * (2 : ℝ) ^ (L ^ (15 / 16 : ℝ)) +
          (C * X / log (Y + 1)) * L ^ (-15 / 28 : ℝ) *
            ∑ n ∈ Icc 1 X, omegaWeight n) :=
      add_le_add (add_le_add hsm' hsq') hext
    _ ≤ X * (smoothConstant * (1 + L ^ (31 / 32 : ℝ)) *
          exp (-(L ^ (1 / 32 : ℝ)))) +
        X * (2 * exp (-(L ^ (31 / 32 : ℝ)))) +
        (X * exp (log 2 * L ^ (15 / 16 : ℝ) - L ^ (31 / 32 : ℝ)) +
          X * (C * D * L ^ (-1 / 224 : ℝ))) :=
      add_le_add le_rfl (add_le_add hgood hbad)
    _ = _ := by dsimp [densityEnvelope]; ring

/-- Strongly pseudoperfect positive integers have natural density zero. -/
theorem result :
    Tendsto (fun X : ℕ => (spCount X : ℝ) / X) atTop (𝓝 0) := by
  obtain ⟨D, hD, hmoment⟩ := omega_moment_bound
  let C := log (4 : ℝ) + 1
  have hC : 0 ≤ C := by dsimp [C]; positivity
  obtain ⟨T, hprime⟩ := eventually_atTop.mp
    (Chebyshev.eventually_primeCounting_le (by norm_num : (0 : ℝ) < 1))
  have hL : Tendsto (fun X : ℕ => log (X : ℝ)) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hp := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 31 / 32)).comp hL
  have hz := tendsto_exp_atTop.comp hp
  apply squeeze_zero' (Eventually.of_forall (fun X => by positivity)) ?_
    ((envelope_limit C D).comp hL)
  filter_upwards [eventually_ge_atTop (3 : ℕ), hp.eventually (eventually_ge_atTop 2),
    hz.eventually (eventually_ge_atTop (max 3 T))] with X hX hscale hzX
  have hY : 2 ≤ ⌊exp ((log (X : ℝ)) ^ (31 / 32 : ℝ))⌋₊ :=
    Nat.le_floor ((by norm_num : (2 : ℝ) ≤ 3).trans ((le_max_left _ _).trans hzX))
  apply count_envelope hX hC hD.le hscale hY (hmoment X hX)
  intro t ht
  apply hprime t
  exact (le_max_right 3 T).trans (hzX.trans ((Nat.lt_floor_add_one _).le.trans ht))

end D5.S3.Arith.Abundancy.StrongPseudoperfectDensity
