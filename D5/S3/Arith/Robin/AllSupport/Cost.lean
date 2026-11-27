/- GID: D5/S3/Arith/Robin/AllSupport/Cost
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/AllSupport/Cost
   mirror-E: none(waiver:analytic-prime-cost-estimate)
   anchors: []
   utility: none
   digest: Exact Robin margin and valuation cost for every prime support. -/

/-
The scalar and finite-universe arguments adapt Robin1984 contributors'
Equivalence/ExponentProxyBound.lean and Analytic/PrimeReferenceSign.lean
(Apache-2.0), with the logarithmic estimate in
Equivalence/AbundancyExponentBound.lean, at commit
5ce18bf3487c68d9353276ef5811057f60d17808.
https://github.com/kimihiro64/Robin1984/tree/5ce18bf3487c68d9353276ef5811057f60d17808
Mathematical context: Guy Robin, Grandes valeurs de la fonction somme
des diviseurs et hypothèse de Riemann (1984).
The exact correction identity follows section 4 of the companion
robin-proof.txt (sshx/758bfb5cf7b54445e0563c6c/attempt-1).
-/
import D5.S3.Arith.Robin.OriginalEndpointPrimeTail
import D5.S3.Arith.Robin.ThetaTailRobinWitness

/-! Exact Robin margin with a prime-cost reserve for arbitrary support. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace D5.S3.Arith.Robin.AllSupport

open Finset Real MeasureTheory
open scoped BigOperators
open D5.S3.Arith.Robin.OriginalEndpointPrimeTail
open D5.S3.Weil.GronwallLowerEnvelope
open D5.S3.Arith.Robin.ThetaTailRobinWitness

def primePrice (H p : ℝ) : ℝ := Real.log p / (H * Real.log H)

def exponentProxy (H p : ℝ) (a : ℕ) : ℝ :=
  if a = 0 then 0 else 1 / p - (a : ℝ) * primePrice H p - p⁻¹ ^ (a + 1)

def benchmark (H p : ℝ) : ℝ :=
  if p ≤ H then 1 / p - primePrice H p else 0

def costAtom (H p : ℝ) : ℝ :=
  if p ≤ H / 2 then min (primePrice H p) (p⁻¹ ^ 2) else 0

def valuationDefect (H p : ℝ) (a : ℕ) : ℝ :=
  benchmark H p - costAtom H p - exponentProxy H p a

private theorem price_sign {H p : ℝ} (hH : 2 ≤ H) (hp : 2 ≤ p) :
    (p ≤ H → primePrice H p ≤ 1 / H) ∧
      (H ≤ p → 1 / H ≤ primePrice H p) := by
  have hH0 : 0 < H := by linarith
  have hp0 : 0 < p := by linarith
  have hlogH : 0 < Real.log H := Real.log_pos (by linarith)
  have hden : 0 < H * Real.log H := mul_pos hH0 hlogH
  have heq : Real.log H / (H * Real.log H) = 1 / H := by
    field_simp [ne_of_gt hH0, ne_of_gt hlogH]
  unfold primePrice
  constructor
  · intro h
    rw [← heq]
    exact div_le_div_of_nonneg_right (Real.log_le_log hp0 h) hden.le
  · intro h
    rw [← heq]
    exact div_le_div_of_nonneg_right (Real.log_le_log hH0 h) hden.le

/-- The zero valuation pays the full inverse-square reserve at p ≤ H/2. -/
theorem absent_prime_cost {H p : ℝ} (hH : 2 ≤ H) (hp : 2 ≤ p)
    (hsmall : p ≤ H / 2) :
    p⁻¹ ^ 2 ≤ 1 / p - primePrice H p := by
  have hp0 : 0 < p := by linarith
  have hprice : primePrice H p ≤ 1 / H := (price_sign hH hp).1 (by linarith)
  have hInv : 1 / H ≤ 1 / (2 * p) :=
    one_div_le_one_div_of_le (by positivity) (by linarith)
  have hInvP : 0 ≤ p⁻¹ := (inv_pos.mpr hp0).le
  have hInvLe : p⁻¹ ≤ (1 / 2 : ℝ) := by
    simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hp
  have hsq : p⁻¹ ^ 2 ≤ 1 / p - 1 / (2 * p) := by
    have hmul := mul_le_mul_of_nonneg_right hInvLe hInvP
    rw [show 1 / p - 1 / (2 * p) = (1 / 2 : ℝ) * p⁻¹ by ring]
    simpa only [pow_two] using hmul
  linarith

/-- Complete valuation inequality. It applies to every natural exponent. -/
theorem exponent_proxy_plus_cost_le_benchmark {H p : ℝ} (hH : 2 ≤ H)
    (hp : 2 ≤ p) (a : ℕ) :
    exponentProxy H p a + costAtom H p ≤ benchmark H p := by
  have hprice : 0 ≤ primePrice H p := by
    unfold primePrice
    exact div_nonneg (Real.log_nonneg (by linarith))
      (mul_nonneg (by linarith) (Real.log_nonneg (by linarith)))
  have hp0 : 0 < p := by linarith
  have hpow : 0 ≤ p⁻¹ ^ (a + 1) := by positivity
  have hsign := price_sign hH hp
  by_cases ha : a = 0
  · subst a
    rw [exponentProxy, ite_eq_left rfl, zero_add]
    by_cases hhalf : p ≤ H / 2
    · have hfull : p ≤ H := by linarith
      rw [costAtom, ite_eq_left hhalf, benchmark, ite_eq_left hfull]
      exact (min_le_right _ _).trans (absent_prime_cost hH hp hhalf)
    · rw [costAtom, ite_eq_right hhalf, benchmark]
      split_ifs with hfull
      · have h := (hsign.1 hfull).trans
          (one_div_le_one_div_of_le hp0 hfull)
        linarith
      · exact le_rfl
  · have ha1 : (1 : ℝ) ≤ (a : ℝ) := by
      exact_mod_cast (show 1 ≤ a by omega)
    have haPrice : primePrice H p ≤ (a : ℝ) * primePrice H p := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right ha1 hprice
    unfold exponentProxy
    rw [ite_eq_right ha]
    by_cases hhalf : p ≤ H / 2
    · have hfull : p ≤ H := by linarith
      rw [costAtom, ite_eq_left hhalf, benchmark, ite_eq_left hfull]
      by_cases haEq : a = 1
      · subst a
        simp only [Nat.cast_one, one_mul, show 1 + 1 = (2 : ℕ) by rfl]
        linarith [min_le_right (primePrice H p) (p⁻¹ ^ 2)]
      · have ha2 : (2 : ℝ) ≤ (a : ℝ) := by
          exact_mod_cast (show 2 ≤ a by omega)
        have hmul := mul_le_mul_of_nonneg_right ha2 hprice
        linarith [min_le_left (primePrice H p) (p⁻¹ ^ 2)]
    · rw [costAtom, ite_eq_right hhalf, add_zero, benchmark]
      by_cases hfull : p ≤ H
      · rw [ite_eq_left hfull]
        linarith
      · rw [ite_eq_right hfull]
        have hHp : H ≤ p := le_of_lt (lt_of_not_ge hfull)
        have hH0 : 0 < H := by linarith
        have h := (one_div_le_one_div_of_le hH0 hHp).trans (hsign.2 hHp)
        linarith

theorem valuation_defect_nonneg {H p : ℝ} (hH : 2 ≤ H) (hp : 2 ≤ p) (a : ℕ) :
    0 ≤ valuationDefect H p a := by
  unfold valuationDefect
  linarith [exponent_proxy_plus_cost_le_benchmark hH hp a]

/-- The cost supplied by every prime up to H/2, including absent primes. -/
def primeCost (H : ℝ) : ℝ :=
  ∑ p ∈ Nat.primesLE ⌊H / 2⌋₊, min (primePrice H p) ((p : ℝ)⁻¹ ^ 2)

def exponentDefect (n : ℕ) (H : ℝ) : ℝ :=
  ∑ p ∈ n.primeFactors ∪ Nat.primesLE ⌊H⌋₊, valuationDefect H p (n.factorization p)

theorem exponent_defect_nonneg (n : ℕ) {H : ℝ} (hH : 2 ≤ H) :
    0 ≤ exponentDefect n H := by
  unfold exponentDefect
  apply Finset.sum_nonneg
  intro p hp
  have hpPrime : p.Prime := by
    rcases Finset.mem_union.mp hp with h | h
    · exact Nat.prime_of_mem_primeFactors h
    · exact Nat.prime_of_mem_primesLE h
  exact valuation_defect_nonneg hH (by exact_mod_cast hpPrime.two_le) _

/-- Exact finite comparison retaining the nonnegative valuation excess. -/
theorem exponent_defect_eq (n : ℕ) {H : ℝ} (hH : 2 ≤ H) :
    exponentDefect n H =
      (∑ p ∈ Nat.primesLE ⌊H⌋₊, (1 : ℝ) / p) -
        Chebyshev.theta H / (H * Real.log H) - primeCost H -
        ∑ p ∈ n.primeFactors, exponentProxy H p (n.factorization p) := by
  classical
  let S : Finset ℕ := n.primeFactors ∪ Nat.primesLE ⌊H⌋₊
  have hFull : Nat.primesLE ⌊H⌋₊ ⊆ S := Finset.subset_union_right
  have hHalf : Nat.primesLE ⌊H / 2⌋₊ ⊆ S :=
    (Nat.primesLE_mono (Nat.floor_mono (by linarith : H / 2 ≤ H))).trans hFull
  have hPrime (p : ℕ) (hp : p ∈ S) : p.Prime := by
    rcases Finset.mem_union.mp hp with h | h
    · exact Nat.prime_of_mem_primeFactors h
    · exact Nat.prime_of_mem_primesLE h
  have hFilter (y : ℝ) (hy : 0 ≤ y) (hsub : Nat.primesLE ⌊y⌋₊ ⊆ S) :
      S.filter (fun p : ℕ => (p : ℝ) ≤ y) = Nat.primesLE ⌊y⌋₊ := by
    ext p
    simp only [Finset.mem_filter, Nat.mem_primesLE]
    constructor
    · intro hp
      exact ⟨Nat.le_floor hp.2, hPrime p hp.1⟩
    · intro hp
      exact ⟨hsub (Nat.mem_primesLE.mpr hp), (Nat.le_floor_iff hy).mp hp.1⟩
  have hBenchmark : (∑ p ∈ S, benchmark H p) =
      (∑ p ∈ Nat.primesLE ⌊H⌋₊, (1 : ℝ) / p) -
        Chebyshev.theta H / (H * Real.log H) := by
    simp only [benchmark, ← Finset.sum_filter, hFilter H (by linarith) hFull]
    rw [Finset.sum_sub_distrib]
    simp only [primePrice, ← Finset.sum_div, ← Chebyshev.theta_eq_sum_primesLE]
  have hCost : (∑ p ∈ S, costAtom H p) = primeCost H := by
    simp only [costAtom, ← Finset.sum_filter, hFilter (H / 2) (by linarith) hHalf,
      primeCost]
  have hProxy : (∑ p ∈ n.primeFactors, exponentProxy H p (n.factorization p)) =
      ∑ p ∈ S, exponentProxy H p (n.factorization p) := by
    apply Finset.sum_subset (Finset.subset_union_left : n.primeFactors ⊆ S)
    intro p _ hp
    have hzero : n.factorization p = 0 := Finsupp.notMem_support_iff.mp
      (by simpa only [Nat.support_factorization] using hp)
    simp [exponentProxy, hzero]
  change (∑ p ∈ S, valuationDefect H p (n.factorization p)) = _
  simp only [valuationDefect, Finset.sum_sub_distrib]
  rw [hBenchmark, hCost, ← hProxy]

/-- The logarithmic Taylor correction on the actual occupied prime factors. -/
def logarithmicRemainder (n : ℕ) : ℝ :=
  ∑ p ∈ n.primeFactors, (layerTail n p - (p : ℝ)⁻¹ ^ (n.factorization p + 1))

theorem logarithmic_remainder_nonneg (n : ℕ) :
    0 ≤ logarithmicRemainder n := by
  unfold logarithmicRemainder
  apply Finset.sum_nonneg
  intro p hp
  have hprime := Nat.prime_of_mem_primeFactors hp
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hprime.pos
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hprime.one_lt
  have hinv := (inv_lt_one₀ hp0).2 hp1
  have hpow : (p : ℝ)⁻¹ ^ (n.factorization p + 1) < 1 :=
    pow_lt_one₀ (inv_nonneg.mpr hp0.le) hinv (by omega)
  have hlog := Real.log_le_sub_one_of_pos (sub_pos.mpr hpow)
  unfold layerTail
  linarith

/-- The full correction of omitted primes, using the native Mertens series.
Composite indices contribute zero by definition of M_eq_summand. -/
def omittedEulerCorrection (n : ℕ) : ℝ :=
  ∑' p : {p : ℕ // p ∉ n.primeFactors}, -Mertens.M_eq_summand (p : ℕ)

private theorem mertens_summand_nonpos (p : ℕ) : Mertens.M_eq_summand p ≤ 0 := by
  by_cases hp : p.Prime
  · rw [Mertens.M_eq_summand, ite_eq_left hp]
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
    have hpos : 0 < 1 - (1 : ℝ) / p := by
      simpa only [one_div] using sub_pos.mpr ((inv_lt_one₀ hp0).2 hp1)
    linarith [Real.log_le_sub_one_of_pos hpos]
  · simp only [Mertens.M_eq_summand, ite_eq_right hp, le_refl]

theorem omitted_euler_correction_nonneg (n : ℕ) : 0 ≤ omittedEulerCorrection n := by
  unfold omittedEulerCorrection
  exact tsum_nonneg fun p => neg_nonneg.mpr (mertens_summand_nonpos (p : ℕ))

theorem omitted_euler_correction_eq (n : ℕ) :
    omittedEulerCorrection n = Real.eulerMascheroniConstant - Mertens.M +
      ∑ p ∈ n.primeFactors, Mertens.M_eq_summand p := by
  have h := Mertens.M_eq_summable.sum_add_tsum_subtype_compl n.primeFactors
  rw [Mertens.tsum_M_eq_summand_eq, Mertens.γ.eq_eulerMascheroni] at h
  unfold omittedEulerCorrection
  rw [tsum_neg]
  linarith

/-- Exact support proxy before extending to primes outside the support. -/
theorem log_sigma_eq_actual_proxy {n : ℕ} (hn : 0 < n) (H : ℝ) :
    Real.log ((ArithmeticFunction.sigma 1 n : ℝ) / n) =
      -(∑ p ∈ n.primeFactors, Mertens.M_eq_summand p) +
      (∑ p ∈ n.primeFactors, exponentProxy H p (n.factorization p)) +
      Real.log (n : ℝ) / (H * Real.log H) - logarithmicRemainder n := by
  have hHeight :
      (∑ p ∈ n.primeFactors, (n.factorization p : ℝ) * primePrice H p) =
        Real.log (n : ℝ) / (H * Real.log H) := by
    simp_rw [primePrice, ← mul_div_assoc]
    rw [← Finset.sum_div, Real.log_nat_eq_sum_factorization n, Finsupp.sum,
      Nat.support_factorization]
  have hProxy :
      (∑ p ∈ n.primeFactors, exponentProxy H p (n.factorization p)) =
        (∑ p ∈ n.primeFactors, ((1 : ℝ) / p - (p : ℝ)⁻¹ ^ (n.factorization p + 1))) -
          Real.log (n : ℝ) / (H * Real.log H) := by
    rw [← hHeight, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro p hp
    have hne : n.factorization p ≠ 0 := Finsupp.mem_support_iff.mp
      (by simpa only [Nat.support_factorization] using hp)
    rw [exponentProxy, ite_eq_right hne]
    ring
  have heuler : eulerMass n = (∑ p ∈ n.primeFactors, (1 : ℝ) / p) -
      ∑ p ∈ n.primeFactors, Mertens.M_eq_summand p := by
    unfold eulerMass
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro p hp
    simp only [Mertens.M_eq_summand, ite_eq_left (Nat.prime_of_mem_primeFactors hp), one_div]
    ring
  have hremain : logarithmicRemainder n =
      tail n - ∑ p ∈ n.primeFactors, (p : ℝ)⁻¹ ^ (n.factorization p + 1) := by
    simp only [logarithmicRemainder, Finset.sum_sub_distrib, tail]
  rw [log_sigma_div_eq_eulerMass_sub_tail hn, heuler, hProxy, hremain,
    Finset.sum_sub_distrib]
  ring

/-- The signed theta tail at the literal logarithmic height. -/
def thetaTail (H : ℝ) : ℝ :=
  ∫ t in Set.Ioi H, (Chebyshev.theta t - t) *
    D5.S3.Arith.Robin.ActualRobinClockCovariance.activationDensity t

/-- Exact all-support ledger with no prime-prefix or optimizer restriction. -/
theorem robin_margin_eq_all_support_ledger {n : ℕ} (hn : 0 < n)
    (hH : 2 ≤ Real.log (n : ℝ)) :
    robinLogMargin n =
      primeCost (Real.log n) + thetaTail (Real.log n) +
      exponentDefect n (Real.log n) + logarithmicRemainder n +
      omittedEulerCorrection n := by
  let H : ℝ := Real.log (n : ℝ)
  have hH2 : 2 ≤ H := hH
  have hdef := exponent_defect_eq n hH2
  have hproxy := log_sigma_eq_actual_proxy hn H
  have homit := omitted_euler_correction_eq n
  have htheta : -thetaTail H = Mertens.E₂p H -
      (Chebyshev.theta H - H) / (H * Real.log H) :=
    (theta_tail_mertens_robin H hH2).2.1
  rw [Mertens.E₂p, ← Nat.primesLE_eq_filter_Ioc_zero] at htheta
  change Real.eulerMascheroniConstant + Real.log (Real.log H) -
    Real.log ((ArithmeticFunction.sigma 1 n : ℝ) / n) =
    primeCost H + thetaTail H + exponentDefect n H + logarithmicRemainder n +
      omittedEulerCorrection n
  change Real.log ((ArithmeticFunction.sigma 1 n : ℝ) / n) =
    -(∑ p ∈ n.primeFactors, Mertens.M_eq_summand p) +
    (∑ p ∈ n.primeFactors, exponentProxy H p (n.factorization p)) +
    H / (H * Real.log H) - logarithmicRemainder n at hproxy
  simp only [sub_div] at htheta
  linarith only [hdef, hproxy, homit, htheta]

/-- Unconditional arithmetic reduction, with the analytic tail still signed. -/
theorem robin_margin_ge_prime_cost_add_theta_tail {n : ℕ} (hn : 0 < n)
    (hH : 2 ≤ Real.log (n : ℝ)) :
    primeCost (Real.log n) + thetaTail (Real.log n) ≤ robinLogMargin n := by
  rw [robin_margin_eq_all_support_ledger hn hH]
  have hD := exponent_defect_nonneg n hH
  have hR := logarithmic_remainder_nonneg n
  have hE := omitted_euler_correction_nonneg n
  linarith

/-- A uniform or pointwise scalar comparison suffices for strict Robin margin. -/
theorem robin_margin_pos_of_cost_tail {n : ℕ} (hn : 0 < n)
    (hH : 2 ≤ Real.log (n : ℝ)) {B : ℝ}
    (hcost : B ≤ primeCost (Real.log n)) (htail : -B < thetaTail (Real.log n)) :
    0 < robinLogMargin n := by
  linarith [robin_margin_ge_prime_cost_add_theta_tail hn hH]

end D5.S3.Arith.Robin.AllSupport
