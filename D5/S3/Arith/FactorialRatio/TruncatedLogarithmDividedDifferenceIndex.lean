/- GID: D5/S3/Arith/FactorialRatio/TruncatedLogarithmDividedDifferenceIndex
   generality: G
   mirror-B: D5/B/S3/Arith/FactorialRatio/TruncatedLogarithmDividedDifferenceIndex
   mirror-E: none(waiver:symbolic-proof-no-numeric-artifact)
   anchors: [mathlib/module/Mathlib.NumberTheory.Chebyshev]
   utility: none
   digest: Exact divided-difference LCM indices and the factor-four prime tent. -/

module


public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import OmegaBuild.Commands


/-! The product of prefix LCMs at the cutoffs `d / r` admits two exact
finite incidence counts. At the factor-four scales the difference of the
counts gives the prime tent and an integral relative quotient. -/

compile_only_with_mathlib


set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FactorialRatio.TruncatedLogarithmDividedDifferenceIndex

open Finset
open ArithmeticFunction

/-- The diagonal index of the normalized independent-step difference lattice. -/
@[expose] public def differenceIndex (n r : ℕ) : ℕ :=
  ∏ d ∈ range n, Nat.lcmUpto (d / r)

private theorem differenceIndex_ne_zero (n r : ℕ) : differenceIndex n r ≠ 0 := by
  unfold differenceIndex
  exact Finset.prod_ne_zero_iff.mpr fun d _ => Nat.lcmUpto_ne_zero _

/-- Exact profile obtained by counting the same finite incidences in either order. -/
public theorem log_differenceIndex (n r : ℕ) (hr : 0 < r) :
    Real.log (differenceIndex n r : ℝ) =
      ∑ q ∈ range n, ((n - r * q : ℕ) : ℝ) * vonMangoldt q := by
  unfold differenceIndex
  rw [Nat.cast_prod, Real.log_prod (fun d _ => Nat.cast_ne_zero.mpr (Nat.lcmUpto_ne_zero _))]
  simp only [← Chebyshev.psi_eq_log_lcmUpto, Chebyshev.psi_eq_sum_Icc, Nat.floor_natCast]
  calc
    _ = ∑ d ∈ range n, ∑ q ∈ range n,
        if r * q ≤ d then vonMangoldt q else 0 := by
      apply Finset.sum_congr rfl
      intro d hd
      have hdn := Finset.mem_range.mp hd
      rw [← Finset.sum_filter]
      have heq : (range n).filter (fun q => r * q ≤ d) = Icc 0 (d / r) := by
        ext q
        simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc, zero_le, true_and]
        constructor
        · rintro ⟨_, hq⟩
          exact (Nat.le_div_iff_mul_le hr).mpr (by simpa [mul_comm] using hq)
        · intro hq
          exact ⟨(hq.trans (Nat.div_le_self _ _)).trans_lt hdn,
            by simpa [mul_comm] using (Nat.le_div_iff_mul_le hr).mp hq⟩
      rw [heq]
    _ = ∑ q ∈ range n, ∑ d ∈ range n,
          if r * q ≤ d then vonMangoldt q else 0 := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro q _
      rw [← Finset.sum_filter]
      have heq : (range n).filter (fun d => r * q ≤ d) = Ico (r * q) n := by
        ext d
        simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
        tauto
      rw [heq, Finset.sum_const, nsmul_eq_mul, Nat.card_Ico]

/-- Count the powers of a fixed prime that are at most d/r. -/
private theorem log_eq_sum_pow_incidence {n d r p : ℕ} (hd : d < n)
    (hr : 0 < r) (hp : p.Prime) :
    p.log (d / r) = ∑ a ∈ range n, if r * p ^ (a + 1) ≤ d then 1 else 0 := by
  rw [← Finset.sum_filter]
  have hcut : p.log (d / r) < n :=
    (Nat.log_le_self _ _).trans_lt ((Nat.div_le_self _ _).trans_lt hd)
  have heq : (range n).filter (fun a => r * p ^ (a + 1) ≤ d) =
      range (p.log (d / r)) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_range]
    by_cases hzero : d / r = 0
    · have hnone : ¬ r * p ^ (a + 1) ≤ d := by
        intro h
        have hpow := (Nat.le_div_iff_mul_le hr).mpr (by simpa [mul_comm] using h)
        rw [hzero] at hpow
        exact (not_le_of_gt (Nat.pow_pos hp.pos)) hpow
      simp [hzero, hnone]
    · have hiff : r * p ^ (a + 1) ≤ d ↔ a + 1 ≤ p.log (d / r) := by
        rw [Nat.le_log_iff_pow_le hp.one_lt hzero]
        exact ⟨fun h => (Nat.le_div_iff_mul_le hr).mpr (by simpa [mul_comm] using h),
          fun h => by simpa [mul_comm] using (Nat.le_div_iff_mul_le hr).mp h⟩
      rw [hiff]
      omega
  rw [heq]
  simp

/-- Every prime-power exponent of the exact divided-difference index. -/
public theorem factorization_differenceIndex (n r : ℕ) (hr : 0 < r) {p : ℕ} (hp : p.Prime) :
    (differenceIndex n r).factorization p =
      ∑ a ∈ range n, (n - r * p ^ (a + 1)) := by
  unfold differenceIndex
  rw [Nat.factorization_prod_apply (fun d _ => Nat.lcmUpto_ne_zero _)]
  simp only [Nat.factorization_lcmUpto _ hp]
  calc
    _ = ∑ d ∈ range n, ∑ a ∈ range n,
        if r * p ^ (a + 1) ≤ d then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro d hd
      exact log_eq_sum_pow_incidence (Finset.mem_range.mp hd) hr hp
    _ = ∑ a ∈ range n, ∑ d ∈ range n,
        if r * p ^ (a + 1) ≤ d then 1 else 0 := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a _
      rw [← Finset.sum_filter]
      have heq : (range n).filter (fun d => r * p ^ (a + 1) ≤ d) =
          Ico (r * p ^ (a + 1)) n := by
        ext d
        simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
        tauto
      rw [heq]
      simp

/-- The linear prime tent, extended by zero outside the factor-four band. -/
@[expose] public def tentWeight (x q : ℕ) : ℕ :=
  if q ≤ x then 0 else if q ≤ 2 * x then 2 * (q - x) else 4 * x - q

private theorem tentWeight_eq_ramp (x q : ℕ) :
    2 * (4 * x - q) + (4 * x - 4 * q) =
      3 * (4 * x - 2 * q) + 2 * tentWeight x q := by
  by_cases h₁ : q ≤ x
  · simp [tentWeight, h₁]; omega
  · by_cases h₂ : q ≤ 2 * x
    · simp [tentWeight, h₁, h₂]; omega
    · simp [tentWeight, h₁, h₂]; omega

/-- The relative index is the natural quotient of the factor-four LCM products. -/
@[expose] public def relativeIndex (x : ℕ) : ℕ :=
  (differenceIndex (4 * x) 1 ^ 2 * differenceIndex (4 * x) 4) /
    differenceIndex (4 * x) 2 ^ 3

/-- The relative index is a positive integer and the quotient is exact. -/
public theorem relativeIndex_spec (x : ℕ) :
    differenceIndex (4 * x) 2 ^ 3 ∣
      differenceIndex (4 * x) 1 ^ 2 * differenceIndex (4 * x) 4 ∧
    relativeIndex x * differenceIndex (4 * x) 2 ^ 3 =
      differenceIndex (4 * x) 1 ^ 2 * differenceIndex (4 * x) 4 ∧
    0 < relativeIndex x := by
  have h1 := differenceIndex_ne_zero (4 * x) 1
  have h2 := differenceIndex_ne_zero (4 * x) 2
  have h4 := differenceIndex_ne_zero (4 * x) 4
  have hdvd : differenceIndex (4 * x) 2 ^ 3 ∣
      differenceIndex (4 * x) 1 ^ 2 * differenceIndex (4 * x) 4 := by
    rw [← Nat.factorization_prime_le_iff_dvd (pow_ne_zero _ h2)
      (mul_ne_zero (pow_ne_zero _ h1) h4)]
    intro p hp
    rw [Nat.factorization_mul (pow_ne_zero _ h1) h4, Nat.factorization_pow, Nat.factorization_pow]
    simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul,
      factorization_differenceIndex _ _ (by decide : 0 < 1) hp,
      factorization_differenceIndex _ _ (by decide : 0 < 2) hp,
      factorization_differenceIndex _ _ (by decide : 0 < 4) hp, one_mul]
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro a _
    have h := tentWeight_eq_ramp x (p ^ (a + 1))
    omega
  have hmul : relativeIndex x * differenceIndex (4 * x) 2 ^ 3 =
      differenceIndex (4 * x) 1 ^ 2 * differenceIndex (4 * x) 4 :=
    Nat.div_mul_cancel hdvd
  refine ⟨hdvd, hmul, Nat.pos_of_ne_zero ?_⟩
  intro hz
  rw [hz, zero_mul] at hmul
  exact (mul_ne_zero (pow_ne_zero _ h1) h4) hmul.symm

/-- All prime powers, including the small primes, give exactly the tent. -/
public theorem factorization_relativeIndex (x : ℕ) {p : ℕ} (hp : p.Prime) :
    (relativeIndex x).factorization p =
      ∑ a ∈ range (4 * x), 2 * tentWeight x (p ^ (a + 1)) := by
  have h := congrArg (fun m : ℕ => m.factorization p) (relativeIndex_spec x).2.1
  rw [Nat.factorization_mul (Nat.ne_of_gt (relativeIndex_spec x).2.2) (pow_ne_zero _ (differenceIndex_ne_zero _ _)),
      Nat.factorization_mul (pow_ne_zero _ (differenceIndex_ne_zero _ _)) (differenceIndex_ne_zero _ _),
      Nat.factorization_pow, Nat.factorization_pow] at h
  simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul,
    factorization_differenceIndex _ _ (by decide : 0 < 1) hp,
    factorization_differenceIndex _ _ (by decide : 0 < 2) hp,
    factorization_differenceIndex _ _ (by decide : 0 < 4) hp, one_mul] at h
  have hsum := Finset.sum_congr (s₁ := range (4 * x)) rfl
    (fun a _ => tentWeight_eq_ramp x (p ^ (a + 1)))
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum ⊢
  omega

/-- Exact logarithmic tent identity, without a prime-power remainder. -/
public theorem log_relativeIndex (x : ℕ) :
    Real.log (relativeIndex x : ℝ) =
      2 * ∑ q ∈ range (4 * x), (tentWeight x q : ℝ) * vonMangoldt q := by
  have hprod := congrArg (fun m : ℕ => Real.log (m : ℝ)) (relativeIndex_spec x).2.1
  simp only [Nat.cast_mul, Nat.cast_pow] at hprod
  rw [Real.log_mul (Nat.cast_ne_zero.mpr (Nat.ne_of_gt (relativeIndex_spec x).2.2))
      (pow_ne_zero _ (Nat.cast_ne_zero.mpr (differenceIndex_ne_zero _ _))),
      Real.log_mul (pow_ne_zero _ (Nat.cast_ne_zero.mpr (differenceIndex_ne_zero _ _)))
      (Nat.cast_ne_zero.mpr (differenceIndex_ne_zero _ _)), Real.log_pow, Real.log_pow] at hprod
  have hsum :
      2 * (∑ q ∈ range (4 * x), ((4 * x - q : ℕ) : ℝ) * vonMangoldt q) +
      (∑ q ∈ range (4 * x), ((4 * x - 4 * q : ℕ) : ℝ) * vonMangoldt q) =
      3 * (∑ q ∈ range (4 * x), ((4 * x - 2 * q : ℕ) : ℝ) * vonMangoldt q) +
      2 * ∑ q ∈ range (4 * x), (tentWeight x q : ℝ) * vonMangoldt q := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro q _
    have hc : 2 * ((4 * x - q : ℕ) : ℝ) + ((4 * x - 4 * q : ℕ) : ℝ) =
        3 * ((4 * x - 2 * q : ℕ) : ℝ) + 2 * (tentWeight x q : ℝ) := by
      exact_mod_cast tentWeight_eq_ramp x q
    nlinarith only [congrArg (fun t : ℝ => t * vonMangoldt q) hc]
  rw [log_differenceIndex _ _ (by decide : 0 < 1), log_differenceIndex _ _ (by decide : 0 < 2),
    log_differenceIndex _ _ (by decide : 0 < 4)] at hprod
  norm_num only [one_mul, Nat.cast_ofNat] at hprod
  rw [hsum, add_comm] at hprod
  exact add_left_cancel hprod

end D5.S3.Arith.FactorialRatio.TruncatedLogarithmDividedDifferenceIndex
