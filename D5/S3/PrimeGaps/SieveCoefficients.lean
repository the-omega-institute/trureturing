/- GID: D5/S3/PrimeGaps/SieveCoefficients
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Port the long-gap sieve normalizer, divisor coefficients, and their moment bounds. -/

/- Ported from openai/LongGapsBetweenPrimes commit 8f5fa88c88b4750028c05b66b081d56a92418054.
   Modified by trureturing on 2026-09-04: repository routing and module split. -/
/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Mathlib

/-!
# Improved Long Gaps Between Primes

For all sufficiently large `X`,
`G(X) >> log X * (log log X)^2 * log log log log X / (log log log X)^2`,
where `G(X)` is the largest gap between consecutive primes not exceeding `X`.

The main results are `short_translates` (Proposition 1.2, in `ShortTranslateClosure`) and
`long_gap_theorem` (Theorem 1.1, in `LongGapConclusion`). The proof uses weak Mertens
estimates, `κ = 1/8`, and a larger fixed constant in the auxiliary smoothness cutoff.

The upstream single file is split across this directory in dependency order; every module
shares the upstream namespace `LongGapsBetweenPrimes`, so the ported declarations and their
dot-notation are unchanged. Retirement condition: delete this port and reference the
upstream declarations directly once a mathlib revision pinned by this repository carries
equivalent statements.
-/

namespace LongGapsBetweenPrimes

noncomputable section

/-- The j-fold natural logarithm used in the statement of Theorem 1.1. -/
def iteratedLog (j : ℕ) (x : ℝ) : ℝ := (Real.log^[j]) x

/-- The function on the right hand side of Theorem 1.1, without its constant. -/
def gapScale (x : ℝ) : ℝ :=
  Real.log x * (iteratedLog 2 x) ^ 2 * iteratedLog 4 x / (iteratedLog 3 x) ^ 2

/-- Consecutive primes, specified without choosing an enumeration. -/
def ConsecutivePrimes (p q : ℕ) : Prop :=
  p.Prime ∧ q.Prime ∧ p < q ∧ ∀ r : ℕ, p < r → r < q → ¬r.Prime

/-- The precise conclusion to be proved. -/
def LongGapTheorem : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ᶠ X : ℝ in Filter.atTop,
    ∃ p q : ℕ, ConsecutivePrimes p q ∧ (q : ℝ) ≤ X ∧ c * gapScale X ≤ (q - p : ℕ)

/-- The short-translate assertion of Proposition 1.2. -/
def ShortTranslates : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ δ < 1 / 2 ∧ ∀ᶠ x : ℝ in Filter.atTop,
    ∀ H : ℕ, x < H → (H : ℝ) ≤ x * (Real.log x) ^ 2 →
    ∀ S : Finset ℕ, S ⊆ Finset.Icc 1 H → (S.card : ℝ) ≤ δ * x →
    ∀ b : ℕ, b < primorial ⌊x⌋₊ →
    ∃ t : ℕ, 1 ≤ t ∧ (t : ℝ) ≤ Real.exp x ∧
      ∀ s ∈ S, ¬Nat.Prime (b + primorial ⌊x⌋₊ * t + s)

/-- The normalization B in (3.1). -/
def normalizer (P : ℕ) : ℝ :=
  ∑ d ∈ P.divisors.erase 1, 1 / ((d.totient : ℝ) * Real.log d)

/-- The coefficient a(d) in (3.1). -/
def coefficient (P d : ℕ) : ℝ :=
  if d = 1 then 1 else -1 / (normalizer P * Real.log d)

/-- A divisor other than one is greater than one. -/
lemma one_lt_of_mem_divisors_erase_one {P d : ℕ}
    (hd : d ∈ P.divisors.erase 1) : 1 < d := by
  exact lt_of_le_of_ne (Nat.pos_of_mem_divisors (Finset.mem_of_mem_erase hd))
    (Finset.ne_of_mem_erase hd).symm

/-- The normalizer is positive when `P > 1`. -/
lemma normalizer_pos {P : ℕ} (hP : 1 < P) : 0 < normalizer P := by
  unfold normalizer
  apply Finset.sum_pos
  · intro d hd
    have hd' := one_lt_of_mem_divisors_erase_one hd
    have ht : 0 < (d.totient : ℝ) := by
      exact_mod_cast Nat.totient_pos.mpr (by omega : 0 < d)
    exact one_div_pos.mpr (mul_pos ht (Real.log_pos (by exact_mod_cast hd')))
  · exact ⟨P, Finset.mem_erase.mpr ⟨ne_of_gt hP, Nat.mem_divisors_self P (by omega)⟩⟩

/-- For `P > 1`, coefficients at `d > 1` are negative. -/
lemma coefficient_neg {P d : ℕ} (hP : 1 < P) (hd : 1 < d) :
    coefficient P d < 0 := by
  rw [coefficient, if_neg (ne_of_gt hd)]
  exact div_neg_of_neg_of_pos (by norm_num)
    (mul_pos (normalizer_pos hP) (Real.log_pos (by exact_mod_cast hd)))

/-- Exact cancellation, equations (3.2) and (3.5). -/
theorem coefficient_cancellation {P : ℕ} (hP : 1 < P) :
    ∑ d ∈ P.divisors, coefficient P d / d.totient = 0 := by
  have hB : normalizer P ≠ 0 := ne_of_gt (normalizer_pos hP)
  have hsum : ∑ d ∈ P.divisors.erase 1, coefficient P d / d.totient =
      -(normalizer P)⁻¹ * normalizer P := by
    change _ = -(normalizer P)⁻¹ *
      ∑ d ∈ P.divisors.erase 1, 1 / ((d.totient : ℝ) * Real.log d)
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d hd
    simp only [coefficient, if_neg (Finset.ne_of_mem_erase hd)]
    ring
  rw [← Finset.sum_erase_add _ _ (Nat.one_mem_divisors.mpr (by omega : P ≠ 0)),
    hsum]
  simp [coefficient, hB]

/-- The omitted terms in (3.11) have positive total mass. -/
theorem partial_cancellation {P : ℕ} (hP : 1 < P)
    (E : Finset ℕ) (hE : E ⊆ P.divisors) (h1 : 1 ∈ E) :
    ∑ d ∈ E, coefficient P d / d.totient =
      ∑ d ∈ P.divisors \ E, |coefficient P d| / d.totient := by
  have hsum := Finset.sum_sdiff hE (f := fun d => coefficient P d / d.totient)
  rw [coefficient_cancellation hP] at hsum
  rw [eq_neg_of_add_eq_zero_right hsum, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  rcases Finset.mem_sdiff.mp hd with ⟨hd, hdE⟩
  have hd1 : d ≠ 1 := by
    rintro rfl
    exact hdE h1
  rw [abs_of_neg (coefficient_neg hP
    (one_lt_of_mem_divisors_erase_one (Finset.mem_erase.mpr ⟨hd1, hd⟩))), neg_div]

/-- A divisor subsum containing one has nonnegative weighted coefficient sum. -/
lemma partial_cancellation_nonneg {P : ℕ} (hP : 1 < P)
    (E : Finset ℕ) (hE : E ⊆ P.divisors) (h1 : 1 ∈ E) :
    0 ≤ ∑ d ∈ E, coefficient P d / d.totient := by
  rw [partial_cancellation hP E hE h1]
  positivity

/-- The local factor as a function of a residue class with specified root. -/
def residueFactor {p : ℕ} (a t : Fin p) : ℝ :=
  if t = a then -1 else 1 / ((p : ℝ) - 1)

/-- Sum a constant function with one exceptional value. -/
lemma sum_one_exception {p : ℕ} (a : Fin p) (c d : ℝ) :
    (∑ t : Fin p, if t = a then c else d) = c + ((p : ℝ) - 1) * d := by
  simp [Finset.sum_ite, Finset.filter_eq', Finset.filter_ne',
    Nat.cast_sub (Nat.succ_le_of_lt (Fin.pos a))]

/-- The local mean is zero (Section 3.1). -/
theorem sum_residueFactor {p : ℕ} (hp : 1 < p) (a : Fin p) :
    ∑ t : Fin p, residueFactor a t = 0 := by
  have hp' : (p : ℝ) - 1 ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast ne_of_gt hp)
  simp [residueFactor, sum_one_exception, hp']

/-- The local square mean is 1/(p-1), before dividing the sum by p. -/
theorem sum_residueFactor_sq {p : ℕ} (hp : 1 < p) (a : Fin p) :
    (∑ t : Fin p, (residueFactor a t) ^ 2) = (p : ℝ) / ((p : ℝ) - 1) := by
  have hp' : (p : ℝ) - 1 ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast ne_of_gt hp)
  simp only [residueFactor, ite_pow, neg_one_sq, sum_one_exception]
  field_simp
  ring

/-- Distinct roots have negative covariance, as used in (3.9). -/
theorem sum_residueFactor_mul {p : ℕ} (hp : 1 < p) (a b : Fin p) (hab : a ≠ b) :
    (∑ t : Fin p, residueFactor a t * residueFactor b t) =
      -(p : ℝ) / ((p : ℝ) - 1) ^ 2 := by
  have hmul (t : Fin p) :
      residueFactor a t * residueFactor b t =
        (1 / ((p : ℝ) - 1)) * (residueFactor a t + residueFactor b t) -
          (1 / ((p : ℝ) - 1)) ^ 2 := by
    unfold residueFactor
    split_ifs with ha hb
    · exact (hab (ha.symm.trans hb)).elim
    all_goals ring
  simp_rw [hmul]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_add_distrib,
    sum_residueFactor hp a, sum_residueFactor hp b]
  simp
  ring

/-- For squarefree `d`, its totient is the product of `p - 1` over its prime factors. -/
lemma totient_eq_prod_sub_one_of_squarefree {d : ℕ} (hd : Squarefree d) :
    d.totient = ∏ p ∈ d.primeFactors, (p - 1) := by
  have h := Nat.totient_mul_prod_primeFactors d
  rw [Nat.prod_primeFactors_of_squarefree hd] at h
  exact mul_right_cancel₀ hd.ne_zero (h.trans (mul_comm _ _))

/-- A_gamma in Lemma 3.1; A is its value at gamma = 0. -/
def coefficientMoment (P : ℕ) (γ : ℝ) : ℝ :=
  ∑ d ∈ P.divisors, coefficient P d ^ 2 * (d : ℝ) ^ γ / d.totient

/-- The absolute coefficient moment over nontrivial divisors. -/
def coefficientAbsMoment (P : ℕ) (γ : ℝ) : ℝ :=
  ∑ d ∈ P.divisors.erase 1, |coefficient P d| * (d : ℝ) ^ γ / d.totient

/-- Expand the coefficient moment at exponent zero. -/
lemma coefficientMoment_zero (P : ℕ) :
    coefficientMoment P 0 = ∑ d ∈ P.divisors, coefficient P d ^ 2 / d.totient := by
  simp [coefficientMoment]

/-- The divisor one gives a lower bound of one for the coefficient moment. -/
lemma coefficientMoment_ge_one {P : ℕ} (hP : P ≠ 0) (γ : ℝ) :
    1 ≤ coefficientMoment P γ := by
  have h := Finset.single_le_sum
    (f := fun d => coefficient P d ^ 2 * (d : ℝ) ^ γ / d.totient)
    (fun d _ => div_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
      (Nat.cast_nonneg _)) (Nat.one_mem_divisors.mpr hP)
  simpa [coefficientMoment, coefficient] using h

/-- The exponential increment is at most `x * exp x`. -/
lemma exp_sub_one_le_mul_exp (x : ℝ) : Real.exp x - 1 ≤ x * Real.exp x := by
  have h := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (-x)) (Real.exp_nonneg x)
  rw [← Real.exp_add, neg_add_cancel, Real.exp_zero] at h
  linarith

/-- The power increment is at most `γ * v ^ γ * log v`. -/
lemma rpow_sub_one_le {v γ : ℝ} (hv : 0 < v) :
    v ^ γ - 1 ≤ γ * v ^ γ * Real.log v := by
  rw [Real.rpow_def_of_pos hv]
  nlinarith [exp_sub_one_le_mul_exp (Real.log v * γ)]

/-- A squared coefficient times `log d` equals its normalized absolute value. -/
lemma coefficient_sq_mul_log {P d : ℕ} (hP : 1 < P) (hd : 1 < d) :
    coefficient P d ^ 2 * Real.log d = |coefficient P d| / normalizer P := by
  rw [abs_of_neg (coefficient_neg hP hd), coefficient, if_neg (ne_of_gt hd)]
  have hB := ne_of_gt (normalizer_pos hP)
  have hlog := ne_of_gt (Real.log_pos (by exact_mod_cast hd : (1 : ℝ) < d))
  field_simp

/-- Control the change in the squared moment by the absolute moment. -/
lemma coefficientMoment_sub_le {P : ℕ} (hP : 1 < P) (γ : ℝ) :
    coefficientMoment P γ - coefficientMoment P 0 ≤
      (γ / normalizer P) * coefficientAbsMoment P γ := by
  rw [coefficientMoment, coefficientMoment_zero, ← Finset.sum_sub_distrib,
    ← Finset.sum_erase_add _ _ (Nat.one_mem_divisors.mpr (by omega : P ≠ 0))]
  simp only [Nat.cast_one, Real.one_rpow, Nat.totient_one, mul_one, div_one,
    sub_self, add_zero]
  unfold coefficientAbsMoment
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro d hd
  have hd' := one_lt_of_mem_divisors_erase_one hd
  calc
    coefficient P d ^ 2 * (d : ℝ) ^ γ / d.totient -
        coefficient P d ^ 2 / d.totient =
        coefficient P d ^ 2 * ((d : ℝ) ^ γ - 1) / d.totient := by ring
    _ ≤ coefficient P d ^ 2 * (γ * (d : ℝ) ^ γ * Real.log d) / d.totient :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left
          (rpow_sub_one_le (by exact_mod_cast (zero_lt_one.trans hd'))) (sq_nonneg _))
        (Nat.cast_nonneg _)
    _ = (coefficient P d ^ 2 * Real.log d) * (γ * (d : ℝ) ^ γ) / d.totient := by ring
    _ = (γ / normalizer P) * (|coefficient P d| * (d : ℝ) ^ γ / d.totient) := by
      rw [coefficient_sq_mul_log hP hd']
      ring

/-- Rankin's tail estimate, in the finite form needed for (3.10). -/
theorem moment_tail_le {α : Type*} (s : Finset α) (f v : α → ℝ) (D β : ℝ)
    (hD : 0 < D) (hβ : 0 ≤ β) (hf : ∀ a ∈ s, 0 ≤ f a)
    (hv : ∀ a ∈ s, 0 ≤ v a) :
    (∑ a ∈ s.filter (fun a => D < v a), f a) ≤
      D ^ (-β) * ∑ a ∈ s, f a * (v a) ^ β := by
  rw [Real.rpow_neg hD.le, ← div_eq_inv_mul]
  apply (le_div_iff₀ (Real.rpow_pos_of_pos hD β)).mpr
  rw [Finset.sum_mul]
  calc
    _ ≤ ∑ a ∈ s.filter (fun a => D < v a), f a * (v a) ^ β := by
      apply Finset.sum_le_sum
      intro a ha
      obtain ⟨has, hav⟩ := Finset.mem_filter.mp ha
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow hD.le hav.le hβ) (hf a has)
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun a ha _ => mul_nonneg (hf a ha) (Real.rpow_nonneg (hv a ha) _))

/-- Divisors regarded as a finite index type. -/
abbrev DivisorIndex (P : ℕ) := {d : ℕ // d ∈ P.divisors}

/-- Tuples of `k` divisors of `P`. -/
abbrev DivisorTuple (P k : ℕ) := Fin k → DivisorIndex P

/-- The product of the divisors in a tuple. -/
def tupleProduct {P k : ℕ} (r : DivisorTuple P k) : ℕ := ∏ i, (r i).val

/-- The common truncated region R_k of (3.3). -/
def tupleRegion (P k : ℕ) (D : ℝ) : Finset (DivisorTuple P k) := by
  classical
  exact Finset.univ.filter fun r =>
    (∀ i j, i ≠ j → Nat.Coprime (r i).val (r j).val) ∧ (tupleProduct r : ℝ) ≤ D

/-- The diagonal mass attached to one tuple in (3.9). -/
def tupleMass {P k : ℕ} (r : DivisorTuple P k) : ℝ :=
  ∏ i, coefficient P (r i).val ^ 2 / ((r i).val.totient : ℝ)

/-- The diagonal mass of a divisor tuple is nonnegative. -/
lemma tupleMass_nonneg {P k : ℕ} (r : DivisorTuple P k) : 0 ≤ tupleMass r := by
  unfold tupleMass
  positivity

/-- Rewrite a sum over divisor indices as a sum over the divisor finset. -/
lemma sum_divisorIndex (P : ℕ) (f : ℕ → ℝ) :
    (∑ d : DivisorIndex P, f d.val) = ∑ d ∈ P.divisors, f d := by
  exact Finset.sum_attach P.divisors f

/-- The total tuple mass is the `k`th power of the zero coefficient moment. -/
lemma sum_tupleMass (P k : ℕ) :
    (∑ r : DivisorTuple P k, tupleMass r) = coefficientMoment P 0 ^ k := by
  classical
  unfold tupleMass
  rw [← Fintype.prod_sum (fun (_ : Fin k) (d : DivisorIndex P) =>
    coefficient P d.val ^ 2 / (d.val.totient : ℝ))]
  rw [sum_divisorIndex P (fun d => coefficient P d ^ 2 / (d.totient : ℝ)),
    ← coefficientMoment_zero]
  simp

/-- The tilted tuple mass factors as a power of the coefficient moment. -/
lemma sum_tupleMass_mul_rpow (P k : ℕ) (γ : ℝ) :
    (∑ r : DivisorTuple P k, tupleMass r * (tupleProduct r : ℝ) ^ γ) =
      coefficientMoment P γ ^ k := by
  classical
  unfold tupleMass tupleProduct
  simp_rw [Nat.cast_prod,
    ← Real.finsetProd_rpow _ _ (fun _ _ => Nat.cast_nonneg _),
    ← Finset.prod_mul_distrib, div_mul_eq_mul_div]
  rw [← Fintype.prod_sum (fun (_ : Fin k) (d : DivisorIndex P) =>
    coefficient P d.val ^ 2 * (d.val : ℝ) ^ γ / (d.val.totient : ℝ))]
  rw [sum_divisorIndex P (fun d => coefficient P d ^ 2 * (d : ℝ) ^ γ / d.totient)]
  simp [coefficientMoment]

/-- The first inequality in (3.10), with no asymptotic assumptions. -/
theorem diagonal_tail_le (P k : ℕ) {D β : ℝ} (hD : 0 < D) (hβ : 0 ≤ β) :
    (∑ r ∈ (Finset.univ : Finset (DivisorTuple P k)).filter
        (fun r => D < (tupleProduct r : ℝ)), tupleMass r) ≤
      D ^ (-β) * coefficientMoment P β ^ k := by
  classical
  simpa only [sum_tupleMass_mul_rpow] using
    moment_tail_le Finset.univ tupleMass (fun r : DivisorTuple P k => (tupleProduct r : ℝ))
      D β hD hβ (fun r _ => tupleMass_nonneg r) (fun r _ => Nat.cast_nonneg _)

/-- Convert an additive bound into an exponential bound on powers. -/
lemma pow_le_mul_exp {A B t : ℝ} (hA : 1 ≤ A) (hB : 0 ≤ B)
    (ht : 0 ≤ t) (hBA : B ≤ A + t) (k : ℕ) :
    B ^ k ≤ A ^ k * Real.exp ((k : ℝ) * t) := by
  have hbase : B ≤ A * Real.exp t := by
    have he := Real.add_one_le_exp t
    nlinarith [mul_nonneg (sub_nonneg.mpr hA) ht,
      mul_le_mul_of_nonneg_left he (by linarith : 0 ≤ A)]
  calc
    B ^ k ≤ (A * Real.exp t) ^ k := pow_le_pow_left₀ hB hbase k
    _ = A ^ k * Real.exp ((k : ℝ) * t) := by rw [mul_pow, Real.exp_nat_mul]

/-- Bound powers of a tilted coefficient moment relative to the zero moment. -/
lemma coefficientMoment_pow_le {P : ℕ} (hP : 1 < P) {C γ : ℝ}
    (hC : 0 ≤ C) (hγ : 0 ≤ γ)
    (hM : coefficientAbsMoment P γ ≤ C * normalizer P) (k : ℕ) :
    coefficientMoment P γ ^ k ≤
      coefficientMoment P 0 ^ k * Real.exp ((k : ℝ) * C * γ) := by
  have hP0 : P ≠ 0 := by omega
  have hB := normalizer_pos hP
  have hbound : coefficientMoment P γ - coefficientMoment P 0 ≤ C * γ := by
    calc
      _ ≤ γ / normalizer P * coefficientAbsMoment P γ := coefficientMoment_sub_le hP γ
      _ ≤ γ / normalizer P * (C * normalizer P) :=
        mul_le_mul_of_nonneg_left hM (div_nonneg hγ hB.le)
      _ = C * γ := by field_simp
  simpa [mul_assoc] using pow_le_mul_exp (coefficientMoment_ge_one hP0 0)
    (zero_le_one.trans (coefficientMoment_ge_one hP0 γ)) (mul_nonneg hC hγ)
    (by linarith : coefficientMoment P γ ≤ coefficientMoment P 0 + C * γ) k

end

end LongGapsBetweenPrimes
