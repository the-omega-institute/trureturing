/- GID: D5/S3/VertexAlgebra/PolynomialFockPowerOPE
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/PolynomialFockPowerOPE
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual polynomial Fock power-state coefficients at every integer mode. -/

/-
proof_shape: power_state_coefficients: content
escape_witness: The actual right-nested current word is evaluated on every
power of X_0. Its creation branch has an explicit statewise cutoff and is
identified with the independent creation-series convolution. The annihilation
branch selects only mode one; Pascal and falling-factorial counts combine
the two branches, including the zero-power boundary.
admission_basis: escape-witness
The content is the actual-output calculation, not abstract Wick
algebra or a commutator specialization.
Direct frozen dependency:
  D5/S3/VertexAlgebra/PolynomialFockStateField.stateField_creation
  (sha256:46200407e1173bbe787bc4da0e17820fa32f6aaebaf0d5bb8ebd7b968584ece6).
Matsuo--Nagatomo Sections 1.2 and 1.4
supply the classical coefficient conventions, not this Lean realization proof.
-/

import D5.S3.VertexAlgebra.PolynomialFockStateField
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Data.Nat.Choose.Sum

set_option autoImplicit false

namespace D5.S3.VertexAlgebra.PolynomialFockPowerOPE

open MvPolynomial
open D5.S3.VertexAlgebra.PolynomialFockSugawaraSupport
open D5.S3.VertexAlgebra.PolynomialFockStateField
open D5.S3.VertexAlgebra.FieldNormalProduct
open scoped VertexOperator

noncomputable def A : PowerSeries Fock := PowerSeries.mk fun j => X j

noncomputable def B (r : ℕ) (d : ℤ) : Fock :=
  if 0 ≤ d then PowerSeries.coeff d.toNat (A ^ r) else 0

set_option backward.isDefEq.respectTransparency false in
/-- All integer coefficients of the actual power-state field on a power state. -/
theorem power_state_coefficients (p q : ℕ) (n : ℤ) :
    ((Y ((X 0 : Fock) ^ p)) [[n]]) ((X 0 : Fock) ^ q) =
      ∑ k ∈ Finset.range (min p q + 1),
        ((p.choose k * q.descFactorial k : ℕ) : ℂ) •
          (B (p - k) (2 * (k : ℤ) - n - 1) * (X 0 : Fock) ^ (q - k)) := by
  classical
  have fieldWord (r : ℕ) : Y ((X 0 : Fock) ^ r) = wordField (List.replicate r 0) := by
    rw [X_pow_eq_monomial]
    have sorted : occurrences (Finsupp.single 0 r) = List.replicate r 0 := by
      rw [occurrences, Finsupp.toMultiset_single]
      induction r with
      | zero => simp
      | succ r ih =>
        rw [succ_nsmul, add_comm, Multiset.singleton_add]
        have eq := Multiset.sort_cons (a := (0 : ℕ)) (s := r • ({0} : Multiset ℕ))
          (r := (· ≤ ·)) (by intro b hb; exact Nat.zero_le b)
        rw [eq, ih, List.replicate_succ]
    simpa only [Y, coe_basisMonomials, sorted] using
      (basisMonomials ℕ ℂ).constr_basis ℂ
        (fun exponents => wordField (occurrences exponents)) (Finsupp.single 0 r)
  have currentModes (i : ℤ) : (current [[i]]) = mode i := by
    rw [current, VertexOperator.ncoeff_of_coeff]
    rw [show -(-i - 1) - 1 = i by omega]
  have derivativeZero : dividedDerivative 0 current = current := by
    apply VertexOperator.ext
    intro v
    simp [dividedDerivative]
  have nextField (r : ℕ) : Y ((X 0 : Fock) ^ (r + 1)) =
      (normalMinusOne current (Y ((X 0 : Fock) ^ r))).1 := by
    rw [fieldWord, List.replicate_succ, wordField, derivativeZero, ← fieldWord]
  have negativeMode (j : ℕ) (v : Fock) : mode (-(j : ℤ) - 1) v = X j * v := by
    rw [show -(j : ℤ) - 1 = Int.negSucc j by omega]
    rfl
  have positiveMode (j s : ℕ) : mode (j : ℤ) ((X 0 : Fock) ^ s) =
      if j = 1 then (s : ℂ) • (X 0 : Fock) ^ (s - 1) else 0 := by
    cases j with
    | zero => simp [mode]
    | succ j =>
      change (j + 1 : ℂ) • pderiv j ((X 0 : Fock) ^ s) =
        if j + 1 = 1 then (s : ℂ) • (X 0 : Fock) ^ (s - 1) else 0
      rw [pderiv_pow, pderiv_X]
      by_cases h : j = 0
      · subst j
        simp [MvPolynomial.smul_eq_C_mul]
      · simp [h, Ne.symm h]
  have bNegative (r : ℕ) (d : ℤ) (h : d < 0) : B r d = 0 := by
    simp [B, show ¬0 ≤ d by omega]
  have bZero (d : ℤ) : B 0 d = if d = 0 then 1 else 0 := by
    by_cases hd : 0 ≤ d
    · rw [B, if_pos hd, pow_zero, PowerSeries.coeff_one]
      have eq : d.toNat = 0 ↔ d = 0 := by omega
      simp only [eq]
    · rw [B, if_neg hd, if_neg (by omega)]
  have convolution (r : ℕ) (d : ℤ) (N : ℕ) (hN : d < N) :
      ∑ j ∈ Finset.range N, (X j : Fock) * B r (d - j) = B (r + 1) d := by
    by_cases hd : 0 ≤ d
    · obtain ⟨t, rfl⟩ := Int.eq_ofNat_of_zero_le hd
      have small : t + 1 ≤ N := by omega
      rw [← Finset.sum_subset (Finset.range_mono small)]
      · simp only [B, Int.natCast_nonneg, ↓reduceIte, Int.toNat_natCast,
          pow_succ', PowerSeries.coeff_mul, A, PowerSeries.coeff_mk,
          Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
        apply Finset.sum_congr rfl
        intro j hj
        have hjt : j ≤ t := by simpa using hj
        simp [Int.toNat_natCast, Nat.not_lt.mpr hjt]
      · intro j hjN hjt
        have htj : t < j := by simpa using hjt
        rw [bNegative r ((t : ℤ) - j) (by omega), mul_zero]
    · rw [bNegative (r + 1) d (by omega)]
      apply Finset.sum_eq_zero
      intro j hj
      rw [bNegative r (d - j) (by omega), mul_zero]
  have recurrence (r s : ℕ) (i : ℤ) :
      ((Y ((X 0 : Fock) ^ (r + 1))) [[i]]) ((X 0 : Fock) ^ s) =
        (∑ᶠ j : ℕ, (X j : Fock) *
          (((Y ((X 0 : Fock) ^ r)) [[i + j]]) ((X 0 : Fock) ^ s))) +
        s • (((Y ((X 0 : Fock) ^ r)) [[i - 2]]) ((X 0 : Fock) ^ (s - 1))) := by
    rw [nextField, (normalMinusOne current (Y ((X 0 : Fock) ^ r))).2]
    simp_rw [currentModes, negativeMode]
    congr 1
    by_cases hs : s = 0
    · subst s
      simp only [pow_zero, zero_smul]
      have vanish (j : ℕ) : mode (j : ℤ) (1 : Fock) = 0 := by
        simpa using positiveMode j 0
      simp [vanish]
    · rw [finsum_eq_single _ 1]
      · rw [positiveMode, if_pos rfl, map_smul]
        rw [show i - (1 : ℕ) - 1 = i - 2 by omega]
        exact Nat.cast_smul_eq_nsmul ℂ s _
      · intro j hj
        rw [positiveMode, if_neg hj, map_zero]
  have expanded : ∀ r s : ℕ, ∀ i : ℤ,
      ((Y ((X 0 : Fock) ^ r)) [[i]]) ((X 0 : Fock) ^ s) =
        ∑ k ∈ Finset.range (r + 1), r.choose k •
          (s.descFactorial k •
            (B (r - k) (2 * (k : ℤ) - i - 1) * (X 0 : Fock) ^ (s - k))) := by
    intro r
    induction r with
    | zero =>
      intro s i
      rw [pow_zero, stateField_creation.1]
      rw [identityField, VertexOperator.ncoeff_of_coeff]
      simp only [Nat.reduceAdd, Finset.sum_range_one, Nat.choose_zero_right, Nat.descFactorial_zero,
        one_smul, Nat.sub_zero, Nat.cast_zero, mul_zero, zero_sub, Nat.zero_sub]
      rw [bZero]
      split_ifs <;> simp
    | succ r ih =>
      intro s i
      let N : ℕ := (2 * (r : ℤ) - i).toNat + 1
      have cutoff (j : ℕ) (hj : j ∉ Finset.range N) :
          ((Y ((X 0 : Fock) ^ r)) [[i + j]]) ((X 0 : Fock) ^ s) = 0 := by
        rw [ih]
        apply Finset.sum_eq_zero
        intro k hk
        have hk' : k ≤ r := by simpa using hk
        have hj' : N ≤ j := by simpa using hj
        have negative : 2 * (k : ℤ) - (i + j) - 1 < 0 := by dsimp [N] at hj'; omega
        rw [bNegative _ _ negative, zero_mul, smul_zero, smul_zero]
      have firstSum :
          (∑ᶠ j : ℕ, (X j : Fock) *
            (((Y ((X 0 : Fock) ^ r)) [[i + j]]) ((X 0 : Fock) ^ s))) =
          ∑ k ∈ Finset.range (r + 1), r.choose k •
            (s.descFactorial k •
              (B (r + 1 - k) (2 * (k : ℤ) - i - 1) * (X 0 : Fock) ^ (s - k))) := by
        rw [finsum_eq_sum_of_support_subset _ (s := Finset.range N) (by
          intro j hj
          by_contra h
          exact hj (by dsimp only; rw [cutoff j h, mul_zero]))]
        simp_rw [ih, Finset.mul_sum, mul_smul_comm]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro k hk
        have hk' : k ≤ r := by simpa using hk
        simp_rw [← mul_assoc]
        rw [← Finset.smul_sum, ← Finset.smul_sum, ← Finset.sum_mul]
        simp_rw [show ∀ j : ℕ, 2 * (k : ℤ) - (i + j) - 1 =
          2 * (k : ℤ) - i - 1 - j by intro j; omega]
        rw [convolution (r - k) (2 * (k : ℤ) - i - 1) N (by dsimp [N]; omega)]
        rw [show r - k + 1 = r + 1 - k by omega]
      rw [recurrence, firstSum]
      rw [ih, Finset.smul_sum]
      have pascal := Finset.sum_choose_succ_nsmul
        (fun k t => s.descFactorial k •
          (B t (2 * (k : ℤ) - i - 1) * (X 0 : Fock) ^ (s - k))) r
      rw [pascal]
      congr 1
      apply Finset.sum_congr rfl
      intro k hk
      by_cases hs : s = 0
      · subst s
        simp
      · obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hs
        simp only [Nat.succ_sub_succ_eq_sub, Nat.sub_zero]
        rw [smul_comm (t + 1) (r.choose k)]
        congr 1
        rw [← mul_smul, ← Nat.succ_descFactorial_succ]
        congr 2
        congr 1
        omega
  rw [expanded]
  have truncation :
      (∑ k ∈ Finset.range (p + 1), p.choose k •
        (q.descFactorial k •
          (B (p - k) (2 * (k : ℤ) - n - 1) * (X 0 : Fock) ^ (q - k)))) =
      ∑ k ∈ Finset.range (min p q + 1), p.choose k •
        (q.descFactorial k •
          (B (p - k) (2 * (k : ℤ) - n - 1) * (X 0 : Fock) ^ (q - k))) := by
    symm
    apply Finset.sum_subset (Finset.range_mono (show min p q + 1 ≤ p + 1 by omega))
    intro k hk hsmall
    have hk' : k ≤ p := by simpa using hk
    have hq : q < k := by simp only [Finset.mem_range] at hsmall; omega
    rw [Nat.descFactorial_of_lt hq, zero_smul, smul_zero]
  rw [truncation]
  apply Finset.sum_congr rfl
  intro k hk
  rw [← Nat.cast_smul_eq_nsmul ℂ, ← Nat.cast_smul_eq_nsmul ℂ,
    smul_smul, ← Nat.cast_mul]

end D5.S3.VertexAlgebra.PolynomialFockPowerOPE
