/- GID: D5/S3/VertexAlgebra/PolynomialFockDerivativePowerOPE
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/PolynomialFockDerivativePowerOPE
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual derivative-labelled Fock power-state coefficients at every integer mode. -/

/-
proof_shape: derivative_power_state_coefficients: content
escape_witness: Actual right-nested divided-current words are evaluated on
arbitrary powers of a separately labelled variable. The creation branch has
an explicit statewise cutoff and is identified with an independently defined
weighted power-series convolution. The annihilation branch selects its
actual oscillator mode; supported induction combines the two branches.
admission_basis: escape-witness
Direct frozen dependency:
  D5/S3/VertexAlgebra/PolynomialFockStateField.stateField_creation
  (sha256:46200407e1173bbe787bc4da0e17820fa32f6aaebaf0d5bb8ebd7b968584ece6).
Matsuo--Nagatomo, hep-th/9704060v1, Sections 2.1--2.3, supplies classical
free-boson normalization and contraction background, not this exact Lean
realization formula. No analytic or Monster realization is asserted.
-/

import D5.S3.VertexAlgebra.PolynomialFockStateField
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Data.Nat.Choose.Sum

set_option autoImplicit false

namespace D5.S3.VertexAlgebra.PolynomialFockDerivativePowerOPE

open MvPolynomial
open D5.S3.VertexAlgebra.PolynomialFockSugawaraSupport
open D5.S3.VertexAlgebra.PolynomialFockStateField
open D5.S3.VertexAlgebra.FieldNormalProduct
open scoped VertexOperator

noncomputable def A (a : ℕ) : PowerSeries Fock :=
  PowerSeries.mk fun j => (((j + a).choose a : ℕ) : ℂ) • (X (j + a) : Fock)

noncomputable def B (a r : ℕ) (d : ℤ) : Fock :=
  if 0 ≤ d then PowerSeries.coeff d.toNat (A a ^ r) else 0

noncomputable def c (a b : ℕ) : ℂ :=
  (-1 : ℂ) ^ a * ((b + 1 : ℕ) : ℂ) * (((a + b + 1).choose a : ℕ) : ℂ)

set_option backward.isDefEq.respectTransparency false in
/-- All integer coefficients of the actual two-labelled derivative power-state field. -/
theorem derivative_power_state_coefficients (a b p q : ℕ) (n : ℤ) :
    ((Y ((X a : Fock) ^ p)) [[n]]) ((X b : Fock) ^ q) =
      ∑ k ∈ Finset.range (min p q + 1),
        ((((p.choose k * q.descFactorial k : ℕ) : ℂ) * c a b ^ k) •
          (B a (p - k) (((a + b + 2 : ℕ) : ℤ) * (k : ℤ) - n - 1) *
            (X b : Fock) ^ (q - k))) := by
  classical
  -- The actual monomial-basis construction supplies the nested word.
  have fieldWord (r : ℕ) : Y ((X a : Fock) ^ r) = wordField (List.replicate r a) := by
    rw [X_pow_eq_monomial]
    have sorted : occurrences (Finsupp.single a r) = List.replicate r a := by
      rw [occurrences, Finsupp.toMultiset_single]
      induction r with
      | zero => simp
      | succ r ih =>
        rw [succ_nsmul, add_comm, Multiset.singleton_add]
        have eq := Multiset.sort_cons (a := a) (s := r • ({a} : Multiset ℕ))
          (r := (· ≤ ·)) (by
            intro other member
            rw [Multiset.mem_singleton.mp (Multiset.mem_of_mem_nsmul member)])
        rw [eq, ih, List.replicate_succ]
    simpa only [Y, coe_basisMonomials, sorted] using
      (basisMonomials ℕ ℂ).constr_basis ℂ
        (fun exponents => wordField (occurrences exponents)) (Finsupp.single a r)
  have currentModes (i : ℤ) : (current [[i]]) = mode i := by
    rw [current, VertexOperator.ncoeff_of_coeff]
    rw [show -(-i - 1) - 1 = i by omega]
  have derivativeModes (i : ℤ) :
      ((dividedDerivative a current) [[i]]) =
        ((Ring.choose (-i - 1 + a) a : ℤ) : ℂ) • mode (i - a) := by
    apply LinearMap.ext
    intro vector
    change Ring.choose (-i - 1 + a) a •
      HVertexOperator.coeff current (-i - 1 + a) vector = _
    rw [VertexOperator.coeff_eq_ncoeff, currentModes]
    rw [show -(-i - 1 + a) - 1 = i - a by omega]
    simp only [LinearMap.smul_apply, Int.cast_smul_eq_zsmul]
  have nextField (r : ℕ) : Y ((X a : Fock) ^ (r + 1)) =
      (normalMinusOne (dividedDerivative a current) (Y ((X a : Fock) ^ r))).1 := by
    rw [fieldWord, List.replicate_succ, wordField, ← fieldWord]
  have negativeDerivative (j : ℕ) (v : Fock) :
      ((dividedDerivative a current) [[-(j : ℤ) - 1]]) v =
        PowerSeries.coeff j (A a) * v := by
    rw [derivativeModes, LinearMap.smul_apply]
    rw [show -(-(j : ℤ) - 1) - 1 + a = ((j + a : ℕ) : ℤ) by omega,
      Ring.choose_natCast]
    rw [show -(j : ℤ) - 1 - a = Int.negSucc (j + a) by omega]
    simp [A, mode, create]
  have positiveMode (j s : ℕ) : mode (j : ℤ) ((X b : Fock) ^ s) =
      if j = b + 1 then ((s : ℂ) * (b + 1 : ℂ)) •
        (X b : Fock) ^ (s - 1) else 0 := by
    cases j with
    | zero => simp [mode]
    | succ j =>
      change (j + 1 : ℂ) • pderiv j ((X b : Fock) ^ s) = _
      rw [pderiv_pow, pderiv_X]
      by_cases h : j = b
      · subst j
        simp [MvPolynomial.smul_eq_C_mul, mul_comm, mul_left_comm, mul_assoc]
      · simp [h, Ne.symm h]
  have positiveDerivative (j s : ℕ) :
      ((dividedDerivative a current) [[(j : ℤ)]]) ((X b : Fock) ^ s) =
        if j = a + b + 1 then ((s : ℂ) * c a b) •
          (X b : Fock) ^ (s - 1) else 0 := by
    rw [derivativeModes, LinearMap.smul_apply]
    by_cases small : j < a
    · have parameter : -(j : ℤ) - 1 + a = ((a - j - 1 : ℕ) : ℤ) := by omega
      rw [parameter, Ring.choose_natCast, Nat.choose_eq_zero_of_lt (by omega)]
      simp [show j ≠ a + b + 1 by omega]
    · have shift : (j : ℤ) - a = ((j - a : ℕ) : ℤ) := by omega
      rw [shift, positiveMode]
      by_cases selected : j = a + b + 1
      · subst j
        rw [if_pos (by omega), if_pos rfl]
        rw [show -((a + b + 1 : ℕ) : ℤ) - 1 + a = -((b : ℤ) + 2) by omega,
          Ring.choose_neg,
          show (b : ℤ) + 2 + a - 1 = ((a + b + 1 : ℕ) : ℤ) by omega,
          Ring.choose_natCast]
        simp only [Units.smul_def, smul_eq_mul, Int.cast_mul,
          Int.cast_negOnePow_natCast, Int.cast_natCast, smul_smul]
        congr 1
        simp only [c, Nat.cast_add, Nat.cast_one]
        ring
      · rw [if_neg (by omega), if_neg selected, smul_zero]
  have bNegative (r : ℕ) (d : ℤ) (h : d < 0) : B a r d = 0 := by
    simp [B, show ¬0 ≤ d by omega]
  have bZero (d : ℤ) : B a 0 d = if d = 0 then 1 else 0 := by
    by_cases hd : 0 ≤ d
    · rw [B, if_pos hd, pow_zero, PowerSeries.coeff_one]
      have eq : d.toNat = 0 ↔ d = 0 := by omega
      simp only [eq]
    · rw [B, if_neg hd, if_neg (by omega)]
  -- A finite weighted convolution, including negative extended coefficients.
  have convolution (r : ℕ) (d : ℤ) (N : ℕ) (hN : d < N) :
      ∑ j ∈ Finset.range N, PowerSeries.coeff j (A a) * B a r (d - j) =
        B a (r + 1) d := by
    by_cases hd : 0 ≤ d
    · obtain ⟨t, rfl⟩ := Int.eq_ofNat_of_zero_le hd
      have small : t + 1 ≤ N := by omega
      rw [← Finset.sum_subset (Finset.range_mono small)]
      · simp only [B, Int.natCast_nonneg, ↓reduceIte, Int.toNat_natCast,
          pow_succ', PowerSeries.coeff_mul,
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
  let M : ℕ := a + b + 2
  have recurrence (r s : ℕ) (i : ℤ) :
      ((Y ((X a : Fock) ^ (r + 1))) [[i]]) ((X b : Fock) ^ s) =
        (∑ᶠ j : ℕ, PowerSeries.coeff j (A a) *
          (((Y ((X a : Fock) ^ r)) [[i + j]]) ((X b : Fock) ^ s))) +
        s • (c a b • (((Y ((X a : Fock) ^ r)) [[i - M]])
          ((X b : Fock) ^ (s - 1)))) := by
    rw [nextField,
      (normalMinusOne (dividedDerivative a current) (Y ((X a : Fock) ^ r))).2]
    simp_rw [negativeDerivative]
    congr 1
    by_cases hs : s = 0
    · subst s
      simp only [pow_zero, zero_smul]
      have vanish (j : ℕ) : ((dividedDerivative a current) [[(j : ℤ)]]) (1 : Fock) = 0 := by
        simpa using positiveDerivative j 0
      simp [vanish]
    · rw [finsum_eq_single _ (a + b + 1)]
      · rw [positiveDerivative, if_pos rfl, map_smul, mul_smul]
        rw [show i - ((a + b + 1 : ℕ) : ℤ) - 1 = i - M by dsimp [M]; omega]
        exact Nat.cast_smul_eq_nsmul ℂ s _
      · intro j hj
        rw [positiveDerivative, if_neg hj, map_zero]
  -- Supported induction evaluates the actual word before truncating the pairing count.
  have expanded : ∀ r s : ℕ, ∀ i : ℤ,
      ((Y ((X a : Fock) ^ r)) [[i]]) ((X b : Fock) ^ s) =
        ∑ k ∈ Finset.range (r + 1), r.choose k •
          (s.descFactorial k • (c a b ^ k •
            (B a (r - k) ((M : ℤ) * (k : ℤ) - i - 1) *
              (X b : Fock) ^ (s - k)))) := by
    intro r
    induction r with
    | zero =>
      intro s i
      rw [pow_zero, stateField_creation.1]
      rw [identityField, VertexOperator.ncoeff_of_coeff]
      simp only [Nat.reduceAdd, Finset.sum_range_one, Nat.choose_zero_right,
        Nat.descFactorial_zero, pow_zero, one_smul, Nat.sub_zero, Nat.cast_zero,
        mul_zero, zero_sub, Nat.zero_sub]
      rw [bZero]
      split_ifs <;> simp
    | succ r ih =>
      intro s i
      let N : ℕ := ((M : ℤ) * (r : ℤ) - i).toNat + 1
      have bound (k : ℕ) (hk : k ≤ r) : (M : ℤ) * k ≤ (M : ℤ) * r :=
        mul_le_mul_of_nonneg_left (by exact_mod_cast hk) (by positivity)
      have cutoff (j : ℕ) (hj : j ∉ Finset.range N) :
          ((Y ((X a : Fock) ^ r)) [[i + j]]) ((X b : Fock) ^ s) = 0 := by
        rw [ih]
        apply Finset.sum_eq_zero
        intro k hk
        have hk' : k ≤ r := by simpa using hk
        have hj' : N ≤ j := by simpa using hj
        have productBound := bound k hk'
        have negative : (M : ℤ) * k - (i + j) - 1 < 0 := by
          dsimp [N] at hj'
          omega
        rw [bNegative _ _ negative, zero_mul, smul_zero, smul_zero, smul_zero]
      have firstSum :
          (∑ᶠ j : ℕ, PowerSeries.coeff j (A a) *
            (((Y ((X a : Fock) ^ r)) [[i + j]]) ((X b : Fock) ^ s))) =
          ∑ k ∈ Finset.range (r + 1), r.choose k •
            (s.descFactorial k • (c a b ^ k •
              (B a (r + 1 - k) ((M : ℤ) * k - i - 1) *
                (X b : Fock) ^ (s - k)))) := by
        rw [finsum_eq_sum_of_support_subset _ (s := Finset.range N) (by
          intro j hj
          by_contra h
          exact hj (by dsimp only; rw [cutoff j h, mul_zero]))]
        simp_rw [ih, Finset.mul_sum, mul_smul_comm]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro k hk
        have hk' : k ≤ r := by simpa using hk
        have productBound := bound k hk'
        simp_rw [← mul_assoc]
        rw [← Finset.smul_sum, ← Finset.smul_sum, ← Finset.smul_sum, ← Finset.sum_mul]
        simp_rw [show ∀ j : ℕ, (M : ℤ) * k - (i + j) - 1 =
          (M : ℤ) * k - i - 1 - j by intro j; omega]
        rw [convolution (r - k) ((M : ℤ) * k - i - 1) N (by dsimp [N]; omega)]
        rw [show r - k + 1 = r + 1 - k by omega]
      rw [recurrence, firstSum, ih, Finset.smul_sum]
      have pascal := Finset.sum_choose_succ_nsmul
        (fun k t => s.descFactorial k • (c a b ^ k •
          (B a t ((M : ℤ) * k - i - 1) * (X b : Fock) ^ (s - k)))) r
      rw [pascal]
      congr 1
      rw [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      by_cases hs : s = 0
      · subst s
        simp
      · obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hs
        simp only [Nat.succ_sub_succ_eq_sub, Nat.sub_zero]
        rw [smul_comm (c a b) (r.choose k), smul_comm t.succ (r.choose k)]
        congr 1
        rw [smul_comm (c a b) (t.descFactorial k), ← mul_smul,
          ← Nat.succ_descFactorial_succ, pow_succ', mul_smul]
        congr 2
        congr 1
        push_cast
        ring
  rw [expanded]
  have truncation :
      (∑ k ∈ Finset.range (p + 1), p.choose k •
        (q.descFactorial k • (c a b ^ k •
          (B a (p - k) ((M : ℤ) * k - n - 1) * (X b : Fock) ^ (q - k))))) =
      ∑ k ∈ Finset.range (min p q + 1), p.choose k •
        (q.descFactorial k • (c a b ^ k •
          (B a (p - k) ((M : ℤ) * k - n - 1) * (X b : Fock) ^ (q - k)))) := by
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
    smul_smul, smul_smul, ← Nat.cast_mul]

end D5.S3.VertexAlgebra.PolynomialFockDerivativePowerOPE
