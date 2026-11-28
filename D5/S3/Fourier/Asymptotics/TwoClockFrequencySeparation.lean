/- GID: D5/S3/Fourier/Asymptotics/TwoClockFrequencySeparation
   generality: I
   mirror-B: D5/B/S3/Fourier/Asymptotics/TwoClockFrequencySeparation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The two clock differences have an explicit exponential frequency separation. -/

import D5.S3.Factorization.Galois.SquareRootArithmetic
import D5.S3.Fourier.Asymptotics.AlgebraicPhaseSeparation
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic.NormNum.LegendreSymbol
import OmegaBuild.Commands

/-! Arithmetic separation for the two phase differences in the nineteen-site model. -/

compile_only_with_mathlib

namespace D5.S3.Fourier.Asymptotics.TwoClockFrequencySeparation

open Polynomial
open scoped BigOperators IntermediateField NumberField

noncomputable section

private theorem quadraticIntegral {r : ℂ} (d : ℚ)
    (hr : r ^ 2 = algebraMap ℚ ℂ d) : IsIntegral ℚ r :=
  ⟨X ^ 2 - C d, monic_X_pow_sub_C _ (by decide), by simp [hr]⟩

private theorem quadraticDegree {r : ℂ} (d : ℚ)
    (hr : r ^ 2 = algebraMap ℚ ℂ d) : Module.finrank ℚ ℚ⟮r⟯ ≤ 2 := by
  rw [IntermediateField.adjoin.finrank (quadraticIntegral d hr)]
  have hdvd : minpoly ℚ r ∣ X ^ 2 - C d := minpoly.dvd ℚ r (by simp [hr])
  exact (natDegree_le_of_dvd hdvd (X_pow_sub_C_ne_zero (by decide) _)).trans
    (by rw [natDegree_X_pow_sub_C])

private theorem tripleDegree {r s t : ℂ} (d e f : ℚ)
    (hr : r ^ 2 = algebraMap ℚ ℂ d) (hs : s ^ 2 = algebraMap ℚ ℂ e)
    (ht : t ^ 2 = algebraMap ℚ ℂ f) :
    Module.finrank ℚ ↥(ℚ⟮r⟯ ⊔ ℚ⟮s⟯ ⊔ ℚ⟮t⟯ : IntermediateField ℚ ℂ) ≤ 8 := by
  calc
    _ ≤ Module.finrank ℚ ↥(ℚ⟮r⟯ ⊔ ℚ⟮s⟯ : IntermediateField ℚ ℂ) *
        Module.finrank ℚ ℚ⟮t⟯ := IntermediateField.finrank_sup_le _ _
    _ ≤ (Module.finrank ℚ ℚ⟮r⟯ * Module.finrank ℚ ℚ⟮s⟯) * Module.finrank ℚ ℚ⟮t⟯ :=
      Nat.mul_le_mul_right _ (IntermediateField.finrank_sup_le _ _)
    _ ≤ 8 := Nat.mul_le_mul (Nat.mul_le_mul (quadraticDegree d hr) (quadraticDegree e hs))
      (quadraticDegree f ht)

private def rad (d : ℝ) : ℂ := (Real.sqrt (d * (3468 - d)) : ℂ) * Complex.I

private theorem rad_sq (d : ℝ) (h : 0 ≤ d * (3468 - d)) :
    rad d ^ 2 = -(d * (3468 - d) : ℝ) := by
  rw [rad, mul_pow, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt h, mul_neg_one]

private theorem phase_eq (d : ℝ) (hd : 0 ≤ d) (hd' : d ≤ 3468) :
    Complex.exp ((Real.arccos (1 - d / 1734) : ℂ) * Complex.I) =
      ((1734 - (d : ℂ)) + rad d) / 1734 := by
  have hl : -1 ≤ 1 - d / 1734 := by linarith
  have hu : 1 - d / 1734 ≤ 1 := by linarith
  have hrad : 0 ≤ d * (3468 - d) := mul_nonneg hd (sub_nonneg.mpr hd')
  have hsin : Real.sqrt (1 - (1 - d / 1734) ^ 2) =
      Real.sqrt (d * (3468 - d)) / 1734 := by
    rw [show 1 - (1 - d / 1734) ^ 2 = d * (3468 - d) / (1734 ^ 2) by ring,
      Real.sqrt_div hrad, Real.sqrt_sq (by norm_num : 0 ≤ (1734 : ℝ))]
  rw [Complex.exp_ofReal_mul_I, Real.cos_arccos hl hu, Real.sin_arccos, hsin, rad]
  push_cast
  ring

private def clockIndex : Fin 3 → ℕ := ![244, 724, 804]
private def clockRoot (i : Fin 3) : ℂ := rad (clockIndex i)
private def clockField : IntermediateField ℚ ℂ := IntermediateField.adjoin ℚ (Set.range clockRoot)
private def clockRadicand (i : Fin 3) : ℤ := -(clockIndex i : ℤ) * (3468 - clockIndex i)

private theorem clockRoot_sq (i : Fin 3) : clockRoot i ^ 2 = algebraMap ℤ ℂ (clockRadicand i) := by
  fin_cases i <;> norm_num [clockRoot, clockRadicand, clockIndex, rad_sq]

private theorem clockRoot_sq_rat (i : Fin 3) :
    clockRoot i ^ 2 = algebraMap ℚ ℂ (clockRadicand i : ℚ) := by
  simpa using clockRoot_sq i

private theorem clockRange :
    Set.range clockRoot = {clockRoot 0} ∪ {clockRoot 1} ∪ {clockRoot 2} := by
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp
  · simp only [Set.mem_union, Set.mem_singleton_iff]
    rintro ((rfl | rfl) | rfl)
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩

private theorem clockField_degree : Module.finrank ℚ clockField ≤ 8 := by
  rw [clockField, clockRange, IntermediateField.adjoin_union, IntermediateField.adjoin_union]
  exact tripleDegree _ _ _ (clockRoot_sq_rat 0) (clockRoot_sq_rat 1) (clockRoot_sq_rat 2)

private instance : NumberField clockField where
  to_charZero := inferInstance
  to_finiteDimensional := by
    rw [clockField, clockRange, IntermediateField.adjoin_union, IntermediateField.adjoin_union]
    have := IntermediateField.adjoin.finiteDimensional (quadraticIntegral _ (clockRoot_sq_rat 0))
    have := IntermediateField.adjoin.finiteDimensional (quadraticIntegral _ (clockRoot_sq_rat 1))
    have := IntermediateField.adjoin.finiteDimensional (quadraticIntegral _ (clockRoot_sq_rat 2))
    infer_instance

private instance : IsGalois ℚ clockField :=
  D5.S3.Factorization.Galois.SquareRootArithmetic.squareRootAdjoin_isGalois clockRoot_sq_rat

private def fieldRoot (i : Fin 3) : clockField :=
  ⟨clockRoot i, IntermediateField.subset_adjoin ℚ _ (Set.mem_range_self i)⟩

private theorem fieldRoot_sq (i : Fin 3) :
    fieldRoot i ^ 2 = algebraMap ℤ clockField (clockRadicand i) := by
  apply Subtype.ext
  exact clockRoot_sq i

private def fieldPhase (i : Fin 3) : clockField :=
  ((1734 - (clockIndex i : clockField)) + fieldRoot i) / 1734

private theorem val_fieldPhase (i : Fin 3) :
    clockField.val (fieldPhase i) =
      Complex.exp ((Real.arccos (1 - (clockIndex i : ℝ) / 1734) : ℂ) * Complex.I) := by
  rw [fieldPhase, map_div₀, map_add, map_sub, map_ofNat, map_natCast]
  exact (phase_eq (clockIndex i) (by positivity)
    (by fin_cases i <;> norm_num [clockIndex])).symm

private theorem exists_frob_sqrt {K : Type*} [Field K] [NumberField K] [IsGalois ℚ K]
    {p : ℕ} [Fact p.Prime] (hodd : p ≠ 2) {ι : Type*}
    (r : ι → K) (d : ι → ℤ) (hsq : ∀ i, r i ^ 2 = algebraMap ℤ K (d i))
    (hd : ∀ i, ¬ (p : ℤ) ∣ d i) :
    ∃ σ : K ≃ₐ[ℚ] K, ∀ i, σ (r i) = jacobiSym (d i) p • r i := by
  let P : Ideal ℤ := Ideal.span {(p : ℤ)}
  have hp : Nat.Prime p := Fact.out
  have : P.IsPrime := (Ideal.span_singleton_prime (Int.natCast_ne_zero.mpr hp.ne_zero)).mpr
    (Nat.prime_iff_prime_int.mp hp)
  obtain ⟨Q, hQ, hlo⟩ :=
    Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain (S := 𝓞 K) P
      (by
        rw [(RingHom.injective_iff_ker_eq_bot _).mp (FaithfulSMul.algebraMap_injective ℤ (𝓞 K))]
        exact bot_le)
  have : Q.IsPrime := hQ
  have : Q.LiesOver P := ⟨hlo.symm⟩
  have hP : P ≠ ⊥ := by
    exact Ideal.span_singleton_eq_bot.not.mpr (Int.natCast_ne_zero.mpr hp.ne_zero)
  have : Finite (𝓞 K ⧸ Q) := Ideal.finiteQuotientOfFreeOfNeBot Q
    (Ideal.ne_bot_of_liesOver_of_ne_bot hP Q)
  obtain ⟨σ, hσ⟩ := IsArithFrobAt.exists_of_isInvariant (𝓞 ℚ) (K ≃ₐ[ℚ] K) Q
  exact ⟨σ, fun i => D5.S3.Factorization.Galois.SquareRootArithmetic.arithmeticFrobenius_sqrt
    hodd (hd i) (hsq i) Q hσ⟩

private def phaseCompanion (i : Fin 3) : clockField :=
  ((1734 - (clockIndex i : clockField)) - fieldRoot i) / 1734

private theorem phase_mul_companion (i : Fin 3) : fieldPhase i * phaseCompanion i = 1 := by
  rw [fieldPhase, phaseCompanion, ← mul_div_mul_comm]
  have hd := fieldRoot_sq i
  push_cast [clockRadicand] at hd
  apply (div_eq_iff (by norm_num)).mpr
  norm_num at hd
  linear_combination -hd

private theorem phase_inv_eq (i : Fin 3) : (fieldPhase i)⁻¹ = phaseCompanion i :=
  inv_eq_of_mul_eq_one_right (phase_mul_companion i)

private theorem integral_root (i : Fin 3) : IsIntegral ℤ (fieldRoot i) := by
  apply IsIntegral.of_pow (n := 2) (by decide)
  rw [fieldRoot_sq]
  exact isIntegral_algebraMap

private theorem integral_phase_pair (i : Fin 3) :
    IsIntegral ℤ ((1734 : clockField) * fieldPhase i) ∧
      IsIntegral ℤ ((1734 : clockField) * (fieldPhase i)⁻¹) := by
  have hi : IsIntegral ℤ (1734 - (clockIndex i : clockField)) :=
    (isIntegral_natCast (R := ℤ) 1734).sub (isIntegral_natCast (R := ℤ) (clockIndex i))
  rw [phase_inv_eq, fieldPhase, phaseCompanion]
  constructor
  · simpa only [mul_div_cancel₀ _ (by norm_num : (1734 : clockField) ≠ 0)] using
      hi.add (integral_root i)
  · simpa only [mul_div_cancel₀ _ (by norm_num : (1734 : clockField) ≠ 0)] using
      hi.sub (integral_root i)

/- The Jacobi sign at each listed prime is negative for its own radicand alone. -/
private def flipPrime : Fin 3 → ℕ := ![41, 11, 79]

private theorem exists_flip (j : Fin 3) :
    ∃ σ : clockField ≃ₐ[ℚ] clockField, ∀ i,
      σ (fieldPhase i) = if i = j then (fieldPhase i)⁻¹ else fieldPhase i := by
  have hp : Fact (flipPrime j).Prime := ⟨by fin_cases j <;> norm_num [flipPrime]⟩
  have hodd : flipPrime j ≠ 2 := by fin_cases j <;> decide
  have hcop : ∀ i, ¬ ((flipPrime j : ℕ) : ℤ) ∣ clockRadicand i := by
    intro i
    fin_cases j <;> fin_cases i <;> decide
  obtain ⟨σ, hσ⟩ := exists_frob_sqrt hodd fieldRoot clockRadicand fieldRoot_sq hcop
  refine ⟨σ, fun i => ?_⟩
  have hsign : jacobiSym (clockRadicand i) (flipPrime j) = if i = j then -1 else 1 := by
    fin_cases j <;> fin_cases i <;> norm_num [clockRadicand, clockIndex, flipPrime]
  have hmap : σ (fieldPhase i) =
      ((1734 - (clockIndex i : clockField)) + σ (fieldRoot i)) / 1734 := by
    simp [fieldPhase, map_ofNat]
  rw [hmap, hσ, hsign]
  split_ifs with he
  · simp [phase_inv_eq, phaseCompanion, sub_eq_add_neg]
  · simp [fieldPhase]

private theorem fieldPhase_ne_zero (i : Fin 3) : fieldPhase i ≠ 0 := by
  intro h
  simpa [h] using phase_mul_companion i

private theorem phase_trace (i : Fin 3) :
    fieldPhase i + (fieldPhase i)⁻¹ =
      ((2 * (1734 - (clockIndex i : ℚ)) / 1734 : ℚ) : clockField) := by
  rw [phase_inv_eq, fieldPhase, phaseCompanion, ← add_div]
  push_cast
  ring

private theorem phase_infinite (i : Fin 3) (k : ℤ) (hk : k ≠ 0) : fieldPhase i ^ k ≠ 1 := by
  intro h
  let x := fieldPhase i
  have hp : x ^ k.natAbs = 1 := by
    cases k with
    | ofNat n => simpa using h
    | negSucc n => simpa [x, zpow_negSucc, inv_eq_one] using h
  have hn : 0 < k.natAbs := Int.natAbs_pos.mpr hk
  have hx : IsIntegral ℤ x := IsIntegral.of_pow hn (hp ▸ isIntegral_one)
  have hix : IsIntegral ℤ x⁻¹ := by
    apply IsIntegral.of_pow hn
    rw [inv_pow, hp, inv_one]
    exact isIntegral_one
  have hi := hx.add hix
  change IsIntegral ℤ (fieldPhase i + (fieldPhase i)⁻¹) at hi
  rw [phase_trace, isIntegral_ratCast_iff] at hi
  obtain ⟨z, hz⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hi
  have hden := congrArg Rat.den hz
  change (z : ℚ).den = (2 * (1734 - (clockIndex i : ℚ)) / 1734).den at hden
  fin_cases i <;> norm_num [clockIndex] at hden

private theorem phase_norm (τ : clockField →+* ℂ) (i : Fin 3) :
    ‖τ (fieldPhase i)‖ = 1 := by
  have hsq : τ (fieldRoot i) ^ 2 = clockRoot i ^ 2 := by
    rw [← map_pow, fieldRoot_sq, clockRoot_sq]
    simp
  rcases eq_or_eq_neg_of_sq_eq_sq _ _ hsq with h | h
  · have hv : τ (fieldPhase i) = clockField.val (fieldPhase i) := by
      simp only [fieldPhase, map_div₀, map_add, map_sub, map_ofNat, map_natCast, h]
      rfl
    rw [hv, val_fieldPhase, Complex.norm_exp_mul_I, Complex.ofReal_im, neg_zero, Real.exp_zero]
  · have hv : τ (fieldPhase i) = clockField.val (phaseCompanion i) := by
      simp only [fieldPhase, phaseCompanion, sub_eq_add_neg, map_div₀, map_add, map_neg,
        map_ofNat, map_natCast, h]
      rfl
    rw [hv, ← phase_inv_eq, map_inv₀, norm_inv, val_fieldPhase, Complex.norm_exp_mul_I,
      Complex.ofReal_im, neg_zero, Real.exp_zero, inv_one]

private theorem erase_flip {K : Type*} [Field K] {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) (k : ℤ)
    (h : x ^ k * y = 1) (hf : x⁻¹ ^ k * y = 1) : x ^ (2 * k) = 1 := by
  rw [inv_zpow] at hf
  have heq : x ^ k = (x ^ k)⁻¹ := mul_right_cancel₀ hy (h.trans hf.symm)
  rw [two_mul, zpow_add₀ hx]
  calc
    x ^ k * x ^ k = (x ^ k)⁻¹ * x ^ k := congrArg (· * x ^ k) heq
    _ = 1 := inv_mul_cancel₀ (zpow_ne_zero _ hx)

private def exponents (m n : ℤ) : Fin 3 → ℤ := ![-(m+n), m, n]

/- Comparing a relation with its image under one flip would give finite order. -/
private theorem clockProduct_ne_one (m n : ℤ) (hmn : m ≠ 0 ∨ n ≠ 0) :
    (∏ i : Fin 3, fieldPhase i ^ exponents m n i) ≠ 1 := by
  intro h
  have h' : fieldPhase 0 ^ (-(m+n)) * (fieldPhase 1 ^ m * fieldPhase 2 ^ n) = 1 := by
    simpa [Fin.prod_univ_succ, exponents] using h
  rcases hmn with hm | hn
  · obtain ⟨σ, hσ⟩ := exists_flip 1
    have hflip : fieldPhase 0 ^ (-(m+n)) * ((fieldPhase 1)⁻¹ ^ m * fieldPhase 2 ^ n) = 1 := by
      simpa only [map_mul, map_zpow₀, map_one, hσ, ite_true,
        ite_eq_right (by decide : (0 : Fin 3) ≠ 1), ite_eq_right (by decide : (2 : Fin 3) ≠ 1)]
        using congrArg σ h'
    exact phase_infinite 1 (2 * m) (by omega) (erase_flip
      (fieldPhase_ne_zero 1) (mul_ne_zero (zpow_ne_zero _ (fieldPhase_ne_zero 0))
        (zpow_ne_zero _ (fieldPhase_ne_zero 2))) m
      (by simpa only [mul_left_comm] using h')
      (by simpa only [mul_left_comm] using hflip))
  · obtain ⟨σ, hσ⟩ := exists_flip 2
    have hflip : fieldPhase 0 ^ (-(m+n)) * (fieldPhase 1 ^ m * (fieldPhase 2)⁻¹ ^ n) = 1 := by
      simpa only [map_mul, map_zpow₀, map_one, hσ, ite_true,
        ite_eq_right (by decide : (0 : Fin 3) ≠ 2), ite_eq_right (by decide : (1 : Fin 3) ≠ 2)]
        using congrArg σ h'
    exact phase_infinite 2 (2 * n) (by omega) (erase_flip
      (fieldPhase_ne_zero 2) (mul_ne_zero (zpow_ne_zero _ (fieldPhase_ne_zero 0))
        (zpow_ne_zero _ (fieldPhase_ne_zero 1))) n
      (by simpa only [mul_left_comm, mul_comm, mul_assoc] using h')
      (by simpa only [mul_left_comm, mul_comm, mul_assoc] using hflip))

private def theta (d : ℝ) : ℝ := Real.arccos (1 - d / 1734)
/-- The integer combination of the two clock differences with coefficients `m` and `n`. -/
def clockFrequency (m n : ℤ) : ℝ :=
  m * (theta 724 - theta 244) + n * (theta 804 - theta 244)

private theorem clockProduct_val (m n : ℤ) :
    clockField.val.toRingHom (∏ i : Fin 3, fieldPhase i ^ exponents m n i) =
      Complex.exp (Complex.I * (clockFrequency m n : ℂ)) := by
  rw [map_prod]
  simp only [map_zpow₀, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, val_fieldPhase,
    Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, exponents, Matrix.cons_val_zero,
    Matrix.cons_val_succ]
  simp only [← Complex.exp_int_mul, ← Complex.exp_add, clockFrequency, theta, clockIndex,
    Matrix.cons_val_zero, Matrix.cons_val_succ]
  congr 1
  push_cast
  ring

/-- The actual clock frequency stays exponentially separated from zero for
all nonzero integer modes. -/
theorem frequency_separation (m n : ℤ) (hmn : m ≠ 0 ∨ n ≠ 0) :
    1 ≤ |clockFrequency m n| * (128 * (1734 : ℝ) ^ (32 * max m.natAbs n.natAbs)) := by
  have h :=
    D5.S3.Fourier.Asymptotics.AlgebraicPhaseSeparation.signed_product_separation
      Finset.univ fieldPhase (exponents m n) 1734 (by decide)
      (fun i _ => (integral_phase_pair i).1) (fun i _ => (integral_phase_pair i).2)
      (fun τ i _ => phase_norm τ i) (clockProduct_ne_one m n hmn) clockField.val
  let B := (1734 : ℝ) ^ (∑ i, (exponents m n i).natAbs)
  have hB : 1 ≤ B := one_le_pow₀ (by norm_num)
  have hbound : ∑ i, (exponents m n i).natAbs ≤ 4 * max m.natAbs n.natAbs := by
    have ha := Int.natAbs_add_le m n
    have hm := le_max_left m.natAbs n.natAbs
    have hn := le_max_right m.natAbs n.natAbs
    simp [Fin.sum_univ_succ, exponents]
    omega
  simp only [Nat.cast_pow, Nat.cast_ofNat] at h
  change 1 ≤ ‖clockField.val.toRingHom (∏ i, fieldPhase i ^ exponents m n i) - 1‖ *
    (B * (2 * B) ^ (Module.finrank ℚ clockField - 1)) at h
  rw [clockProduct_val] at h
  refine h.trans (mul_le_mul ?_ ?_ (by positivity) (by positivity))
  · simpa only [Real.norm_eq_abs] using
      (Real.norm_exp_I_mul_ofReal_sub_one_le (x := clockFrequency m n))
  · calc
      B * (2 * B) ^ (Module.finrank ℚ clockField - 1) ≤ B * (2 * B) ^ 7 :=
        mul_le_mul_of_nonneg_left
          (pow_le_pow_right₀ (by linarith) (by have := clockField_degree; omega)) (by positivity)
      _ = 128 * (1734 : ℝ) ^ ((∑ i, (exponents m n i).natAbs) * 8) := by
        rw [pow_mul]; dsimp [B]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) (by omega)) (by norm_num)

end

end D5.S3.Fourier.Asymptotics.TwoClockFrequencySeparation
