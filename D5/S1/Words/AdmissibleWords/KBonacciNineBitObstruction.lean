/- GID: D5/S1/Words/AdmissibleWords/KBonacciNineBitObstruction
   generality: I
   mirror-B: D5/B/S1/Words/AdmissibleWords/KBonacciNineBitObstruction
   mirror-E: none(waiver:kernel-checked-finite-refutation)
   anchors: []
   utility: kind=bounded-enumeration; basis=refutes=gid:D5/S1/Words/AdmissibleWords/KBonacciNineBitObstruction.claim; result=D5/S1/Words/AdmissibleWords/KBonacciNineBitObstruction.result; claim=D5/S1/Words/AdmissibleWords/KBonacciNineBitObstruction.claim
   digest: One legal Boolean word of at most nine bits cannot attain both target remainders. -/

import D5.S1.Words.AdmissibleWords.KBonacciActualSaturation

/-! Raw simultaneous remainder exclusion for the original order-two Boolean scanner. -/

set_option autoImplicit false
noncomputable section

namespace D5.S1.Words.AdmissibleWords.KBonacciNineBitObstruction

open Polynomial Finset
open D5.S0.Tower.DBonacci.Names D5.S0.Tower.DBonacci.Substitution
open D5.S1.Words.AdmissibleWords.KBonacciActualSaturation

/-- A single short word is accepted by the original order-two scanner and has
both raw remainders of the polynomial `1 + X`, with every position counted. -/
def claim : Prop :=
  ∃ n : ℕ, n ≤ 9 ∧ ∃ w : Fin n → Bool,
    DBonacciAdmissible 2 n w ∧
      wordPolynomial w %ₘ phi 2 = (1 + X) %ₘ phi 2 ∧
      wordPolynomial w %ₘ phi 3 = (1 + X) %ₘ phi 3

private theorem nine_bit_obstruction (w : Fin 9 → Bool)
    (hlegal : DBonacciAdmissible 2 9 w)
    (h2 : wordPolynomial w %ₘ phi 2 = (1 + X) %ₘ phi 2)
    (h3 : wordPolynomial w %ₘ phi 3 = (1 + X) %ₘ phi 3) : False := by
  let b : Fin 9 → ZMod 2 := fun i => if w i then 1 else 0
  have hp2 : phi 2 = (X ^ 2 + X + 1 : (ZMod 2)[X]) := by
    simp [phi, sum_range_succ, CharTwo.sub_eq_add]
    ring
  have hp3 : phi 3 = (X ^ 3 + X ^ 2 + X + 1 : (ZMod 2)[X]) := by
    simp [phi, sum_range_succ, CharTwo.sub_eq_add]
    ring
  have hm2 : (phi 2).Monic := by rw [hp2]; monicity!
  have hm3 : (phi 3).Monic := by rw [hp3]; monicity!
  have hd2 : (phi 2).degree = 2 := by rw [hp2]; compute_degree!
  have hd3 : (phi 3).degree = 3 := by rw [hp3]; compute_degree!
  have hr2 : wordPolynomial w %ₘ phi 2 =
      C (b 0 + b 2 + b 3 + b 5 + b 6 + b 8) +
        C (b 1 + b 2 + b 4 + b 5 + b 7 + b 8) * X := by
    refine (div_modByMonic_unique
      (C (b 2) * (1) +
          C (b 3) * (1 + X) +
          C (b 4) * (X + X ^ 2) +
          C (b 5) * (1 + X ^ 2 + X ^ 3) +
          C (b 6) * (1 + X + X ^ 3 + X ^ 4) +
          C (b 7) * (X + X ^ 2 + X ^ 4 + X ^ 5) +
          C (b 8) * (1 + X ^ 2 + X ^ 3 + X ^ 5 + X ^ 6))
      _ hm2 ⟨?_, ?_⟩).2
    · simp only [wordPolynomial, vectorPolynomial, Fin.sum_univ_succ,
        Fin.sum_univ_zero, Fin.val_zero, Fin.val_succ,
        ← C_mul_X_pow_eq_monomial, hp2, map_add]
      change _ = ∑ i : Fin 9, C (b i) * X ^ i.val
      simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero, Fin.val_succ]
      simp only [Fin.reduceSucc]
      ring_nf
      simp only [CharTwo.two_eq_zero, mul_zero, add_zero]
    · rw [hd2]
      compute_degree!
  have ht2 : ((1 + X : (ZMod 2)[X]) %ₘ phi 2) = 1 + X := by
    apply (modByMonic_eq_self_iff hm2).2
    rw [hd2]
    compute_degree!
  have hr3 : wordPolynomial w %ₘ phi 3 =
      C (b 0 + b 3 + b 4 + b 7 + b 8) + C (b 1 + b 3 + b 5 + b 7) * X +
        C (b 2 + b 3 + b 6 + b 7) * X ^ 2 := by
    refine (div_modByMonic_unique
      (C (b 3) * (1) +
          C (b 4) * (1 + X) +
          C (b 5) * (X + X ^ 2) +
          C (b 6) * (X ^ 2 + X ^ 3) +
          C (b 7) * (1 + X ^ 3 + X ^ 4) +
          C (b 8) * (1 + X + X ^ 4 + X ^ 5))
      _ hm3 ⟨?_, ?_⟩).2
    · simp only [wordPolynomial, vectorPolynomial, Fin.sum_univ_succ,
        Fin.sum_univ_zero, Fin.val_zero, Fin.val_succ,
        ← C_mul_X_pow_eq_monomial, hp3, map_add]
      change _ = ∑ i : Fin 9, C (b i) * X ^ i.val
      simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero, Fin.val_succ]
      simp only [Fin.reduceSucc]
      ring_nf
      simp only [CharTwo.two_eq_zero, mul_zero, add_zero]
    · rw [hd3]
      compute_degree!
  have ht3 : ((1 + X : (ZMod 2)[X]) %ₘ phi 3) = 1 + X := by
    apply (modByMonic_eq_self_iff hm3).2
    rw [hd3]
    compute_degree!
  rw [hr2, ht2] at h2
  rw [hr3, ht3] at h3
  have hc20 : b 0 + b 2 + b 3 + b 5 + b 6 + b 8 = 1 := by
    have h := congrArg (fun P : (ZMod 2)[X] => P.coeff 0) h2
    norm_num only [coeff_add, coeff_C, coeff_C_mul_X, coeff_C_mul_X_pow,
      coeff_one, coeff_X] at h
    simpa only [ite_true, ite_false, add_zero, zero_add] using h
  have hc21 : b 1 + b 2 + b 4 + b 5 + b 7 + b 8 = 1 := by
    have h := congrArg (fun P : (ZMod 2)[X] => P.coeff 1) h2
    norm_num only [coeff_add, coeff_C, coeff_C_mul_X, coeff_C_mul_X_pow,
      coeff_one, coeff_X] at h
    simpa only [ite_true, ite_false, add_zero, zero_add] using h
  have hc30 : b 0 + b 3 + b 4 + b 7 + b 8 = 1 := by
    have h := congrArg (fun P : (ZMod 2)[X] => P.coeff 0) h3
    norm_num only [coeff_add, coeff_C, coeff_C_mul_X, coeff_C_mul_X_pow,
      coeff_one, coeff_X] at h
    simpa only [ite_true, ite_false, add_zero, zero_add] using h
  have hc31 : b 1 + b 3 + b 5 + b 7 = 1 := by
    have h := congrArg (fun P : (ZMod 2)[X] => P.coeff 1) h3
    norm_num only [coeff_add, coeff_C, coeff_C_mul_X, coeff_C_mul_X_pow,
      coeff_one, coeff_X] at h
    simpa only [ite_true, ite_false, add_zero, zero_add] using h
  have hc32 : b 2 + b 3 + b 6 + b 7 = 0 := by
    have h := congrArg (fun P : (ZMod 2)[X] => P.coeff 2) h3
    norm_num only [coeff_add, coeff_C, coeff_C_mul_X, coeff_C_mul_X_pow,
      coeff_one, coeff_X] at h
    simpa only [ite_true, ite_false, add_zero, zero_add] using h
  have hexclusion : ∀ v : Fin 9 → Bool,
      let c : Fin 9 → ZMod 2 := fun i => if v i then 1 else 0
      DBonacciAdmissible 2 9 v →
      c 0 + c 2 + c 3 + c 5 + c 6 + c 8 = 1 →
      c 1 + c 2 + c 4 + c 5 + c 7 + c 8 = 1 →
      c 0 + c 3 + c 4 + c 7 + c 8 = 1 →
      c 1 + c 3 + c 5 + c 7 = 1 →
      c 2 + c 3 + c 6 + c 7 = 0 → False := by
    decide +kernel
  exact hexclusion w hlegal hc20 hc21 hc30 hc31 hc32

/-- The two raw target remainders have no common accepted Boolean source of
charged length zero through nine. -/
theorem result : ¬ claim := by
  rintro ⟨n, hn, w, hw, h2, h3⟩
  have hpad : ∀ m : ℕ, n ≤ m → ∃ v : Fin m → Bool,
      DBonacciAdmissible 2 m v ∧ wordPolynomial v = wordPolynomial w := by
    intro m hm
    induction m, hm using Nat.le_induction with
    | base => exact ⟨w, hw, rfl⟩
    | succ m hm ih =>
        obtain ⟨v, hv, hp⟩ := ih
        refine ⟨Fin.snoc v false, admissible_snoc_false 2 m v hv, ?_⟩
        simpa [wordPolynomial, vectorPolynomial, Fin.sum_univ_castSucc] using hp
  obtain ⟨v, hv, hp⟩ := hpad 9 hn
  exact nine_bit_obstruction v hv (hp ▸ h2) (hp ▸ h3)

end D5.S1.Words.AdmissibleWords.KBonacciNineBitObstruction
