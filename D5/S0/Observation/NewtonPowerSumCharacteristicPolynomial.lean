/- GID: D5/S0/Observation/NewtonPowerSumCharacteristicPolynomial
   generality: G
   mirror-B: D5/B/S0/Observation/NewtonPowerSumCharacteristicPolynomial
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Newton identities recover a split characteristic polynomial from bounded power sums. -/

import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities
import Mathlib.RingTheory.Polynomial.Vieta

/- Library-search audit trail (2026-08-31):
   * Five-route repository searches found no receipt or D5 declaration covering this atom.
     `PowerTraceCharacteristicPolynomialSaturation` assumes equal characteristic polynomials
     to extend trace equality, while `IntegerRecoveryStructureSeparation` records the converse
     Newton bridge as a premise and supplies a positive-characteristic counterexample.
   * Pinned Mathlib searches for `NewtonIdentities`, `mul_esymm_eq_sum`, `psum`, `esymm`,
     `prod_X_sub_C_coeff`, `coeff_eq_esymm_roots_of_splits`, `charpoly`, and trace/charpoly
     bridges found `MvPolynomial.mul_esymm_eq_sum` as the exact Newton primitive and
     `Multiset.prod_X_sub_X_eq_sum_esymm` as the exact Vieta expansion. No theorem packages
     the bounded-power-sums-to-matrix-charpoly statement below.
   * Loogle confirmed the Newton primitive and found no stronger packaged matrix theorem.
     Anonymous third-party code searches were unavailable (GitHub HTTP 401; grep.app HTTP 429).
   * No new definition or abbreviation is introduced. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S0.Observation.NewtonPowerSumCharacteristicPolynomial

open Polynomial

/-- Over a characteristic-zero field, the first `n` positive power sums of two
enumerated `n`-element spectra determine the corresponding monic split polynomial. -/
theorem power_sums_determine_split_characteristic_polynomial
    {K : Type*} [Field K] [CharZero K] {n : ℕ}
    (x y : Fin n → K)
    (hPower : ∀ k < n, ∑ i, x i ^ (k + 1) = ∑ i, y i ^ (k + 1)) :
    (∏ i, (X - C (x i))) = ∏ i, (X - C (y i)) := by
  classical
  have hPower' (e : ℕ) (hePos : 0 < e) (heBound : e ≤ n) :
      ∑ i, x i ^ e = ∑ i, y i ^ e := by
    simpa [Nat.sub_add_cancel hePos] using hPower (e - 1) (by omega)
  have hElementary : ∀ k ≤ n,
      MvPolynomial.eval x (MvPolynomial.esymm (Fin n) K k) =
        MvPolynomial.eval y (MvPolynomial.esymm (Fin n) K k) := by
    intro k hk
    induction k using Nat.strong_induction_on with
    | h k ih =>
        by_cases hkZero : k = 0
        · subst k
          simp
        have hkPos : 0 < k := Nat.pos_of_ne_zero hkZero
        have hxNewton := congrArg (MvPolynomial.eval x)
          (MvPolynomial.mul_esymm_eq_sum (Fin n) K k)
        have hyNewton := congrArg (MvPolynomial.eval y)
          (MvPolynomial.mul_esymm_eq_sum (Fin n) K k)
        apply mul_left_cancel₀ (Nat.cast_ne_zero.mpr hkZero)
        calc
          (k : K) * MvPolynomial.eval x (MvPolynomial.esymm (Fin n) K k) =
              (-1 : K) ^ (k + 1) *
                ∑ a ∈ Finset.antidiagonal k with a.1 < k,
                  (-1 : K) ^ a.1 *
                    MvPolynomial.eval x (MvPolynomial.esymm (Fin n) K a.1) *
                      ∑ i, x i ^ a.2 := by
                simpa [MvPolynomial.psum] using hxNewton
          _ = (-1 : K) ^ (k + 1) *
                ∑ a ∈ Finset.antidiagonal k with a.1 < k,
                  (-1 : K) ^ a.1 *
                    MvPolynomial.eval y (MvPolynomial.esymm (Fin n) K a.1) *
                      ∑ i, y i ^ a.2 := by
                apply congrArg ((-1 : K) ^ (k + 1) * ·)
                apply Finset.sum_congr rfl
                intro a ha
                have haData := Finset.mem_filter.mp ha
                have haSum := Finset.mem_antidiagonal.mp haData.1
                have haFirst : a.1 < k := haData.2
                have haSecondPos : 0 < a.2 := by omega
                have haSecondBound : a.2 ≤ n := by omega
                rw [ih a.1 haFirst (by omega), hPower' a.2 haSecondPos haSecondBound]
          _ = (k : K) * MvPolynomial.eval y (MvPolynomial.esymm (Fin n) K k) := by
                simpa [MvPolynomial.psum] using hyNewton.symm
  have hElementaryMultiset (k : ℕ) (hk : k ≤ n) :
      (Finset.univ.val.map x).esymm k = (Finset.univ.val.map y).esymm k := by
    rw [← MvPolynomial.aeval_esymm_eq_multiset_esymm (Fin n) K k x,
      ← MvPolynomial.aeval_esymm_eq_multiset_esymm (Fin n) K k y]
    exact hElementary k hk
  calc
    (∏ i, (X - C (x i))) =
        ∑ k ∈ Finset.range (n + 1),
          (-1) ^ k * (C ((Finset.univ.val.map x).esymm k) * X ^ (n - k)) := by
      simpa only [Finset.prod, Multiset.map_map, Function.comp_apply, Multiset.card_map,
        Finset.card_val, Finset.card_univ, Fintype.card_fin] using
          (Multiset.prod_X_sub_X_eq_sum_esymm (Finset.univ.val.map x))
    _ = ∑ k ∈ Finset.range (n + 1),
          (-1) ^ k * (C ((Finset.univ.val.map y).esymm k) * X ^ (n - k)) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [hElementaryMultiset k (by simpa using Finset.mem_range.mp hk)]
    _ = ∏ i, (X - C (y i)) := by
      symm
      simpa only [Finset.prod, Multiset.map_map, Function.comp_apply, Multiset.card_map,
        Finset.card_val, Finset.card_univ, Fintype.card_fin] using
          (Multiset.prod_X_sub_X_eq_sum_esymm (Finset.univ.val.map y))

#print axioms power_sums_determine_split_characteristic_polynomial

/-- If two `n`-dimensional matrices have enumerated split spectra with the same
first `n` positive power sums, then their characteristic polynomials are equal. -/
theorem matrix_charpoly_eq_of_spectral_power_sums_eq
    {K : Type*} [Field K] [CharZero K] {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) K) (spectrumA spectrumB : Fin n → K)
    (hA : A.charpoly = ∏ i, (X - C (spectrumA i)))
    (hB : B.charpoly = ∏ i, (X - C (spectrumB i)))
    (hPower : ∀ k < n,
      ∑ i, spectrumA i ^ (k + 1) = ∑ i, spectrumB i ^ (k + 1)) :
    A.charpoly = B.charpoly := by
  rw [hA, hB]
  exact power_sums_determine_split_characteristic_polynomial spectrumA spectrumB hPower

#print axioms matrix_charpoly_eq_of_spectral_power_sums_eq

end D5.S0.Observation.NewtonPowerSumCharacteristicPolynomial
