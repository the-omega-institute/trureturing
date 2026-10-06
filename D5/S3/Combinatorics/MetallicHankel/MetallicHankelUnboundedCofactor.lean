/- GID: D5/S3/Combinatorics/MetallicHankel/MetallicHankelUnboundedCofactor
   generality: G
   mirror-B: D5/B/S3/Combinatorics/MetallicHankel/MetallicHankelUnboundedCofactor
   mirror-E: none(waiver:normal-index-hankel-cofactor)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Matrix.NonsingularInverse]
   utility: none
   digest: A companion operator computes the two-shift cofactor across normal-index gaps. -/

import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import D5.S3.Combinatorics.MetallicHankel.MetallicHankelDeterminants

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.MetallicHankel.MetallicHankelUnboundedCofactor

open Finset MetallicHankelDefs
open scoped Matrix

/-- Two normal moment relations determine a cofactor even when intervening minors vanish. -/
theorem normal_cofactor (Φ : PowerSeries ℤ) (ℓ m : ℕ) (hm : 0 < m)
    (c b : ℕ → ℤ) (h : ℤ) (hc : c m = 1) (hb : m = 1 → b 1 = 0)
    (orthogonal : ∀ t < m,
      ∑ r ∈ range (m + 1), c r * PowerSeries.coeff (ℓ + r + t) Φ = 0)
    (previous : ∀ t < m - 1,
      ∑ r ∈ range m, b r * PowerSeries.coeff (ℓ + r + t) Φ = 0)
    (leading : ∑ r ∈ range m,
      b r * PowerSeries.coeff (ℓ + r + (m - 1)) Φ = h)
    (unit : IsUnit (shiftedHankel Φ ℓ m)) :
    h * shiftedHankel Φ (ℓ + 2) (m - 1) =
      shiftedHankel Φ ℓ m * (c 1 * b 0 - c 0 * b 1) := by
  classical
  cases m with
  | zero => omega
  | succ m =>
    cases m with
    | zero =>
      have hb1 := hb rfl
      have hh : b 0 * PowerSeries.coeff ℓ Φ = h := by simpa using leading
      simp [shiftedHankel, hc, hb1]
      exact hh.symm.trans (mul_comm _ _)
    | succ n =>
      let H : Matrix (Fin (n + 2)) (Fin (n + 2)) ℤ :=
        Matrix.of fun i j => PowerSeries.coeff (ℓ + i.val + j.val) Φ
      let last : Fin (n + 2) := Fin.last (n + 1)
      let one : Fin (n + 2) := ⟨1, by omega⟩
      let T : Matrix (Fin (n + 2)) (Fin (n + 2)) ℤ :=
        Matrix.of fun i j =>
          if j = last then -c i.val else if i.val = j.val + 1 then 1 else 0
      have hu : IsUnit H.det := unit
      have symmetric : H.IsSymm := by
        ext i j
        simp only [Matrix.transpose_apply, H, Matrix.of_apply]
        rw [show ℓ + j.val + i.val = ℓ + i.val + j.val by omega]
      have product (i j : Fin (n + 2)) :
          (H * T) i j = PowerSeries.coeff (ℓ + i.val + j.val + 1) Φ := by
        rw [Matrix.mul_apply]
        by_cases hj : j = last
        · subst j
          simp only [T, Matrix.of_apply, if_true, H, mul_neg, sum_neg_distrib]
          have hz := orthogonal i.val i.isLt
          rw [sum_range_succ, hc, one_mul] at hz
          have hs : (∑ r : Fin (n + 2),
              PowerSeries.coeff (ℓ + i.val + r.val) Φ * c r.val) =
              ∑ r ∈ range (n + 2), c r * PowerSeries.coeff (ℓ + r + i.val) Φ := by
            rw [← Fin.sum_univ_eq_sum_range]
            apply sum_congr rfl
            intro r _
            rw [mul_comm]
            rw [show ℓ + i.val + r.val = ℓ + r.val + i.val by omega]
          rw [hs]
          have hi : ℓ + (n + 1 + 1) + i.val = ℓ + i.val + last.val + 1 := by
            simp only [last, Fin.val_last]
            omega
          rw [hi] at hz
          exact neg_eq_iff_eq_neg.mpr (eq_neg_of_add_eq_zero_left hz)
        · have hjlt : j.val + 1 < n + 2 := by
            have hne : j.val ≠ n + 1 := by
              intro he
              apply hj
              exact Fin.ext (by simpa [last] using he)
            omega
          let next : Fin (n + 2) := ⟨j.val + 1, hjlt⟩
          rw [sum_eq_single next]
          · simp [T, hj, next, H, Nat.add_assoc]
          · intro r _ hr
            have hne : r.val ≠ j.val + 1 := by
              intro he
              apply hr
              exact Fin.ext he
            simp [T, hj, hne]
          · simp
      have selfadjoint : H * T = T.transpose * H := by
        have hs : (H * T).IsSymm := by
          ext i j
          simp only [Matrix.transpose_apply, product]
          rw [show ℓ + j.val + i.val + 1 = ℓ + i.val + j.val + 1 by omega]
        calc
          H * T = (H * T).transpose := hs.eq.symm
          _ = T.transpose * H := by rw [Matrix.transpose_mul, symmetric.eq]
      have commutes : T * H⁻¹ = H⁻¹ * T.transpose := by
        have he := congrArg (fun A => H⁻¹ * A * H⁻¹) selfadjoint
        have lhs : H⁻¹ * (H * T) * H⁻¹ = T * H⁻¹ := by
          rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul H hu, Matrix.one_mul]
        have rhs : H⁻¹ * (T.transpose * H) * H⁻¹ = H⁻¹ * T.transpose := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_nonsing_inv H hu,
            Matrix.mul_one]
        rwa [lhs, rhs] at he
      have hbvec : H *ᵥ (fun i => b i.val) = Pi.single last h := by
        funext i
        simp only [Matrix.mulVec, dotProduct, H, Matrix.of_apply]
        have hs : (∑ r : Fin (n + 2),
            PowerSeries.coeff (ℓ + i.val + r.val) Φ * b r.val) =
            ∑ r ∈ range (n + 2), b r * PowerSeries.coeff (ℓ + r + i.val) Φ := by
          rw [← Fin.sum_univ_eq_sum_range]
          apply sum_congr rfl
          intro r _
          rw [mul_comm]
          rw [show ℓ + i.val + r.val = ℓ + r.val + i.val by omega]
        rw [hs]
        by_cases hi : i = last
        · subst i
          simpa [last] using leading
        · have hlt : i.val < n + 1 := by
            have hne : i.val ≠ n + 1 := by
              intro he
              apply hi
              exact Fin.ext (by simpa [last] using he)
            omega
          rw [previous i.val (by omega)]
          simp [hi]
      have column (i : Fin (n + 2)) : b i.val = H⁻¹ i last * h := by
        have he := congrArg (fun v => (H⁻¹ *ᵥ v) i) hbvec
        simpa [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul H hu,
          Matrix.mulVec_single, Matrix.col, smul_eq_mul] using he
      have left : (T * H⁻¹) 0 one = -c 0 * H⁻¹ last one := by
        rw [Matrix.mul_apply, sum_eq_single last]
        · simp [T]
        · intro r _ hr
          simp [T, hr]
        · simp
      have right : (H⁻¹ * T.transpose) 0 one =
          H⁻¹ 0 0 - c 1 * H⁻¹ 0 last := by
        rw [Matrix.mul_apply]
        have entries (r : Fin (n + 2)) :
            H⁻¹ 0 r * T.transpose r one =
              (if r = 0 then H⁻¹ 0 0 else 0) +
                (if r = last then -c 1 * H⁻¹ 0 last else 0) := by
          simp only [Matrix.transpose_apply, T, Matrix.of_apply, one]
          by_cases hr : r = last
          · subst r
            have hne : last ≠ 0 := by
              intro he
              have hv := congrArg Fin.val he
              simp [last] at hv
            simp [hne]
            ring
          · by_cases hz : r = 0
            · subst r
              simp [hr]
            · have hv : ¬1 = r.val + 1 := by
                intro he
                apply hz
                exact Fin.ext (by simp only [Fin.val_zero]; omega)
              simp [hr, hz]
        simp_rw [entries]
        rw [sum_add_distrib]
        simp [sub_eq_add_neg]
      have invsymmetric := symmetric.inv
      have inv00 : h * H⁻¹ 0 0 = c 1 * b 0 - c 0 * b 1 := by
        have he := congrArg (fun A => A 0 one) commutes
        rw [left, right, ← invsymmetric.apply last one] at he
        have hb0 := column 0
        have hb1 := column one
        dsimp only [one, Fin.val_zero] at hb0 hb1
        have he' := (eq_sub_iff_add_eq.mp he).symm
        rw [he', hb0, hb1]
        ring
      have cofactor : H.det * H⁻¹ 0 0 = shiftedHankel Φ (ℓ + 2) (n + 1) := by
        have he : H.det * H⁻¹ 0 0 = H.adjugate 0 0 := by
          rw [Matrix.nonsing_inv_apply H hu]
          simp only [Matrix.smul_apply, smul_eq_mul]
          rw [← mul_assoc, hu.mul_val_inv, one_mul]
        rw [he, Matrix.adjugate_fin_succ_eq_det_submatrix]
        simp only [Fin.val_zero, zero_add, pow_zero, one_mul, Fin.succAbove_zero]
        change _ = (Matrix.of fun i j : Fin (n + 1) =>
          PowerSeries.coeff (ℓ + 2 + i.val + j.val) Φ).det
        congr 1
        ext i j
        simp only [Matrix.submatrix_apply, H, Matrix.of_apply, Fin.val_succ]
        rw [show ℓ + (i.val + 1) + (j.val + 1) = ℓ + 2 + i.val + j.val by omega]
      change h * shiftedHankel Φ (ℓ + 2) (n + 1) = H.det * _
      rw [← cofactor, ← inv00]
      ring

end D5.S3.Combinatorics.MetallicHankel.MetallicHankelUnboundedCofactor
