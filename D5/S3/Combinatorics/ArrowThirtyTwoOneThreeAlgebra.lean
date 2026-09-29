/- GID: D5/S3/Combinatorics/ArrowThirtyTwoOneThreeAlgebra
   generality: G
   mirror-B: D5/B/S3/Combinatorics/ArrowThirtyTwoOneThreeAlgebra
   mirror-E: none(waiver:recurrence-to-cubic-formal-series-algebra)
   anchors: [mathlib/module/Mathlib.RingTheory.PowerSeries.Catalan]
   utility: none
   digest: The Catalan refined recurrence entails the arrow-pattern cubic. -/

import Mathlib.RingTheory.PowerSeries.Catalan
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.ArrowThirtyTwoOneThreeAlgebra

open PowerSeries Finset

noncomputable section

theorem cubic_of_recurrence (a : ℕ → ℕ) (h0 : a 0 = 1)
    (hrec : ∀ n, 1 ≤ n → (a n : ℤ) = (a (n - 1) : ℤ) +
      ∑ k ∈ Finset.Icc 1 (n - 1), (catalan (k - 1) : ℤ) *
        PowerSeries.coeff (n - 1 - k)
          ((PowerSeries.mk fun m => (a m : ℤ)) ^ (k + 1))) :
    let F : PowerSeries ℤ := PowerSeries.mk fun m => (a m : ℤ)
    1 + (3 * PowerSeries.X - 2) * F +
      (1 - PowerSeries.X) * (1 - 2 * PowerSeries.X) * F ^ 2 +
        PowerSeries.X ^ 3 * F ^ 3 = 0 := by
  let F : PowerSeries ℤ := PowerSeries.mk fun m => (a m : ℤ)
  let X : PowerSeries ℤ := PowerSeries.X
  let z : PowerSeries ℤ := X * F
  let C : PowerSeries ℤ := PowerSeries.catalanSeries.map (Nat.castRingHom ℤ)
  let T : PowerSeries ℤ := C.subst z
  have hz0 : constantCoeff z = 0 := by simp [z, X]
  have hs : HasSubst z := .of_constantCoeff_zero hz0
  have hC : C = 1 + X * C ^ 2 := by
    have h := congrArg (PowerSeries.map (Nat.castRingHom ℤ))
      PowerSeries.catalanSeries_sq_mul_X_add_one
    simpa [C, X, add_comm, mul_comm] using h.symm
  have hT : T = 1 + z * T ^ 2 := by
    have h := congrArg (fun f : PowerSeries ℤ => f.subst z) hC
    have hmap : (substAlgHom hs) X = z := substAlgHom_X hs
    simpa only [← coe_substAlgHom hs, map_add, map_mul, map_pow, map_one,
      hmap, T] using h
  have hcoeff (n : ℕ) :
      coeff n (z ^ 2 * T) =
        ∑ k ∈ Finset.Icc 1 (n - 1), (catalan (k - 1) : ℤ) *
          coeff (n - 1 - k) (F ^ (k + 1)) := by
    have he : z ^ 2 * T = (X ^ 2 * C).subst z := by
      rw [subst_mul hs, subst_pow hs, subst_X hs]
    rw [he, coeff_subst' hs]
    simp only [smul_eq_mul]
    have hsupport : (fun m : ℕ => coeff m (X ^ 2 * C) * coeff n (z ^ m)).support ⊆
        Finset.Icc 2 n := by
      intro m hm
      apply Finset.mem_Icc.mpr
      constructor
      · by_contra hh
        have hm0 : coeff m (X ^ 2 * C) = 0 := by
          rw [coeff_X_pow_mul']
          simp [show ¬ 2 ≤ m by omega]
        exact hm (by simp [hm0])
      · by_contra hh
        have hzlow : coeff n (z ^ m) = 0 :=
          X_pow_dvd_iff.mp (pow_dvd_pow_of_dvd (X_dvd_iff.mpr hz0) m) n (by omega)
        exact hm (by simp [hzlow])
    rw [finsum_eq_sum_of_support_subset _ hsupport]
    have hterm (m : ℕ) (hm : m ∈ Finset.Icc 2 n) :
        coeff m (X ^ 2 * C) * coeff n (z ^ m) =
          (catalan (m - 2) : ℤ) * coeff (n - m) (F ^ m) := by
      obtain ⟨hm2, hmn⟩ := Finset.mem_Icc.mp hm
      have hc : coeff m (X ^ 2 * C) = (catalan (m - 2) : ℤ) := by
        rw [coeff_X_pow_mul', if_pos hm2]
        simp [C]
      have hz : coeff n (z ^ m) = coeff (n - m) (F ^ m) := by
        rw [show z ^ m = X ^ m * F ^ m by simp [z, mul_pow], coeff_X_pow_mul',
          if_pos hmn]
      rw [hc, hz]
    trans ∑ m ∈ Finset.Icc 2 n, (catalan (m - 2) : ℤ) * coeff (n - m) (F ^ m)
    · exact Finset.sum_congr rfl hterm
    apply Finset.sum_bij (fun m _ => m - 1)
    · intro m hm
      rcases Finset.mem_Icc.mp hm with ⟨hm2, hmn⟩
      apply Finset.mem_Icc.mpr
      omega
    · intro m hm j hj heq
      rcases Finset.mem_Icc.mp hm with ⟨hm2, _⟩
      rcases Finset.mem_Icc.mp hj with ⟨hj2, _⟩
      omega
    · intro k hk
      rcases Finset.mem_Icc.mp hk with ⟨hk1, hkn⟩
      refine ⟨k + 1, ?_, by omega⟩
      apply Finset.mem_Icc.mpr
      omega
    · intro m hm
      rcases Finset.mem_Icc.mp hm with ⟨hm2, hmn⟩
      have h1 : m - 1 - 1 = m - 2 := by omega
      have h2 : n - 1 - (m - 1) = n - m := by omega
      have h3 : m - 1 + 1 = m := by omega
      simp [h1, h2, h3]
  have hF : F = 1 + z + z ^ 2 * T := by
    ext n
    cases n with
    | zero =>
      simp [F, z, X, h0, hz0, coeff_zero_eq_constantCoeff]
    | succ n =>
      have hr := hrec (n + 1) (by omega)
      rw [map_add, map_add, hcoeff]
      have hzf : coeff (n + 1) z = (a n : ℤ) := by
        simp [z, X, F]
      simp [F, hzf, hr]
  have hB : (F - 1 - z) ^ 2 - z * (F - 1 - z) + z ^ 3 = 0 := by
    have he : F - 1 - z = z ^ 2 * T := by linear_combination hF
    rw [he]
    calc
      (z ^ 2 * T) ^ 2 - z * (z ^ 2 * T) + z ^ 3 =
          z ^ 3 * (z * T ^ 2 - T + 1) := by ring
      _ = 0 := by rw [show z * T ^ 2 - T + 1 = 0 by linear_combination -hT]; ring
  change 1 + (3 * X - 2) * F + (1 - X) * (1 - 2 * X) * F ^ 2 +
    X ^ 3 * F ^ 3 = 0
  have hz : z = X * F := rfl
  rw [hz] at hB
  convert hB using 1
  ring

end

end D5.S3.Combinatorics.ArrowThirtyTwoOneThreeAlgebra
