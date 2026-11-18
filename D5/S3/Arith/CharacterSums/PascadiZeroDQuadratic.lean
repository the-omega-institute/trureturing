/- GID: D5/S3/Arith/CharacterSums/PascadiZeroDQuadratic
   generality: G
   mirror-B: D5/B/S3/Arith/CharacterSums/PascadiZeroDQuadratic
   mirror-E: none(waiver:zero-dixon-quadratic-pencil)
   anchors: []
   utility: none
   digest: Zero Dixon residual gives a sixth-height quadratic pencil resultant gap. -/

import D5.S3.Arith.CharacterSums.PascadiQuadraticPrimitiveDirection
import D5.S3.Arith.CharacterSums.PascadiQuadraticDirection
import D5.S3.Arith.CharacterSums.PascadiSeventhHeightCover

/-! The constant-baseline identity uses the actual three-column-minor Dixon
determinant. A nonzero partner selects the primitive direction when the
baseline leading pair vanishes. -/

open Polynomial

namespace D5.S3.Arith.CharacterSums.PrimeCube

noncomputable section

open private bracket from D5.S3.Arith.CharacterSums.PascadiPrimeCubeSingularCover
open private singular_quadratic_leading_unit from
  D5.S3.Arith.CharacterSums.PascadiSeventhHeightCover

set_option maxHeartbeats 2000000 in
/-- At a constant leading baseline, the actual Dixon residual controls the
quadratic resultant through the partner leading minor, including its zero fiber. -/
theorem constant_base_dixon_quadratic_identity {R : Type*} [CommRing R]
    (l m q r s : Fin 3 → R) (hm : m 0 = 0) (hs : s 0 = 0) :
    l 0 * residual l m q r s = -(m 1 * s 2 - m 2 * s 1) *
      (pair l m q r s 1).resultant (pair l m q r s 2) 2 2 := by
  rw [quadratic_resultant_formula]
  simp only [pair_coefficients, coeff_add, coeff_C_mul, coeff_C, coeff_X,
    coeff_X_pow, residual, residualMatrix, bracket, Matrix.det_fin_three]
  norm_num
  simp only [hm, hs, zero_mul, mul_zero, add_zero, sub_zero]
  ring

private theorem primitive_direction_at (m s : Fin 3 → ℤ) (a : Fin 3) (J : ℝ)
    (hJ : 1 ≤ J) (hn : m a ≠ 0 ∨ s a ≠ 0)
    (hc : ∀ i, m a * s i - m i * s a = 0)
    (hm : ∀ i, |(m i : ℝ)| ≤ 3 * J)
    (hs : ∀ i, |(s i : ℝ)| ≤ J ^ 2) :
    ∃ (d n : ℤ) (k : Fin 3 → ℤ) (D : ℝ),
      (∀ i, m i = d * k i) ∧ (∀ i, s i = n * k i) ∧
      0 ≤ D ∧ (∀ i, |(k i : ℝ)| ≤ D) ∧
      |(d : ℝ)| * D ≤ 3 * J ∧ |(n : ℝ)| * D ≤ J ^ 2 ∧ D ≤ 3 * J ^ 2 := by
  let e := Equiv.swap (0 : Fin 3) a
  obtain ⟨d, n, k, D, _, hmd, hns, hD, hk, hd, hnD, hDu⟩ :=
    quadratic_coefficient_primitive_direction (m ∘ e) (s ∘ e) J hJ
      (by simpa [e] using hn) (by intro i; simpa [e] using hc (e i))
      (fun i => hm (e i)) (fun i => hs (e i))
  refine ⟨d, n, k ∘ e, D, ?_, ?_, hD, (fun i => hk (e i)), hd, hnD, hDu⟩
  · intro i
    simpa [e] using hmd (e i)
  · intro i
    simpa [e] using hns (e i)

/-- Genuine quadratic singular pencils with zero actual Dixon residual have
zero quadratic resultant at sixth height. The baseline may have m₀=s₀=0;
neither direction selection nor elimination assumes k₀ is nonzero. Only
the first quadratic needs a nonzero reduction. -/
theorem zero_dixon_quadratic_resultant_zero (l m q r s : Fin 3 → ℤ)
    (p : ℕ) [Fact p.Prime] (b : ℤ) (I J : ℝ) (hI : 1 ≤ I) (hJ : 1 ≤ J)
    (hl : ∀ i, |(l i : ℝ)| ≤ 3 * I) (hm : ∀ i, |(m i : ℝ)| ≤ 3 * J)
    (hq : ∀ i, |(q i : ℝ)| ≤ I ^ 2) (hr : ∀ i, |(r i : ℝ)| ≤ 2 * I * J)
    (hs : ∀ i, |(s i : ℝ)| ≤ J ^ 2)
    (h₁ : (pair l m q r s 1).natDegree = 2)
    (h₂ : (pair l m q r s 2).natDegree = 2)
    (hred : (pair l m q r s 1).map (Int.castRingHom (ZMod p)) ≠ 0)
    (hv₁ : (p : ℤ) ^ 3 ∣ (pair l m q r s 1).eval b)
    (hv₂ : (p : ℤ) ^ 3 ∣ (pair l m q r s 2).eval b)
    (hd₁ : (p : ℤ) ∣ (pair l m q r s 1).derivative.eval b)
    (hd₂ : (p : ℤ) ∣ (pair l m q r s 2).derivative.eval b)
    (hL : IsUnit ((l 0 + b * m 0 : ℤ) : ZMod p))
    (hD : residual l m q r s = 0)
    (hgap : 6804 * I ^ 6 * J ^ 4 < (p : ℝ) ^ 5) :
    (pair l m q r s 1).resultant (pair l m q r s 2) 2 2 = 0 := by
  have hlead := singular_quadratic_leading_unit _ p b hred h₁ hv₁ hd₁
  have hcoeff (i : Fin 3) : (pair l m q r s i).coeff 3 = m 0 * s i - m i * s 0 := by
    rw [pair_coefficients]
    simp only [coeff_add, coeff_C_mul, coeff_C, coeff_X, coeff_X_pow]
    norm_num
  have hc (i : Fin 3) : m 0 * s i - m i * s 0 = 0 := by
    fin_cases i
    · ring
    · rw [← hcoeff 1]; exact coeff_eq_zero_of_natDegree_lt (by omega)
    · rw [← hcoeff 2]; exact coeff_eq_zero_of_natDegree_lt (by omega)
  have hdir (a : Fin 3) (hn : m a ≠ 0 ∨ s a ≠ 0)
      (hcol : ∀ i, m a * s i - m i * s a = 0) :
      (pair l m q r s 1).resultant (pair l m q r s 2) 2 2 = 0 := by
    obtain ⟨d, n, k, D, hmd, hns, hD0, hk, hd, hnD, hDu⟩ :=
      primitive_direction_at m s a J hJ hn hcol hm hs
    have hmeq : m = fun i => d * k i := funext hmd
    have hseq : s = fun i => n * k i := funext hns
    rw [hmeq, hseq] at h₁ h₂ hv₁ hv₂ hd₁ hd₂ hlead hL ⊢
    exact quadratic_direction_resultant_zero l q r k d n p b I J D
      (by linarith) (by linarith) hD0 hq hr hl hk hd hnD hDu
      h₁ h₂ hv₁ hv₂ hd₁ hd₂ hlead hL hgap
  by_cases hz : m 0 = 0 ∧ s 0 = 0
  · by_cases hminor : m 1 * s 2 - m 2 * s 1 = 0
    · have hn : m 1 ≠ 0 ∨ s 1 ≠ 0 := by
        by_contra h
        push_neg at h
        apply hlead
        rw [pair_coefficients]
        simp [hz.1, hz.2, h.1, h.2]
      apply hdir 1 hn
      intro i
      fin_cases i
      · simp [hz.1, hz.2]
      · ring
      · exact hminor
    · have hid := constant_base_dixon_quadratic_identity l m q r s hz.1 hz.2
      rw [hD, mul_zero] at hid
      exact (mul_eq_zero.mp hid.symm).resolve_left (neg_ne_zero.mpr hminor)
  · exact hdir 0 (by tauto) hc

end
end D5.S3.Arith.CharacterSums.PrimeCube
