/- GID: D5/S3/Arith/CharacterSums/PascadiCubicQuadraticHeight
   generality: G
   mirror-B: D5/B/S3/Arith/CharacterSums/PascadiCubicQuadraticHeight
   mirror-E: none(waiver:open-original-lattice-reduction)
   anchors: []
   utility: none
   digest: A genuine cubic's quadratic factor improves mixed resultant height to weight six. -/

import D5.S3.Arith.CharacterSums.PascadiPrimeCubeSingularCover

/-! A genuine cubic has a nonconstant complementary factor. Its leading integer
coefficient gives an extra factor I/J in the scaled Gelfond estimate. The resulting
quadratic-factor bound is consumed by the mixed quadratic resultant estimate below.
This addresses the true-cubic factor branch, not the original counting conjecture. -/

open Polynomial

namespace D5.S3.Arith.CharacterSums.PrimeCube

noncomputable section

private theorem original_scale_cancel (I J : ℝ) (hJ : J ≠ 0)
    (j : ℕ) (hj : j ≤ 3) :
    I ^ (3 - j) * J ^ j * (I / J) ^ j = I ^ 3 := by
  interval_cases j <;> norm_num <;> field_simp

private theorem improved_scale_cancel (I J : ℝ) (hJ : J ≠ 0)
    (j : ℕ) (hj : j ≤ 2) :
    I ^ (2 - j) * J ^ (j + 1) * (I / J) ^ (j + 1) = I ^ 3 := by
  interval_cases j <;> norm_num <;> field_simp <;> ring

/-- A quadratic factor of a genuine integer cubic gains one factor J/I in its
weighted coefficient bound, because the complementary integer factor is linear. -/
theorem cubic_quadratic_factor_height (P R U : ℤ[X]) (hRU : P = R * U)
    (hdP : P.natDegree = 3) (hdR : R.natDegree = 2)
    (I J C : ℝ) (hJI : J ≤ I) (hJ : 1 ≤ J) (hC : 0 ≤ C)
    (hb : ∀ j ≤ P.natDegree, |(P.coeff j : ℝ)| ≤ C * I ^ (3 - j) * J ^ j) :
    ∀ j ≤ R.natDegree, |(R.coeff j : ℝ)| ≤ 8 * C * I ^ (2 - j) * J ^ (j + 1) := by
  have hP : P ≠ 0 := by
    intro hz
    rw [hz, natDegree_zero] at hdP
    omega
  have hU : U ≠ 0 := by intro hz; simp [hRU, hz] at hP
  have hR : R ≠ 0 := by intro hz; simp [hRU, hz] at hP
  have hdU : U.natDegree = 1 := by
    have hn := Polynomial.natDegree_mul hR hU
    rw [← hRU, hdP, hdR] at hn
    omega
  have hJp : 0 < J := lt_of_lt_of_le zero_lt_one hJ
  have hIp : 0 < I := hJp.trans_le hJI
  let a : ℝ := I / J
  have ha : 1 ≤ a := (one_le_div hJp).mpr hJI
  have hap : 0 < a := lt_of_lt_of_le zero_lt_one ha
  let t : ℂ[X] := Polynomial.C (a : ℂ) * Polynomial.X
  let F (f : ℤ[X]) : ℂ[X] := (f.map (Int.castRingHom ℂ)).comp t
  have hnorm (f : ℤ[X]) (j : ℕ) :
      ‖(F f).coeff j‖ = |(f.coeff j : ℝ)| * a ^ j := by
    simp [F, t, comp_C_mul_X_coeff, norm_pow, Complex.norm_intCast,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hap]
  have hdeg (f : ℤ[X]) : (F f).natDegree ≤ f.natDegree := by
    calc
      (F f).natDegree ≤ (f.map (Int.castRingHom ℂ)).natDegree * t.natDegree :=
        natDegree_comp_le
      _ ≤ f.natDegree * 1 := Nat.mul_le_mul natDegree_map_le
        ((natDegree_C_mul_le _ _).trans natDegree_X_le)
      _ = _ := Nat.mul_one _
  have hmul : F P = F R * F U := by simp [F, hRU, Polynomial.map_mul, mul_comp]
  have hds : (F R).natDegree + (F U).natDegree ≤ 3 := by
    have h₁ := hdeg R
    have h₂ := hdeg U
    omega
  have hUs : a ≤ (F U).supNorm := by
    have hc : (1 : ℝ) ≤ |(U.coeff U.natDegree : ℝ)| := by
      rw [coeff_natDegree]
      exact_mod_cast Int.one_le_abs (leadingCoeff_ne_zero.mpr hU)
    calc
      a = 1 * a := by ring
      _ ≤ |(U.coeff U.natDegree : ℝ)| * a :=
        mul_le_mul_of_nonneg_right hc hap.le
      _ = |(U.coeff U.natDegree : ℝ)| * a ^ U.natDegree := by rw [hdU, pow_one]
      _ = ‖(F U).coeff U.natDegree‖ := (hnorm U _).symm
      _ ≤ (F U).supNorm := (F U).le_supNorm _
  have hPs : (F P).supNorm ≤ C * I ^ 3 := by
    obtain ⟨j, hj⟩ := (F P).exists_eq_supNorm
    rw [hj, hnorm]
    by_cases hjd : j ≤ P.natDegree
    · calc
        |(P.coeff j : ℝ)| * a ^ j ≤ (C * I ^ (3 - j) * J ^ j) * a ^ j := by
          gcongr
          exact hb j hjd
        _ = C * I ^ 3 := by
          rw [show (C * I ^ (3 - j) * J ^ j) * a ^ j =
            C * (I ^ (3 - j) * J ^ j * (I / J) ^ j) by dsimp [a]; ring]
          rw [original_scale_cancel I J hJp.ne' j (by omega)]
    · rw [coeff_eq_zero_of_natDegree_lt (by omega)]
      simp only [Int.cast_zero, abs_zero, zero_mul]
      positivity
  have hRs : (F R).supNorm * a ≤ 8 * C * I ^ 3 := by
    have hg := Polynomial.supNorm_mul_supNorm_le_two_pow (F R) (F U)
    rw [← hmul] at hg
    have hpow : (2 : ℝ) ^ ((F R).natDegree + (F U).natDegree) ≤ 8 := by
      calc
        (2 : ℝ) ^ ((F R).natDegree + (F U).natDegree) ≤ (2 : ℝ) ^ 3 :=
          pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hds
        _ = _ := by norm_num
    calc
      (F R).supNorm * a ≤ (F R).supNorm * (F U).supNorm :=
        mul_le_mul_of_nonneg_left hUs (F R).supNorm_nonneg
      _ ≤ _ := hg
      _ ≤ 8 * (C * I ^ 3) :=
        mul_le_mul hpow hPs (F P).supNorm_nonneg (by norm_num)
      _ = _ := by ring
  intro j hj
  have hj2 : j ≤ 2 := by omega
  apply (mul_le_mul_iff_left₀ (pow_pos hap (j + 1))).mp
  calc
    |(R.coeff j : ℝ)| * a ^ (j + 1) = ‖(F R).coeff j‖ * a := by
      rw [hnorm, pow_succ]
      ring
    _ ≤ (F R).supNorm * a :=
      mul_le_mul_of_nonneg_right ((F R).le_supNorm j) hap.le
    _ ≤ 8 * C * I ^ 3 := hRs
    _ = (8 * C * I ^ (2 - j) * J ^ (j + 1)) * a ^ (j + 1) := by
      rw [show (8 * C * I ^ (2 - j) * J ^ (j + 1)) * a ^ (j + 1) =
        (8 * C) * (I ^ (2 - j) * J ^ (j + 1) * (I / J) ^ (j + 1)) by
        dsimp [a]
        ring]
      rw [improved_scale_cancel I J hJp.ne' j hj2]

private theorem abs_mul_bound {x y A B : ℝ} (hx : |x| ≤ A) (hy : |y| ≤ B) :
    |x * y| ≤ A * B := by
  rw [abs_mul]
  exact mul_le_mul hx hy (abs_nonneg _) ((abs_nonneg _).trans hx)

private theorem abs_sub_bound {x y A B : ℝ} (hx : |x| ≤ A) (hy : |y| ≤ B) :
    |x - y| ≤ A + B := (abs_sub _ _).trans (add_le_add hx hy)

/-- The improved factor bound is consumed by a sixth-weight mixed resultant bound:
one quadratic comes from a genuine cubic, while the other has the original height. -/
theorem cubic_quadratic_mixed_resultant_height (P R U S : ℤ[X]) (hRU : P = R * U)
    (hdP : P.natDegree = 3) (hdR : R.natDegree = 2) (hdS : S.natDegree = 2)
    (I J C : ℝ) (hJI : J ≤ I) (hJ : 1 ≤ J) (hC : 0 ≤ C)
    (hb : ∀ j ≤ P.natDegree, |(P.coeff j : ℝ)| ≤ C * I ^ (3 - j) * J ^ j)
    (hS : ∀ j ≤ S.natDegree, |(S.coeff j : ℝ)| ≤ 8 * C * I ^ (3 - j) * J ^ j) :
    |((R.resultant S 2 2 : ℤ) : ℝ)| ≤ 24 * (8 * C) ^ 4 * (I * J) ^ 6 := by
  have hR := cubic_quadratic_factor_height P R U hRU hdP hdR I J C hJI hJ hC hb
  have hR0 := hR 0 (by omega)
  have hR1 := hR 1 (by omega)
  have hR2 := hR 2 (by omega)
  have hS0 := hS 0 (by omega)
  have hS1 := hS 1 (by omega)
  have hS2 := hS 2 (by omega)
  norm_num at hR0 hR1 hR2 hS0 hS1 hS2
  let A : ℝ := 8 * C
  have hminor20 :
      |(R.coeff 2 : ℝ) * (S.coeff 0 : ℝ) - (S.coeff 2 : ℝ) * (R.coeff 0 : ℝ)| ≤
        2 * A ^ 2 * I ^ 3 * J ^ 3 := by
    have h := abs_sub_bound (abs_mul_bound hR2 hS0) (abs_mul_bound hS2 hR0)
    convert h using 1 <;> dsimp [A] <;> ring
  have hminor21 :
      |(R.coeff 2 : ℝ) * (S.coeff 1 : ℝ) - (S.coeff 2 : ℝ) * (R.coeff 1 : ℝ)| ≤
        2 * A ^ 2 * I ^ 2 * J ^ 4 := by
    have h := abs_sub_bound (abs_mul_bound hR2 hS1) (abs_mul_bound hS2 hR1)
    convert h using 1 <;> dsimp [A] <;> ring
  have hminor10 :
      |(R.coeff 1 : ℝ) * (S.coeff 0 : ℝ) - (R.coeff 0 : ℝ) * (S.coeff 1 : ℝ)| ≤
        2 * A ^ 2 * I ^ 4 * J ^ 2 := by
    have h := abs_sub_bound (abs_mul_bound hR1 hS0) (abs_mul_bound hR0 hS1)
    convert h using 1 <;> dsimp [A] <;> ring
  have hsquare :
      |((R.coeff 2 : ℝ) * (S.coeff 0 : ℝ) -
          (S.coeff 2 : ℝ) * (R.coeff 0 : ℝ)) ^ 2| ≤
        (2 * A ^ 2 * I ^ 3 * J ^ 3) ^ 2 := by
    simpa only [pow_two] using abs_mul_bound hminor20 hminor20
  have h := abs_sub_bound hsquare (abs_mul_bound hminor21 hminor10)
  have hstrong : |((R.resultant S 2 2 : ℤ) : ℝ)| ≤
      8 * A ^ 4 * (I * J) ^ 6 := by
    rw [quadratic_resultant_formula]
    push_cast
    convert h using 1 <;> ring
  calc
    _ ≤ 8 * A ^ 4 * (I * J) ^ 6 := hstrong
    _ ≤ 24 * A ^ 4 * (I * J) ^ 6 := by
      have : 0 ≤ A ^ 4 * (I * J) ^ 6 := by positivity
      nlinarith only [this]
    _ = _ := rfl

end

end D5.S3.Arith.CharacterSums.PrimeCube
