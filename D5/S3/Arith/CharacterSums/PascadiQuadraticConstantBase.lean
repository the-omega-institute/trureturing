/- GID: D5/S3/Arith/CharacterSums/PascadiQuadraticConstantBase
   generality: G
   mirror-B: D5/B/S3/Arith/CharacterSums/PascadiQuadraticConstantBase
   mirror-E: none(waiver:open-original-lattice-reduction)
   anchors: []
   utility: none
   digest: A constant-baseline quadratic pencil has a seventh-weight singular resultant gap. -/

import D5.S3.Arith.CharacterSums.PascadiPrimeCubeSingularCover

/-! The constant-baseline branch divides the padded quadratic resultant by the baseline
constant before applying its height gap. The oracle supplied the divide-before-specializing
route; the explicit integer quotient and the constant 14256 were derived independently.
This is a conditional elimination theorem, not the full original counting conjecture. -/

open Polynomial

namespace D5.S3.Arith.CharacterSums.PrimeCube

noncomputable section

private def cbD {R : Type*} [CommRing R] (l m : Fin 3 → R) : R :=
  m 1 * l 2 - l 1 * m 2

private def cbH {R : Type*} [CommRing R] (l m q r s : Fin 3 → R) : R :=
  l 0 * (s 1 * q 2 - q 1 * s 2) +
    q 0 * (l 1 * s 2 - s 1 * l 2) + r 0 * (q 1 * m 2 - m 1 * q 2)

private def cbE {R : Type*} [CommRing R] (l m q r s : Fin 3 → R) : R :=
  l 0 * (s 1 * r 2 - r 1 * s 2) + q 0 * (m 1 * s 2 - s 1 * m 2) +
    r 0 * (l 1 * s 2 - s 1 * l 2 + (r 1 * m 2 - m 1 * r 2))

private def cbF {R : Type*} [CommRing R] (l m q r : Fin 3 → R) : R :=
  l 0 * (r 1 * q 2 - q 1 * r 2) +
    q 0 * (l 1 * r 2 - r 1 * l 2 + (q 1 * m 2 - m 1 * q 2)) +
    r 0 * (q 1 * l 2 - l 1 * q 2)

private def cbQuotient {R : Type*} [CommRing R] (l m q r s : Fin 3 → R) : R :=
  l 0 * (cbH l m q r s ^ 2 - cbE l m q r s * cbF l m q r) +
    cbD l m * (2 * r 0 * q 0 * cbH l m q r s - q 0 ^ 2 * cbE l m q r s -
      r 0 ^ 2 * cbF l m q r)

set_option maxHeartbeats 2000000 in
-- Expand the fixed quadratic-resultant identity and its integer quotient.
private theorem constant_base_quotient_identity {R : Type*} [CommRing R]
    (l m q r s : Fin 3 → R) (hm : m 0 = 0) (hs : s 0 = 0) :
    (pair l m q r s 1).resultant (pair l m q r s 2) 2 2 =
      l 0 * cbQuotient l m q r s := by
  rw [quadratic_resultant_formula]
  simp only [pair_coefficients, coeff_add, coeff_C_mul, coeff_C, coeff_X, coeff_X_pow]
  norm_num
  simp only [hm, hs, zero_mul, mul_zero, add_zero, sub_zero,
    cbQuotient, cbD, cbH, cbE, cbF]
  ring

private theorem abs_mul_bound {x y A B : ℝ} (hx : |x| ≤ A) (hy : |y| ≤ B) :
    |x * y| ≤ A * B := by
  rw [abs_mul]
  exact mul_le_mul hx hy (abs_nonneg _) ((abs_nonneg _).trans hx)

private theorem abs_add_bound {x y A B : ℝ} (hx : |x| ≤ A) (hy : |y| ≤ B) :
    |x + y| ≤ A + B := (abs_add_le _ _).trans (add_le_add hx hy)

private theorem abs_sub_bound {x y A B : ℝ} (hx : |x| ≤ A) (hy : |y| ≤ B) :
    |x - y| ≤ A + B := (abs_sub _ _).trans (add_le_add hx hy)

private theorem quotient_uniform_height (l m q r s : Fin 3 → ℝ)
    (hl : ∀ i, |l i| ≤ 3) (hm : ∀ i, |m i| ≤ 3)
    (hq : ∀ i, |q i| ≤ 1) (hr : ∀ i, |r i| ≤ 2)
    (hs : ∀ i, |s i| ≤ 1) : |cbQuotient l m q r s| ≤ 14256 := by
  have bound (a b : Fin 3 → ℝ) (A B : ℝ)
      (ha : ∀ i, |a i| ≤ A) (hb : ∀ i, |b i| ≤ B) :
      |a 1 * b 2 - b 1 * a 2| ≤ A * B + B * A :=
    abs_sub_bound (abs_mul_bound (ha 1) (hb 2)) (abs_mul_bound (hb 1) (ha 2))
  have hml : |cbD l m| ≤ 18 := by
    have h := bound m l 3 3 hm hl
    norm_num [cbD] at h ⊢
    exact h
  have hsq : |s 1 * q 2 - q 1 * s 2| ≤ 2 := by
    have h := bound s q 1 1 hs hq
    norm_num at h
    exact h
  have hls : |l 1 * s 2 - s 1 * l 2| ≤ 6 := by
    have h := bound l s 3 1 hl hs
    norm_num at h
    exact h
  have hqm : |q 1 * m 2 - m 1 * q 2| ≤ 6 := by
    have h := bound q m 1 3 hq hm
    norm_num at h
    exact h
  have hsr : |s 1 * r 2 - r 1 * s 2| ≤ 4 := by
    have h := bound s r 1 2 hs hr
    norm_num at h
    exact h
  have hms : |m 1 * s 2 - s 1 * m 2| ≤ 6 := by
    have h := bound m s 3 1 hm hs
    norm_num at h
    exact h
  have hrm : |r 1 * m 2 - m 1 * r 2| ≤ 12 := by
    have h := bound r m 2 3 hr hm
    norm_num at h
    exact h
  have hrq : |r 1 * q 2 - q 1 * r 2| ≤ 4 := by
    have h := bound r q 2 1 hr hq
    norm_num at h
    exact h
  have hlr : |l 1 * r 2 - r 1 * l 2| ≤ 12 := by
    have h := bound l r 3 2 hl hr
    norm_num at h
    exact h
  have hql : |q 1 * l 2 - l 1 * q 2| ≤ 6 := by
    have h := bound q l 1 3 hq hl
    norm_num at h
    exact h
  have hH : |cbH l m q r s| ≤ 24 := by
    have h := abs_add_bound
      (abs_add_bound (abs_mul_bound (hl 0) hsq) (abs_mul_bound (hq 0) hls))
      (abs_mul_bound (hr 0) hqm)
    norm_num at h
    exact h
  have hE : |cbE l m q r s| ≤ 54 := by
    have h := abs_add_bound
      (abs_add_bound (abs_mul_bound (hl 0) hsr) (abs_mul_bound (hq 0) hms))
      (abs_mul_bound (hr 0) (abs_add_bound hls hrm))
    norm_num at h
    exact h
  have hF : |cbF l m q r| ≤ 42 := by
    have h := abs_add_bound
      (abs_add_bound (abs_mul_bound (hl 0) hrq)
        (abs_mul_bound (hq 0) (abs_add_bound hlr hqm)))
      (abs_mul_bound (hr 0) hql)
    norm_num at h
    exact h
  have hH2 : |cbH l m q r s ^ 2| ≤ 24 * 24 := by
    simpa only [pow_two] using abs_mul_bound hH hH
  have hq2 : |q 0 ^ 2| ≤ 1 * 1 := by
    simpa only [pow_two] using abs_mul_bound (hq 0) (hq 0)
  have hr2 : |r 0 ^ 2| ≤ 2 * 2 := by
    simpa only [pow_two] using abs_mul_bound (hr 0) (hr 0)
  have h := abs_add_bound
    (abs_mul_bound (hl 0) (abs_sub_bound hH2 (abs_mul_bound hE hF)))
    (abs_mul_bound hml (abs_sub_bound
      (abs_sub_bound
        (abs_mul_bound (abs_mul_bound (abs_mul_bound (by norm_num : |(2 : ℝ)| ≤ 2)
          (hr 0)) (hq 0)) hH)
        (abs_mul_bound hq2 hE)) (abs_mul_bound hr2 hF)))
  norm_num at h
  exact h

set_option maxHeartbeats 2000000 in
-- Normalize the explicit quotient's binary weights seven and four.
private theorem quotient_scale {R : Type*} [CommRing R] (l m q r s : Fin 3 → R)
    (a b : R) :
    cbQuotient (fun i => a * l i) (fun i => b * m i) (fun i => a ^ 2 * q i)
      (fun i => (a * b) * r i) (fun i => b ^ 2 * s i) =
      a ^ 7 * b ^ 4 * cbQuotient l m q r s := by
  simp only [cbQuotient, cbD, cbH, cbE, cbF]
  ring

private theorem quotient_height (l m q r s : Fin 3 → ℤ) (I J : ℝ)
    (hI : 1 ≤ I) (hJ : 1 ≤ J)
    (hl : ∀ i, |(l i : ℝ)| ≤ 3 * I) (hm : ∀ i, |(m i : ℝ)| ≤ 3 * J)
    (hq : ∀ i, |(q i : ℝ)| ≤ I ^ 2)
    (hr : ∀ i, |(r i : ℝ)| ≤ 2 * I * J)
    (hs : ∀ i, |(s i : ℝ)| ≤ J ^ 2) :
    |((cbQuotient l m q r s : ℤ) : ℝ)| ≤ 14256 * I ^ 7 * J ^ 4 := by
  have hIp : 0 < I := lt_of_lt_of_le zero_lt_one hI
  have hJp : 0 < J := lt_of_lt_of_le zero_lt_one hJ
  let L : Fin 3 → ℝ := fun i => (l i : ℝ) / I
  let M : Fin 3 → ℝ := fun i => (m i : ℝ) / J
  let Q : Fin 3 → ℝ := fun i => (q i : ℝ) / I ^ 2
  let R : Fin 3 → ℝ := fun i => (r i : ℝ) / (I * J)
  let S : Fin 3 → ℝ := fun i => (s i : ℝ) / J ^ 2
  have hb := quotient_uniform_height L M Q R S
    (fun i => by simpa [L, abs_div, abs_of_pos hIp] using (div_le_iff₀ hIp).mpr (hl i))
    (fun i => by simpa [M, abs_div, abs_of_pos hJp] using (div_le_iff₀ hJp).mpr (hm i))
    (fun i => by
      dsimp [Q]
      rw [abs_div, abs_of_pos (pow_pos hIp 2)]
      apply (div_le_iff₀ (pow_pos hIp 2)).mpr
      simpa using hq i)
    (fun i => by simpa [R, abs_div, abs_of_pos (mul_pos hIp hJp), mul_assoc] using
      (div_le_iff₀ (mul_pos hIp hJp)).mpr (by simpa [mul_assoc] using hr i))
    (fun i => by
      dsimp [S]
      rw [abs_div, abs_of_pos (pow_pos hJp 2)]
      apply (div_le_iff₀ (pow_pos hJp 2)).mpr
      simpa using hs i)
  have heq := quotient_scale L M Q R S I J
  have hc : ((cbQuotient l m q r s : ℤ) : ℝ) =
      cbQuotient (fun i => (l i : ℝ)) (fun i => (m i : ℝ))
        (fun i => (q i : ℝ)) (fun i => (r i : ℝ)) (fun i => (s i : ℝ)) := by
    simp [cbQuotient, cbD, cbH, cbE, cbF]
  have heq' : ((cbQuotient l m q r s : ℤ) : ℝ) =
      I ^ 7 * J ^ 4 * cbQuotient L M Q R S := by
    rw [hc]
    convert heq using 1
    congr 1 <;> funext i <;> dsimp [L, M, Q, R, S] <;> field_simp
  rw [heq', abs_mul, abs_of_pos (mul_pos (pow_pos hIp 7) (pow_pos hJp 4))]
  calc
    _ ≤ I ^ 7 * J ^ 4 * 14256 := mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by ring

/-- A genuine quadratic singular pencil with constant baseline L and linear baseline Q
has zero resultant under a seventh-weight gap, including all degenerate linear Q cases. -/
theorem constant_base_quadratic_singular_resultant_zero
    (l m q r s : Fin 3 → ℤ) (p : ℕ) [Fact p.Prime] (b : ℤ) (I J : ℝ)
    (hI : 1 ≤ I) (hJ : 1 ≤ J)
    (hl : ∀ i, |(l i : ℝ)| ≤ 3 * I) (hm : ∀ i, |(m i : ℝ)| ≤ 3 * J)
    (hq : ∀ i, |(q i : ℝ)| ≤ I ^ 2)
    (hr : ∀ i, |(r i : ℝ)| ≤ 2 * I * J)
    (hs : ∀ i, |(s i : ℝ)| ≤ J ^ 2)
    (hm0 : m 0 = 0) (hs0 : s 0 = 0) (hunit : IsUnit ((l 0 : ℤ) : ZMod p))
    (hd1 : (pair l m q r s 1).natDegree = 2)
    (hd2 : (pair l m q r s 2).natDegree = 2)
    (he : (p : ℤ) ^ 3 ∣ (pair l m q r s 1).eval b)
    (hk : (p : ℤ) ^ 3 ∣ (pair l m q r s 2).eval b)
    (hd : (p : ℤ) ∣ (pair l m q r s 1).derivative.eval b)
    (hg : (p : ℤ) ∣ (pair l m q r s 2).derivative.eval b)
    (hgap : 14256 * I ^ 7 * J ^ 4 < (p : ℝ) ^ 5) :
    (pair l m q r s 1).resultant (pair l m q r s 2) 2 2 = 0 := by
  have hdiv := quadratic_resultant_dvd_fifth
    (pair l m q r s 1) (pair l m q r s 2) b (p : ℤ) hd1 hd2 he hk hd hg
  rw [hd1, hd2, constant_base_quotient_identity l m q r s hm0 hs0] at hdiv
  have hcop : IsCoprime (p : ℤ) (l 0) :=
    (Nat.prime_iff_prime_int.mp (Fact.out : p.Prime)).coprime_iff_not_dvd.mpr
      (by simpa only [← ZMod.intCast_zmod_eq_zero_iff_dvd] using hunit.ne_zero)
  have hB : (p : ℤ) ^ 5 ∣ cbQuotient l m q r s :=
    (hcop.pow_left (m := 5)).dvd_of_dvd_mul_left hdiv
  have hbnd := quotient_height l m q r s I J hI hJ hl hm hq hr hs
  have hz : cbQuotient l m q r s = 0 := by
    by_contra hn
    have hv := Int.le_abs_of_dvd hn hB
    have hv' : (p : ℝ) ^ 5 ≤ |((cbQuotient l m q r s : ℤ) : ℝ)| := by
      exact_mod_cast hv
    exact (not_lt_of_ge hv') (hbnd.trans_lt hgap)
  rw [constant_base_quotient_identity l m q r s hm0 hs0, hz, mul_zero]

end

end D5.S3.Arith.CharacterSums.PrimeCube
