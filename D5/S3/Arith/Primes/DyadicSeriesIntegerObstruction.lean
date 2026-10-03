/- GID: D5/S3/Arith/Primes/DyadicSeriesIntegerObstruction
   generality: I
   mirror-B: D5/B/S3/Arith/Primes/DyadicSeriesIntegerObstruction
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: A dyadic coefficient scale and analytic tail exclude integer evaluations. -/

import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.Primes.DyadicSeriesIntegerObstruction

open scoped BigOperators

set_option maxHeartbeats 1000000 in
/-- An analytic series with odd dyadically scaled coefficients cannot take the
stated integer value once its first omitted term dominates its remainder. -/
theorem dyadic_series_integer_obstruction (s : ℕ → ℂ) (r : ℕ) (hr : 1 ≤ r) (x : ℤ) (hx : 2 < x)
    (μ : ℂ)
    (hs0 : s 0 = 1)
    (hscaled : ∀ j : ℕ, 0 < j → ∃ z : ℤ, Odd z ∧ (2 : ℂ) ^ (j + padicValNat 2 j.factorial) * s j = (z : ℂ))
    (hsupper : ∀ j : ℕ, ‖s j‖ ≤ (Real.sqrt (2 : ℝ)) ^ r * (4 : ℝ) ^ j)
    (hsum : HasSum (fun j : ℕ => s j * (((x : ℂ) ^ 2)⁻¹) ^ j) μ)
    (hgap : 128 * (6 : ℝ) ^ r < (x : ℝ) ^ 2 - 4) :
    ∀ M : ℤ, (x : ℂ) ^ r * μ ≠ (M : ℂ) := by
  classical
  have hslower (j : ℕ) (hj : 0 < j) : 1 / (2 : ℝ)^(j + padicValNat 2 j.factorial) ≤ ‖s j‖ := by
    obtain ⟨z, hzOdd, hzEq⟩ := hscaled j hj
    have hzNe : z ≠ 0 := by
      intro hz
      rw [hz] at hzOdd
      norm_num at hzOdd
    have hnorm : (1 : ℝ) ≤ ‖(z : ℂ)‖ := by
      rw [Complex.norm_intCast]
      exact_mod_cast (Int.one_le_abs hzNe)
    have hnormEq := congrArg norm hzEq
    norm_num [norm_mul, norm_pow] at hnormEq
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2^(j + padicValNat 2 j.factorial))).2
    simp only [Complex.norm_intCast] at hnorm
    nlinarith [hnorm, hnormEq]
  have truncationConstants (r : ℕ) (hr : 1 ≤ r) :
      let J := (r + 1) / 2
      (2 : ℝ)^(J + padicValNat 2 J.factorial) * (Real.sqrt (2 : ℝ))^r * (4 : ℝ)^(J + 1) ≤ 8 * (6 : ℝ)^r ∧
      (2 : ℝ)^((J + 1) + padicValNat 2 (J + 1).factorial) * (Real.sqrt (2 : ℝ))^r * (4 : ℝ)^(J + 2) ≤
        128 * (6 : ℝ)^r := by
    let J : ℕ := (r + 1) / 2
    change (2 : ℝ)^(J + padicValNat 2 J.factorial) * (Real.sqrt (2 : ℝ))^r * (4 : ℝ)^(J + 1) ≤ 8 * (6 : ℝ)^r ∧
      (2 : ℝ)^((J + 1) + padicValNat 2 (J + 1).factorial) * (Real.sqrt (2 : ℝ))^r * (4 : ℝ)^(J + 2) ≤ 128 * (6 : ℝ)^r

    have hJpos : 0 < J := by dsimp [J]; omega
    have hJle : 2 * J ≤ r + 1 := by dsimp [J]; omega
    have heJ : J + padicValNat 2 J.factorial ≤ r := by
      have hv := padicValNat_factorial_lt_of_ne_zero 2 hJpos.ne'
      omega
    have heJ1 : (J + 1) + padicValNat 2 (J + 1).factorial ≤ r + 2 := by
      have hv := padicValNat_factorial_lt_of_ne_zero 2 (by omega : J + 1 ≠ 0)
      omega

    have hsqrt : Real.sqrt (2 : ℝ) ≤ 3 / 2 := by
      have hsq := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
      have hnonneg := Real.sqrt_nonneg (2 : ℝ)
      nlinarith
    have hC : (Real.sqrt (2 : ℝ))^r ≤ (3 / 2 : ℝ)^r := pow_le_pow_left₀ (Real.sqrt_nonneg _) hsqrt r

    have hfour (a : ℕ) : (4 : ℝ)^a = (2 : ℝ)^(2 * a) := by
      calc
        (4 : ℝ)^a = ((2 : ℝ)^2)^a := by norm_num
        _ = (2 : ℝ)^(2 * a) := by rw [pow_mul]
    have hfour1 : (4 : ℝ)^(J + 1) ≤ 8 * (2 : ℝ)^r := by
      calc
        (4 : ℝ)^(J + 1) = (2 : ℝ)^(2 * (J + 1)) := hfour _
        _ ≤ (2 : ℝ)^(r + 3) := pow_le_pow_right₀ (by norm_num) (by omega)
        _ = 8 * (2 : ℝ)^r := by rw [pow_add]; norm_num <;> ring
    have hfour2 : (4 : ℝ)^(J + 2) ≤ 32 * (2 : ℝ)^r := by
      calc
        (4 : ℝ)^(J + 2) = (2 : ℝ)^(2 * (J + 2)) := hfour _
        _ ≤ (2 : ℝ)^(r + 5) := pow_le_pow_right₀ (by norm_num) (by omega)
        _ = 32 * (2 : ℝ)^r := by rw [pow_add]; norm_num <;> ring

    have hD1 : (2 : ℝ)^(J + padicValNat 2 J.factorial) ≤ (2 : ℝ)^r := pow_le_pow_right₀ (by norm_num) heJ
    have hD2 : (2 : ℝ)^((J + 1) + padicValNat 2 (J + 1).factorial) ≤ 4 * (2 : ℝ)^r := by
      calc
        _ ≤ (2 : ℝ)^(r + 2) := pow_le_pow_right₀ (by norm_num) heJ1
        _ = 4 * (2 : ℝ)^r := by rw [pow_add]; norm_num <;> ring

    have hsix : (2 : ℝ)^r * (3 / 2 : ℝ)^r * (2 : ℝ)^r = (6 : ℝ)^r := by
      have hbase : (6 : ℝ) = 2 * (3 / 2) * 2 := by norm_num
      rw [hbase, mul_pow, mul_pow]
    constructor
    · calc
        (2 : ℝ)^(J + padicValNat 2 J.factorial) * (Real.sqrt (2 : ℝ))^r * (4 : ℝ)^(J + 1) ≤
          (2 : ℝ)^r * (3 / 2 : ℝ)^r * (4 : ℝ)^(J + 1) := by
            apply mul_le_mul_of_nonneg_right _ (pow_nonneg (by norm_num) _)
            exact mul_le_mul hD1 hC
              (pow_nonneg (Real.sqrt_nonneg _) _)
              (pow_nonneg (by norm_num) _)
        _ ≤ (2 : ℝ)^r * (3 / 2 : ℝ)^r * (8 * (2 : ℝ)^r) := by
          exact mul_le_mul_of_nonneg_left hfour1
            (mul_nonneg (pow_nonneg (by norm_num) _) (pow_nonneg (by norm_num) _))
        _ = 8 * (6 : ℝ)^r := by rw [← hsix]; ring
    · calc
        (2 : ℝ)^((J + 1) + padicValNat 2 (J + 1).factorial) * (Real.sqrt (2 : ℝ))^r * (4 : ℝ)^(J + 2) ≤
          (4 * (2 : ℝ)^r) * (3 / 2 : ℝ)^r * (4 : ℝ)^(J + 2) := by
            apply mul_le_mul_of_nonneg_right _ (pow_nonneg (by norm_num) _)
            exact mul_le_mul hD2 hC
              (pow_nonneg (Real.sqrt_nonneg _) _)
              (by positivity)
        _ ≤ (4 * (2 : ℝ)^r) * (3 / 2 : ℝ)^r * (32 * (2 : ℝ)^r) := by
          exact mul_le_mul_of_nonneg_left hfour2
            (mul_nonneg (by positivity) (pow_nonneg (by norm_num) _))
        _ = 128 * (6 : ℝ)^r := by rw [← hsix]; ring
  obtain ⟨hconst1, hconst2⟩ := truncationConstants r hr
  let J : ℕ := (r + 1) / 2
  let e : ℕ → ℕ := fun j => j + padicValNat 2 j.factorial
  let C : ℝ := (Real.sqrt (2 : ℝ)) ^ r
  let q : ℝ := (x : ℝ) ^ 2
  let y : ℂ := ((x : ℂ) ^ 2)⁻¹
  let f : ℕ → ℂ := fun j => s j * y ^ j
  let tail : ℕ → ℂ := fun N => ∑' n : ℕ, f (n + N)
  let D : ℂ := (2 : ℂ) ^ (e J)
  let W : ℂ := D * (x : ℂ) ^ (2 * J) * μ
  let t : ℂ := ∑ j ∈ Finset.range (J + 1), (D * s j) * (x : ℂ) ^ (2 * (J - j))
  change HasSum f μ at hsum

  have hJpos : 0 < J := by dsimp [J]; omega
  have hrJ : r ≤ 2 * J := by dsimp [J]; omega
  have hxreal : 2 < (x : ℝ) := by exact_mod_cast hx
  have hxreal0 : 0 < (x : ℝ) := by linarith
  have hxC0 : (x : ℂ) ≠ 0 := by exact_mod_cast (show x ≠ 0 by omega)
  have hqpos : 0 < q := by dsimp [q]; positivity
  have hq4 : 4 < q := by dsimp [q]; nlinarith
  have hq4pos : 0 < q - 4 := by linarith
  have hq4ne : q - 4 ≠ 0 := ne_of_gt hq4pos
  have hyNorm : ‖y‖ = q⁻¹ := by
    change ‖((x : ℂ) ^ 2)⁻¹‖ = (((x : ℝ) ^ 2)⁻¹)
    simp [norm_inv, norm_pow, Complex.norm_intCast, abs_of_pos hxreal0]
  have hyq : 4 * ‖y‖ < 1 := by
    rw [hyNorm]
    have hh : (4 : ℝ) / q < 1 := (div_lt_iff₀ hqpos).2 (by linarith)
    simpa [div_eq_mul_inv] using hh
  have hySmall : ‖y‖ < (1 / 4 : ℝ) := by linarith
  have hgeomDen : 1 - 4 / q ≠ 0 := by
    have : 4 / q < 1 := by simpa [div_eq_mul_inv, hyNorm] using hyq
    linarith
  have hCnonneg : 0 ≤ C := by dsimp [C]; positivity
  have hDnorm : ‖D‖ = (2 : ℝ) ^ (e J) := by simp [D, norm_pow]
  have hXnorm (n : ℕ) : ‖(x : ℂ) ^ (2 * n)‖ = q ^ n := by
    change ‖(x : ℂ) ^ (2 * n)‖ = ((x : ℝ) ^ 2) ^ n
    rw [norm_pow, Complex.norm_intCast, abs_of_pos hxreal0, pow_mul]

  have heStrict : StrictMono e := by
    intro m n hmn
    have hfac := Nat.factorial_dvd_factorial hmn.le
    have hval : padicValNat 2 m.factorial ≤ padicValNat 2 n.factorial :=
      (padicValNat_dvd_iff_le (p := 2) (Nat.factorial_ne_zero n)).1
        (dvd_trans (pow_padicValNat_dvd (p := 2) (n := m.factorial)) hfac)
    dsimp [e]
    omega
  have he0 : e 0 = 0 := by simp [e]
  have hall : ∀ j : ℕ, ∃ z : ℤ, (2 : ℂ) ^ (e j) * s j = (z : ℂ) := by
    intro j
    by_cases hj : 0 < j
    · obtain ⟨z, _, hz⟩ := hscaled j hj
      exact ⟨z, hz⟩
    · have hj0 : j = 0 := by omega
      subst j
      exact ⟨1, by simp [he0, hs0]⟩
  choose z hz using hall
  let d : ℕ → ℤ := fun j =>
    (2 : ℤ) ^ (e J - e j) * z j * x ^ (2 * (J - j))
  have htermInt (j : ℕ) (hj : j ≤ J) : (D * s j) * (x : ℂ) ^ (2 * (J - j)) = (d j : ℂ) := by
    have hej : e j ≤ e J := heStrict.monotone hj
    have he : e J = (e J - e j) + e j := by omega
    change (((2 : ℂ) ^ (e J)) * s j) * _ = _
    calc
      (((2 : ℂ) ^ (e J)) * s j) * (x : ℂ) ^ (2 * (J - j)) = (2 : ℂ) ^ (e J - e j) * ((2 : ℂ) ^ (e j) * s j) *
              (x : ℂ) ^ (2 * (J - j)) := by
        conv_lhs => rw [he, pow_add]
        ring
      _ = (d j : ℂ) := by
        rw [hz j]
        dsimp [d]
        push_cast
        ring
  have htInt : ∃ Z : ℤ, t = (Z : ℂ) := by
    refine ⟨∑ j ∈ Finset.range (J + 1), d j, ?_⟩
    change (∑ j ∈ Finset.range (J + 1), (D * s j) * (x : ℂ) ^ (2 * (J - j))) = _
    push_cast
    apply Finset.sum_congr rfl
    intro j hj
    exact htermInt j (by have := Finset.mem_range.mp hj; omega)

  have htail (N : ℕ) : ‖tail N‖ ≤ C * (4 * ‖y‖) ^ N / (1 - 4 * ‖y‖) := by
    let a : ℝ := 4 * ‖y‖
    have ha0 : 0 ≤ a := by dsimp [a]; positivity
    have ha1 : a < 1 := by simpa [a] using hyq
    have hbound (n : ℕ) : ‖f (n + N)‖ ≤ (C * a ^ N) * a ^ n := by
      calc
        ‖f (n + N)‖ = ‖s (n + N)‖ * ‖y‖ ^ (n + N) := by
          simp [f]
        _ ≤ (C * (4 : ℝ) ^ (n + N)) * ‖y‖ ^ (n + N) := mul_le_mul_of_nonneg_right (hsupper (n + N))
            (pow_nonneg (norm_nonneg y) _)
        _ = (C * a ^ N) * a ^ n := by
          dsimp [a, C]
          simp only [pow_add, mul_pow]
          ring
    have hgeom : Summable (fun n : ℕ => (C * a ^ N) * a ^ n) := (summable_geometric_of_lt_one ha0 ha1).mul_left _
    have hnorm : Summable (fun n : ℕ => ‖f (n + N)‖) := Summable.of_nonneg_of_le (fun n => norm_nonneg _) hbound hgeom
    calc
      ‖tail N‖ ≤ ∑' n : ℕ, ‖f (n + N)‖ := by
        simpa [tail] using norm_tsum_le_tsum_norm hnorm
      _ ≤ ∑' n : ℕ, (C * a ^ N) * a ^ n := hnorm.tsum_le_tsum hbound hgeom
      _ = (C * a ^ N) * (1 - a)⁻¹ := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one ha0 ha1]
      _ = C * (4 * ‖y‖) ^ N / (1 - 4 * ‖y‖) := by
        dsimp [a]
        ring

  have hwhole : Summable f := hsum.summable
  have hμsplit : (∑ j ∈ Finset.range (J + 1), f j) + tail (J + 1) = μ := by
    exact (hwhole.sum_add_tsum_nat_add (J + 1)).trans hsum.tsum_eq
  have hXpow (n : ℕ) : (x : ℂ) ^ (2 * n) = ((x : ℂ) ^ 2) ^ n := by
    rw [pow_mul]
  have hfinite : (D * (x : ℂ) ^ (2 * J)) * (∑ j ∈ Finset.range (J + 1), f j) = t := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    have hjJ : j ≤ J := by have := Finset.mem_range.mp hj; omega
    have hpow : (x : ℂ) ^ (2 * J) * y ^ j = (x : ℂ) ^ (2 * (J - j)) := by
      rw [hXpow J, hXpow (J - j)]
      dsimp [y]
      calc
        ((x : ℂ) ^ 2) ^ J * (((x : ℂ) ^ 2)⁻¹) ^ j = ((x : ℂ) ^ 2) ^ (J - j) *
            (((x : ℂ) ^ 2) ^ j * (((x : ℂ) ^ 2)⁻¹) ^ j) := by
          rw [← pow_mul_pow_sub ((x : ℂ) ^ 2) hjJ]
          ring
        _ = ((x : ℂ) ^ 2) ^ (J - j) := by
          rw [← mul_pow, mul_inv_cancel₀ (pow_ne_zero 2 hxC0), one_pow, mul_one]
    change (D * (x : ℂ) ^ (2 * J)) * (s j * y ^ j) = (D * s j) * (x : ℂ) ^ (2 * (J - j))
    calc
      (D * (x : ℂ) ^ (2 * J)) * (s j * y ^ j) = (D * s j) * ((x : ℂ) ^ (2 * J) * y ^ j) := by ring
      _ = (D * s j) * (x : ℂ) ^ (2 * (J - j)) := by rw [hpow]
  have hWtail : W - t = (D * (x : ℂ) ^ (2 * J)) * tail (J + 1) := by
    dsimp [W]
    calc
      D * (x : ℂ) ^ (2 * J) * μ - t = (D * (x : ℂ) ^ (2 * J)) *
            ((∑ j ∈ Finset.range (J + 1), f j) + tail (J + 1)) - t := by
          rw [hμsplit]
      _ = (D * (x : ℂ) ^ (2 * J)) * tail (J + 1) := by
          rw [mul_add, hfinite]
          ring

  have hdenStrong : 128 * (6 : ℝ) ^ r < q - 4 := by
    simpa [q] using hgap
  have hdenWeak : 8 * (6 : ℝ) ^ r < q - 4 := by
    have : 8 * (6 : ℝ) ^ r ≤ 128 * (6 : ℝ) ^ r := by
      gcongr
      norm_num
    exact lt_of_le_of_lt this hdenStrong

  have hscaleNorm : ‖D * (x : ℂ) ^ (2 * J)‖ = (2 : ℝ) ^ (e J) * q ^ J := by
    rw [norm_mul, hDnorm, hXnorm]
  have htailAlgebra : q ^ J * (C * (4 / q) ^ (J + 1) / (1 - 4 / q)) = C * (4 : ℝ) ^ (J + 1) / (q - 4) := by
    rw [div_pow]
    simp only [pow_succ]
    field_simp [ne_of_gt hqpos, hq4ne, hgeomDen] <;> ring
  have hsmall : ‖W - t‖ < 1 := by
    have hnum : (2 : ℝ) ^ (e J) * C * (4 : ℝ) ^ (J + 1) ≤ 8 * (6 : ℝ) ^ r := by
      simpa only [J, e, C] using hconst1
    calc
      ‖W - t‖ = ((2 : ℝ) ^ (e J) * q ^ J) * ‖tail (J + 1)‖ := by
        rw [hWtail, norm_mul, hscaleNorm]
      _ ≤ ((2 : ℝ) ^ (e J) * q ^ J) * (C * (4 * ‖y‖) ^ (J + 1) / (1 - 4 * ‖y‖)) :=
        mul_le_mul_of_nonneg_left (htail (J + 1)) (by positivity)
      _ = ((2 : ℝ) ^ (e J) * C * (4 : ℝ) ^ (J + 1)) / (q - 4) := by
        calc
          ((2 : ℝ) ^ (e J) * q ^ J) * (C * (4 * ‖y‖) ^ (J + 1) / (1 - 4 * ‖y‖)) = (2 : ℝ) ^ (e J) *
                (q ^ J * (C * (4 / q) ^ (J + 1) / (1 - 4 / q))) := by
            rw [hyNorm]
            simp only [div_eq_mul_inv]
            ring
          _ = (2 : ℝ) ^ (e J) * (C * (4 : ℝ) ^ (J + 1) / (q - 4)) := by rw [htailAlgebra]
          _ = ((2 : ℝ) ^ (e J) * C * (4 : ℝ) ^ (J + 1)) / (q - 4) := by ring
      _ ≤ (8 * (6 : ℝ) ^ r) / (q - 4) := (div_le_div_iff₀ hq4pos hq4pos).2 (by nlinarith [hnum, hq4pos])
      _ < 1 := (div_lt_iff₀ hq4pos).2 (by simpa using hdenWeak)

  let N : ℕ := J + 1
  let Dnext : ℝ := (2 : ℝ) ^ (e N)
  have hNpos : 0 < N := by dsimp [N]; omega
  have hDnextPos : 0 < Dnext := by dsimp [Dnext]; positivity
  have hnextNum : Dnext * C * (4 : ℝ) ^ (J + 2) ≤ 128 * (6 : ℝ) ^ r := by
    simpa only [N, Dnext, J, e, C] using hconst2
  have hnextGap : Dnext * (C * (4 : ℝ) ^ (J + 2)) < q - 4 := by
    nlinarith [hnextNum, hdenStrong]
  have hnextCoef : C * (4 : ℝ) ^ (J + 2) / (q - 4) < 1 / Dnext := by
    apply (div_lt_div_iff₀ hq4pos hDnextPos).2
    nlinarith [hnextGap]
  have hrestAlgebra : C * (4 / q) ^ (J + 2) / (1 - 4 / q) = (C * (4 : ℝ) ^ (J + 2) / (q - 4)) * (q⁻¹) ^ (J + 1) := by
    rw [div_pow]
    simp only [pow_succ]
    simp only [inv_pow]
    field_simp [ne_of_gt hqpos, hq4ne, hgeomDen] <;> ring
  have hrestLt : C * (4 * ‖y‖) ^ (J + 2) / (1 - 4 * ‖y‖) < (1 / Dnext) * ‖y‖ ^ N := by
    rw [hyNorm]
    change C * (4 / q) ^ (J + 2) / (1 - 4 / q) < (1 / Dnext) * (q⁻¹) ^ (J + 1)
    rw [hrestAlgebra]
    exact mul_lt_mul_of_pos_right hnextCoef (pow_pos (inv_pos.mpr hqpos) _)
  have hfirstLower : (1 / Dnext) * ‖y‖ ^ N ≤ ‖f N‖ := by
    calc
      (1 / Dnext) * ‖y‖ ^ N ≤ ‖s N‖ * ‖y‖ ^ N := mul_le_mul_of_nonneg_right (by simpa [Dnext, e] using hslower N hNpos)
          (pow_nonneg (norm_nonneg y) _)
      _ = ‖f N‖ := by simp [f]
  have hfirstDominates : ‖tail (N + 1)‖ < ‖f N‖ := lt_of_le_of_lt (htail (N + 1)) (lt_of_lt_of_le (by
      simpa [N, Nat.add_assoc] using hrestLt) hfirstLower)
  have hshift : Summable (fun n : ℕ => f (n + N)) := (summable_nat_add_iff N).2 hwhole
  have hsplit : tail N = f N + tail (N + 1) := by
    simpa [tail, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      hshift.tsum_eq_zero_add
  have htailNonzero : tail N ≠ 0 := by
    intro hzero
    have hzero' : f N + tail (N + 1) = 0 := hsplit.symm.trans hzero
    have heq := add_eq_zero_iff_eq_neg.mp hzero'
    have hnorm : ‖f N‖ = ‖tail (N + 1)‖ := by rw [heq, norm_neg]
    exact (not_lt_of_ge hnorm.le) hfirstDominates
  have hWtailNonzero : W - t ≠ 0 := by
    rw [hWtail]
    exact mul_ne_zero
      (mul_ne_zero (pow_ne_zero _ (by norm_num : (2 : ℂ) ≠ 0)) (pow_ne_zero _ hxC0))
      (by simpa only [N] using htailNonzero)

  obtain ⟨Z, htZ⟩ := htInt
  intro M hM
  let K : ℤ := (2 : ℤ) ^ (e J) * x ^ (2 * J - r) * M
  have hWZ : W = (K : ℂ) := by
    have hexp : 2 * J = (2 * J - r) + r := by omega
    calc
      W = (2 : ℂ) ^ (e J) * (x : ℂ) ^ (2 * J) * μ := rfl
      _ = (2 : ℂ) ^ (e J) * (x : ℂ) ^ (2 * J - r) * ((x : ℂ) ^ r * μ) := by
        conv_lhs => rw [hexp, pow_add]
        ring
      _ = (2 : ℂ) ^ (e J) * (x : ℂ) ^ (2 * J - r) * (M : ℂ) := by
        rw [hM]
      _ = (K : ℂ) := by dsimp [K]; push_cast; ring
  have hsmallZ : |K - Z| < 1 := by
    have hh : |((K - Z : ℤ) : ℝ)| < (1 : ℝ) := by
      simpa [hWZ, htZ, ← Int.cast_sub, Complex.norm_intCast] using hsmall
    exact_mod_cast hh
  have hzeroZ : K - Z = 0 := Int.abs_lt_one_iff.mp hsmallZ
  apply hWtailNonzero
  rw [hWZ, htZ]
  have hKZ : K = Z := sub_eq_zero.mp hzeroZ
  rw [hKZ, sub_self]

#print axioms dyadic_series_integer_obstruction

end D5.S3.Arith.Primes.DyadicSeriesIntegerObstruction
