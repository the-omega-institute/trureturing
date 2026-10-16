/- GID: D5/S3/Analytic/EulerGerm/LocalFactorUniversalScaling
   generality: I
   mirror-B: D5/B/S3/Analytic/EulerGerm/LocalFactorUniversalScaling
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Scale every golden local factor universally and sharpen its second normalized tail. -/

import D5.S3.Analytic.EulerGerm.GoldenLocalFactor

/- Library-search audit trail (2026-09-03):
   * Exact-name and statement-shape searches on origin/dev found no theorem
     for prime scaling, next-mode expansion, or sharp second-normalized
     summability. The fourth-tail shape occurs in the frozen second-order
     factorization, but its supporting lemmas are private and its public bound
     is the weaker half-plane Re s > 1 / phi^4.
   * Pinned Mathlib supplies Complex.cpow_def_of_ne_zero,
     Complex.natCast_log, Nat.Primes.summable_rpow, and
     Summable.sum_add_tsum_nat_add. These are bound below.
   * No definition is introduced. The only direct D5 import supplies the
     canonical germLocalFactor and o5_beta_zero declarations; its frozen beta
     dependency supplies o5Beta, o5_beta_growth, and o5_beta_power_law. -/

namespace D5.S3.Analytic.EulerGerm.LocalFactorUniversalScaling

set_option autoImplicit false
set_option relaxedAutoImplicit false

open D5.S3.Analytic.GoldenEulerBeta
open D5.S3.Analytic.EulerGerm.GoldenLocalFactor

noncomputable section

/-- Every prime-local golden germ is the same universal series after the
logarithmic rescaling `s -> (log p / log q) * s`. This equality does not assert
that any local factor has a zero. -/
theorem germLocalFactor_prime_scaling (p q : Nat.Primes) (s : ℂ) :
    germLocalFactor s p =
      germLocalFactor ((((Real.log p / Real.log q : ℝ)) : ℂ) * s) q := by
  rw [germLocalFactor, germLocalFactor]
  apply tsum_congr
  intro v
  have hp0 : (p : ℂ) ≠ 0 := by
    exact_mod_cast p.prop.ne_zero
  have hq0 : (q : ℂ) ≠ 0 := by
    exact_mod_cast q.prop.ne_zero
  have hlogq : Real.log (q : Nat) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast q.prop.one_lt)).ne'
  have hlogqC : (Real.log (q : Nat) : ℂ) ≠ 0 := by
    exact_mod_cast hlogq
  have hComplexLogq : Complex.log (q : ℂ) ≠ 0 := by
    rw [← Complex.natCast_log]
    exact hlogqC
  rw [Complex.cpow_def_of_ne_zero hp0,
    Complex.cpow_def_of_ne_zero hq0,
    ← Complex.natCast_log, ← Complex.natCast_log]
  congr 1
  push_cast
  field_simp [hlogqC, hComplexLogq]

private theorem natCast_le_o5Beta (v : Nat) : (v : ℝ) ≤ o5Beta v := by
  cases v with
  | zero => simp [o5_beta_zero]
  | succ v =>
      have hgrowth := o5_beta_growth (v + 1)
      have hsqrt_sq : Real.sqrt 5 ^ 2 = (5 : ℝ) :=
        Real.sq_sqrt (by norm_num)
      have hsqrt_nonneg : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
      have hsqrt_two : 2 < Real.sqrt 5 := by nlinarith
      have hinv_pos : 0 < 1 / Real.goldenRatio :=
        one_div_pos.mpr Real.goldenRatio_pos
      push_cast at hgrowth ⊢
      nlinarith

private theorem local_factor_summable_pos (s : ℂ) (hs : 0 < s.re)
    (p : Nat.Primes) :
    Summable (fun v : Nat =>
      (p : ℂ) ^ (-s * (o5Beta v : ℂ))) := by
  let q : ℝ := (p : ℝ) ^ (-s.re)
  have hp_one : (1 : ℝ) ≤ p := by exact_mod_cast p.prop.one_lt.le
  have hp_pos : (0 : ℝ) < p := by exact_mod_cast p.prop.pos
  have hq_nonneg : 0 ≤ q := Real.rpow_nonneg hp_pos.le _
  have hq_lt_one : q < 1 := by
    exact Real.rpow_lt_one_of_one_lt_of_neg
      (by exact_mod_cast p.prop.one_lt) (neg_neg_of_pos hs)
  have hgeom : Summable (fun v : Nat => q ^ v) :=
    summable_geometric_of_norm_lt_one (by
      rw [Real.norm_eq_abs, abs_of_nonneg hq_nonneg]
      exact hq_lt_one)
  have hnorm : Summable (fun v : Nat =>
      ‖(p : ℂ) ^ (-s * (o5Beta v : ℂ))‖) := by
    apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun v => ?_) hgeom
    rw [Complex.norm_natCast_cpow_of_pos p.prop.pos]
    simp only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, sub_zero]
    have hexponent : -s.re * o5Beta v ≤ -s.re * (v : ℝ) := by
      nlinarith [natCast_le_o5Beta v]
    calc
      (p : ℝ) ^ (-s.re * o5Beta v) ≤
          (p : ℝ) ^ (-s.re * (v : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le hp_one hexponent
      _ = q ^ v := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hp_pos.le]
  exact hnorm.of_norm

private theorem local_factor_eq_second_order_and_tail_pos
    (s : ℂ) (hs : 0 < s.re) (p : Nat.Primes) :
    let x := (p : ℂ) ^
      (-s * ((Real.goldenRatio ^ 2 : ℝ) : ℂ))
    let y := (p : ℂ) ^
      (-s * ((Real.goldenRatio ^ 3 : ℝ) : ℂ))
    let tail := ∑' k : Nat,
      (p : ℂ) ^ (-s * (o5Beta (k + 4) : ℂ))
    germLocalFactor s p = (1 + x) * (1 + y) + tail := by
  dsimp only
  let f : Nat → ℂ := fun v =>
    (p : ℂ) ^ (-s * (o5Beta v : ℂ))
  have hall : Summable f := by
    simpa [f] using local_factor_summable_pos s hs p
  have hphi : Real.goldenRatio ^ 4 =
      Real.goldenRatio ^ 2 + Real.goldenRatio ^ 3 := by
    calc
      Real.goldenRatio ^ 4 =
          Real.goldenRatio ^ 2 * Real.goldenRatio ^ 2 := by ring
      _ = Real.goldenRatio ^ 2 * (Real.goldenRatio + 1) :=
        congrArg (fun z : ℝ => Real.goldenRatio ^ 2 * z)
          Real.goldenRatio_sq
      _ = Real.goldenRatio ^ 2 + Real.goldenRatio ^ 3 := by ring
  have hpow :
      (p : ℂ) ^ (-s * ((Real.goldenRatio ^ 4 : ℝ) : ℂ)) =
        (p : ℂ) ^ (-s * ((Real.goldenRatio ^ 2 : ℝ) : ℂ)) *
          (p : ℂ) ^ (-s * ((Real.goldenRatio ^ 3 : ℝ) : ℂ)) := by
    have hexponent :
        -s * ((Real.goldenRatio ^ 4 : ℝ) : ℂ) =
          -s * ((Real.goldenRatio ^ 2 : ℝ) : ℂ) +
            -s * ((Real.goldenRatio ^ 3 : ℝ) : ℂ) := by
      rw [hphi]
      push_cast
      ring
    rw [hexponent, Complex.cpow_add _ _ (by
      exact_mod_cast p.prop.ne_zero)]
  have hprefix :
      (∑ v ∈ Finset.range 4, f v) =
        (1 + (p : ℂ) ^
          (-s * ((Real.goldenRatio ^ 2 : ℝ) : ℂ))) *
        (1 + (p : ℂ) ^
          (-s * ((Real.goldenRatio ^ 3 : ℝ) : ℂ))) := by
    have hf0 : f 0 = 1 := by simp [f, o5_beta_zero]
    have hf1 : f 1 = (p : ℂ) ^
        (-s * ((Real.goldenRatio ^ 2 : ℝ) : ℂ)) := by
      simp only [f, o5_beta_power_law.1]
    have hf2 : f 2 = (p : ℂ) ^
        (-s * ((Real.goldenRatio ^ 3 : ℝ) : ℂ)) := by
      simp only [f, o5_beta_power_law.2.1]
    have hf3 : f 3 = (p : ℂ) ^
        (-s * ((Real.goldenRatio ^ 4 : ℝ) : ℂ)) := by
      simp only [f, o5_beta_power_law.2.2]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero,
      hf0, hf1, hf2, hf3, zero_add]
    rw [hpow]
    ring
  rw [germLocalFactor, show (fun v : Nat =>
      (p : ℂ) ^ (-s * (o5Beta v : ℂ))) = f from rfl,
    ← hall.sum_add_tsum_nat_add 4, hprefix]

/-- Removing the first two golden modes leaves the square of the third mode
and the exact tail beginning at `o5Beta 4`. -/
theorem germLocalFactor_next_mode_expansion
    (s : ℂ) (p : Nat.Primes) (hs : 0 < s.re) :
    let x := (p : ℂ) ^
      (-s * ((Real.goldenRatio ^ 2 : ℝ) : ℂ))
    let y := (p : ℂ) ^
      (-s * ((Real.goldenRatio ^ 3 : ℝ) : ℂ))
    (1 - y) * (1 + x)⁻¹ * germLocalFactor s p - 1 =
      -y ^ 2 + (1 - y) * (1 + x)⁻¹ *
        ∑' k : Nat, (p : ℂ) ^
          (-s * (o5Beta (k + 4) : ℂ)) := by
  dsimp only
  let x : ℂ := (p : ℂ) ^
    (-s * ((Real.goldenRatio ^ 2 : ℝ) : ℂ))
  let y : ℂ := (p : ℂ) ^
    (-s * ((Real.goldenRatio ^ 3 : ℝ) : ℂ))
  let tail : ℂ := ∑' k : Nat,
    (p : ℂ) ^ (-s * (o5Beta (k + 4) : ℂ))
  change (1 - y) * (1 + x)⁻¹ * germLocalFactor s p - 1 =
    -y ^ 2 + (1 - y) * (1 + x)⁻¹ * tail
  have hxlt : ‖x‖ < 1 := by
    dsimp [x]
    rw [Complex.norm_natCast_cpow_of_pos p.prop.pos]
    rw [show (-s * ((Real.goldenRatio ^ 2 : ℝ) : ℂ)).re =
      -s.re * Real.goldenRatio ^ 2 by norm_num]
    exact Real.rpow_lt_one_of_one_lt_of_neg
      (by exact_mod_cast p.prop.one_lt)
      (mul_neg_of_neg_of_pos (neg_neg_of_pos hs)
        (sq_pos_of_pos Real.goldenRatio_pos))
  have hx : 1 + x ≠ 0 := by
    intro hzero
    have hneg : x = -1 := by linear_combination hzero
    rw [hneg, norm_neg, norm_one] at hxlt
    exact lt_irrefl 1 hxlt
  have hlocal : germLocalFactor s p = (1 + x) * (1 + y) + tail := by
    simpa [x, y, tail] using local_factor_eq_second_order_and_tail_pos s hs p
  rw [hlocal]
  field_simp [hx]
  ring

private theorem goldenRatio_gt_eight_fifths :
    (8 : ℝ) / 5 < Real.goldenRatio := by
  rw [Real.goldenRatio]
  have hsqrt_sq : Real.sqrt 5 ^ 2 = (5 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  have hsqrt_nonneg : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  nlinarith

private theorem goldenRatio_lt_five_thirds :
    Real.goldenRatio < (5 : ℝ) / 3 := by
  rw [Real.goldenRatio]
  have hsqrt_sq : Real.sqrt 5 ^ 2 = (5 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  have hsqrt_nonneg : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  nlinarith

private theorem floor_five_mul_goldenRatio :
    ⌊(5 : ℝ) * Real.goldenRatio⌋ = (8 : Int) := by
  rw [Int.floor_eq_iff]
  constructor <;> norm_num at * <;>
    nlinarith [goldenRatio_gt_eight_fifths,
      goldenRatio_lt_five_thirds]

private theorem o5_beta_four_sharp :
    o5Beta 4 = 2 * Real.goldenRatio ^ 3 + 1 := by
  have hcube : Real.goldenRatio ^ 3 = 2 * Real.goldenRatio + 1 := by
    calc
      Real.goldenRatio ^ 3 =
          Real.goldenRatio * Real.goldenRatio ^ 2 := by ring
      _ = Real.goldenRatio * (Real.goldenRatio + 1) := by
        rw [Real.goldenRatio_sq]
      _ = 2 * Real.goldenRatio + 1 := by
        nlinarith [Real.goldenRatio_sq]
  rw [o5Beta]
  norm_num
  rw [floor_five_mul_goldenRatio, hcube]
  norm_num
  ring

private theorem o5_beta_four_add_ge (k : Nat) :
    2 * Real.goldenRatio ^ 3 + 1 + (k : ℝ) ≤ o5Beta (k + 4) := by
  cases k with
  | zero => simpa using o5_beta_four_sharp.symm.le
  | succ k =>
      have hsqrt_sq : Real.sqrt 5 ^ 2 = (5 : ℝ) :=
        Real.sq_sqrt (by norm_num)
      have hsqrt_nonneg : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
      have hsqrt_two : 2 < Real.sqrt 5 := by nlinarith
      have hphi_inv : 1 / Real.goldenRatio = Real.goldenRatio - 1 := by
        rw [one_div, Real.inv_goldenRatio]
        linarith [Real.goldenRatio_add_goldenConj]
      have hcube : Real.goldenRatio ^ 3 = 2 * Real.goldenRatio + 1 := by
        calc
          Real.goldenRatio ^ 3 =
              Real.goldenRatio * Real.goldenRatio ^ 2 := by ring
          _ = Real.goldenRatio * (Real.goldenRatio + 1) := by
            rw [Real.goldenRatio_sq]
          _ = 2 * Real.goldenRatio + 1 := by
            nlinarith [Real.goldenRatio_sq]
      apply le_trans _ (o5_beta_growth (k + 5))
      rw [hphi_inv, hcube]
      push_cast
      have hk : 0 ≤ (k : ℝ) := by positivity
      rw [Real.goldenRatio]
      ring_nf
      nlinarith

private theorem sharp_fourth_tail_real_summable (sigma : ℝ)
    (hsigma : 1 / (2 * Real.goldenRatio ^ 3) < sigma) :
    Summable (fun q : Nat.Primes × Nat =>
      (q.1 : ℝ) ^ (-sigma * o5Beta (q.2 + 4))) := by
  let beta4 : ℝ := 2 * Real.goldenRatio ^ 3 + 1
  have hcritical : 1 < sigma * (2 * Real.goldenRatio ^ 3) :=
    (div_lt_iff₀ (by positivity : 0 < 2 * Real.goldenRatio ^ 3)).mp
      (by simpa [div_eq_mul_inv] using hsigma)
  have hsigma_pos : 0 < sigma := lt_trans (by positivity) hsigma
  let r : ℝ := -sigma * beta4
  let q : ℝ := (2 : ℝ) ^ (-sigma)
  have hr : r < -1 := by dsimp [r, beta4]; nlinarith
  have hq_nonneg : 0 ≤ q := by dsimp [q]; positivity
  have hq_lt_one : q < 1 := by
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num)
      (neg_neg_of_pos hsigma_pos)
  have hbase : Summable (fun p : Nat.Primes => (p : ℝ) ^ r) :=
    Nat.Primes.summable_rpow.mpr hr
  have hslice (k : Nat) :
      Summable (fun p : Nat.Primes =>
        (p : ℝ) ^ (-sigma * o5Beta (k + 4))) := by
    apply Nat.Primes.summable_rpow.mpr
    have hbeta := o5_beta_four_add_ge k
    nlinarith
  have hterm (k : Nat) (p : Nat.Primes) :
      (p : ℝ) ^ (-sigma * o5Beta (k + 4)) ≤
        (p : ℝ) ^ r * q ^ k := by
    have hp_one : 1 ≤ (p : ℝ) := by exact_mod_cast p.prop.one_lt.le
    have hp_two : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast p.prop.two_le
    have hbeta := o5_beta_four_add_ge k
    have hk : 0 ≤ (k : ℝ) := by positivity
    calc
      (p : ℝ) ^ (-sigma * o5Beta (k + 4)) ≤
          (p : ℝ) ^ (-sigma * (beta4 + (k : ℝ))) :=
        Real.rpow_le_rpow_of_exponent_le hp_one (by
          dsimp [beta4]
          nlinarith)
      _ = (p : ℝ) ^ r *
          (p : ℝ) ^ (-sigma * (k : ℝ)) := by
        rw [← Real.rpow_add (by exact_mod_cast p.prop.pos)]
        dsimp [r]
        congr 1
        ring
      _ ≤ (p : ℝ) ^ r *
          (2 : ℝ) ^ (-sigma * (k : ℝ)) := by
        exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_nonpos (z := -sigma * (k : ℝ))
            (by norm_num) hp_two
            (mul_nonpos_of_nonpos_of_nonneg (by linarith) hk))
          (by positivity)
      _ = (p : ℝ) ^ r * q ^ k := by
        dsimp [q]
        rw [← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2)]
  have htsum (k : Nat) :
      (∑' p : Nat.Primes,
          (p : ℝ) ^ (-sigma * o5Beta (k + 4))) ≤
        (∑' p : Nat.Primes, (p : ℝ) ^ r) * q ^ k := by
    calc
      (∑' p : Nat.Primes,
          (p : ℝ) ^ (-sigma * o5Beta (k + 4))) ≤
          ∑' p : Nat.Primes, (p : ℝ) ^ r * q ^ k :=
        (hslice k).tsum_le_tsum (hterm k) (hbase.mul_right (q ^ k))
      _ = (∑' p : Nat.Primes, (p : ℝ) ^ r) * q ^ k :=
        tsum_mul_right
  have houter : Summable (fun k : Nat =>
      ∑' p : Nat.Primes,
        (p : ℝ) ^ (-sigma * o5Beta (k + 4))) :=
    ((summable_geometric_of_lt_one hq_nonneg hq_lt_one).mul_left
      (∑' p : Nat.Primes, (p : ℝ) ^ r)).of_nonneg_of_le
        (fun _ => by positivity) htsum
  have hswapped : Summable (fun kp : Nat × Nat.Primes =>
      (kp.2 : ℝ) ^ (-sigma * o5Beta (kp.1 + 4))) :=
    (summable_prod_of_nonneg (fun _ => by positivity)).mpr
      ⟨hslice, houter⟩
  exact (Equiv.prodComm Nat.Primes Nat).summable_iff.mpr hswapped

private theorem sharp_fourth_tail_norm_summable (s : ℂ)
    (hs : 1 / (2 * Real.goldenRatio ^ 3) < s.re) :
    Summable (fun q : Nat.Primes × Nat =>
      ‖(q.1 : ℂ) ^
        (-s * (o5Beta (q.2 + 4) : ℂ))‖) := by
  refine (sharp_fourth_tail_real_summable s.re hs).congr fun q => ?_
  rw [Complex.norm_natCast_cpow_of_pos q.1.prop.pos]
  simp only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero]

private theorem mode_norm_le_one_pos (s : ℂ) (hs : 0 < s.re)
    (c : ℝ) (hc : 0 < c) (p : Nat.Primes) :
    ‖(p : ℂ) ^ (-s * (c : ℂ))‖ ≤ 1 := by
  rw [Complex.norm_natCast_cpow_of_pos p.prop.pos]
  rw [show (-s * (c : ℂ)).re = -s.re * c by norm_num]
  exact Real.rpow_le_one_of_one_le_of_nonpos
    (by exact_mod_cast p.prop.one_le) (by nlinarith)

private theorem first_mode_norm_le_two_pos (s : ℂ) (hs : 0 < s.re)
    (p : Nat.Primes) :
    ‖(p : ℂ) ^
        (-s * ((Real.goldenRatio ^ 2 : ℝ) : ℂ))‖ ≤
      (2 : ℝ) ^ (-s.re * Real.goldenRatio ^ 2) := by
  rw [Complex.norm_natCast_cpow_of_pos p.prop.pos]
  rw [show (-s * ((Real.goldenRatio ^ 2 : ℝ) : ℂ)).re =
      -s.re * Real.goldenRatio ^ 2 by norm_num]
  exact Real.rpow_le_rpow_of_nonpos (by norm_num)
    (by exact_mod_cast p.prop.two_le)
    (mul_nonpos_of_nonpos_of_nonneg (by linarith)
      (sq_nonneg Real.goldenRatio))

private theorem inverse_one_add_first_mode_norm_le_pos
    (s : ℂ) (hs : 0 < s.re) (p : Nat.Primes) :
    let q : ℝ := (2 : ℝ) ^ (-s.re * Real.goldenRatio ^ 2)
    ‖(1 + (p : ℂ) ^
        (-s * ((Real.goldenRatio ^ 2 : ℝ) : ℂ)))⁻¹‖ ≤
      1 / (1 - q) := by
  dsimp only
  let x : ℂ := (p : ℂ) ^
    (-s * ((Real.goldenRatio ^ 2 : ℝ) : ℂ))
  let q : ℝ := (2 : ℝ) ^ (-s.re * Real.goldenRatio ^ 2)
  have hq_lt : q < 1 := by
    dsimp [q]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num)
      (mul_neg_of_neg_of_pos (neg_neg_of_pos hs)
        (sq_pos_of_pos Real.goldenRatio_pos))
  have hxq : ‖x‖ ≤ q := by
    simpa [x, q] using first_mode_norm_le_two_pos s hs p
  have hlower : 1 - q ≤ ‖1 + x‖ := by
    calc
      1 - q ≤ 1 - ‖x‖ := sub_le_sub_left hxq 1
      _ = ‖(1 : ℂ)‖ - ‖-x‖ := by simp
      _ ≤ ‖(1 : ℂ) - (-x)‖ := norm_sub_norm_le _ _
      _ = ‖1 + x‖ := by simp only [sub_neg_eq_add]
  have hpositive : 0 < 1 - q := sub_pos.mpr hq_lt
  rw [norm_inv]
  simpa [x, q, one_div] using
    one_div_le_one_div_of_le hpositive hlower

private theorem third_mode_square_norm_summable_sharp
    (s : ℂ) (hs : 1 / (2 * Real.goldenRatio ^ 3) < s.re) :
    Summable (fun p : Nat.Primes =>
      ‖((p : ℂ) ^
        (-s * ((Real.goldenRatio ^ 3 : ℝ) : ℂ))) ^ 2‖) := by
  have hcritical : 1 < s.re * (2 * Real.goldenRatio ^ 3) :=
    (div_lt_iff₀ (by positivity : 0 < 2 * Real.goldenRatio ^ 3)).mp
      (by simpa [div_eq_mul_inv] using hs)
  have hexponent : -s.re * Real.goldenRatio ^ 3 * 2 < -1 := by
    nlinarith
  refine (Nat.Primes.summable_rpow.mpr hexponent).congr fun p => ?_
  rw [norm_pow, Complex.norm_natCast_cpow_of_pos p.prop.pos]
  rw [show (-s * ((Real.goldenRatio ^ 3 : ℝ) : ℂ)).re =
      -s.re * Real.goldenRatio ^ 3 by
        simp only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re,
          Complex.ofReal_im, mul_zero, sub_zero]]
  exact Real.rpow_mul_natCast
    (by exact_mod_cast p.prop.pos : (0 : ℝ) < p).le
    (-s.re * Real.goldenRatio ^ 3) 2

/-- The second normalized local-factor deviation is absolutely summable on
`Re s > 1 / (2 * phi^3)`. This sharpens the frozen `1 / phi^4` sufficient
bound to the lower edge `1 / (2 * phi^3)` of the golden window. It asserts no
zero of any local factor. -/
theorem second_normalized_factor_deviation_norm_summable_sharp
    (s : ℂ) (hs : 1 / (2 * Real.goldenRatio ^ 3) < s.re) :
    Summable (fun p : Nat.Primes =>
      ‖(1 - (p : ℂ) ^
          (-s * ((Real.goldenRatio ^ 3 : ℝ) : ℂ))) *
          (1 + (p : ℂ) ^
            (-s * ((Real.goldenRatio ^ 2 : ℝ) : ℂ)))⁻¹ *
          germLocalFactor s p - 1‖) := by
  let x : Nat.Primes → ℂ := fun p => (p : ℂ) ^
    (-s * ((Real.goldenRatio ^ 2 : ℝ) : ℂ))
  let y : Nat.Primes → ℂ := fun p => (p : ℂ) ^
    (-s * ((Real.goldenRatio ^ 3 : ℝ) : ℂ))
  let tail : Nat.Primes → ℂ := fun p => ∑' k : Nat,
    (p : ℂ) ^ (-s * (o5Beta (k + 4) : ℂ))
  let q : ℝ := (2 : ℝ) ^ (-s.re * Real.goldenRatio ^ 2)
  let C : ℝ := 1 / (1 - q)
  have hspos : 0 < s.re := lt_trans (by positivity) hs
  have hq_lt : q < 1 := by
    dsimp [q]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num)
      (mul_neg_of_neg_of_pos (neg_neg_of_pos hspos)
        (sq_pos_of_pos Real.goldenRatio_pos))
  have hCnonneg : 0 ≤ C := by dsimp [C]; positivity
  have hnorm := sharp_fourth_tail_norm_summable s hs
  have htailNorm : Summable (fun p : Nat.Primes => ‖tail p‖) := by
    refine hnorm.prod.of_nonneg_of_le (fun _ => norm_nonneg _) fun p => ?_
    exact norm_tsum_le_tsum_norm (hnorm.prod_factor p)
  have hySquareNorm : Summable (fun p : Nat.Primes => ‖y p ^ 2‖) := by
    simpa [y] using third_mode_square_norm_summable_sharp s hs
  have hmajor : Summable (fun p : Nat.Primes =>
      ‖y p ^ 2‖ + (2 * C) * ‖tail p‖) :=
    hySquareNorm.add (htailNorm.mul_left (2 * C))
  refine hmajor.of_norm_bounded fun p => ?_
  have hy : ‖y p‖ ≤ 1 := by
    change ‖(p : ℂ) ^
      (-s * ((Real.goldenRatio ^ 3 : ℝ) : ℂ))‖ ≤ 1
    exact mode_norm_le_one_pos s hspos (Real.goldenRatio ^ 3)
      (by positivity) p
  have hinv : ‖(1 + x p)⁻¹‖ ≤ C := by
    change ‖(1 + (p : ℂ) ^
      (-s * ((Real.goldenRatio ^ 2 : ℝ) : ℂ)))⁻¹‖ ≤
        1 / (1 - (2 : ℝ) ^ (-s.re * Real.goldenRatio ^ 2))
    exact inverse_one_add_first_mode_norm_le_pos s hspos p
  have hdeviation :
      (1 - y p) * (1 + x p)⁻¹ * germLocalFactor s p - 1 =
        -(y p ^ 2) + (1 - y p) * (1 + x p)⁻¹ * tail p := by
    simpa [x, y, tail] using
      germLocalFactor_next_mode_expansion s p hspos
  rw [hdeviation]
  rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  calc
    ‖-(y p ^ 2) + (1 - y p) * (1 + x p)⁻¹ * tail p‖ ≤
        ‖y p ^ 2‖ + ‖(1 - y p) * (1 + x p)⁻¹ * tail p‖ := by
      simpa only [norm_neg] using norm_add_le (-(y p ^ 2))
        ((1 - y p) * (1 + x p)⁻¹ * tail p)
    _ ≤ ‖y p ^ 2‖ + (2 * C) * ‖tail p‖ := by
      gcongr
      rw [norm_mul, norm_mul]
      have hone : ‖1 - y p‖ ≤ 2 := by
        calc
          ‖1 - y p‖ ≤ ‖(1 : ℂ)‖ + ‖y p‖ := norm_sub_le _ _
          _ ≤ 2 := by norm_num; linarith
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      exact mul_le_mul hone hinv (norm_nonneg _) (by norm_num)

private example : Nat.Primes := ⟨2, by norm_num⟩

private example : 0 < (1 : ℂ).re := by norm_num

private example :
    1 / (2 * Real.goldenRatio ^ 3) <
      (Complex.ofReal (1 / (2 * Real.goldenRatio ^ 3) + 1)).re := by
  simp only [Complex.ofReal_re]
  linarith

#print axioms germLocalFactor_prime_scaling
#print axioms germLocalFactor_next_mode_expansion
#print axioms second_normalized_factor_deviation_norm_summable_sharp

end

end D5.S3.Analytic.EulerGerm.LocalFactorUniversalScaling
