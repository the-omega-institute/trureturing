/- GID: D5/S3/Analytic/EulerGerm/GoldenGermSecondOrderFactorization
   generality: I
   mirror-B: D5/B/S3/Analytic/EulerGerm/GoldenGermSecondOrderFactorization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Extract the signed second-order zeta factors of the golden Euler germ. -/

import D5.S3.Analytic.EulerGerm.GoldenGermZetaFactorization
import Mathlib.Topology.Algebra.InfiniteSum.Group

/- Library-search audit trail (2026-08-28):
   * Current-tree name and body-shape searches found the canonical `o5Beta`
     and `germLocalFactor`, the first zeta extraction, and a generic
     caller-supplied second-order product theorem, but no canonical signed
     second-order extraction for this germ.
   * Pinned Mathlib supplies `riemannZeta_eulerProduct_hasProd`, prime rpow
     summability, and infinite-product assembly; it has no theorem for the
     golden exponent family or its `1 / phi^4` normalized tail.
   * No new definition is introduced: the theorem constructs its unique
     continuation directly from the frozen canonical germ primitives. -/

namespace D5.S3.Analytic.EulerGerm.GoldenGermSecondOrderFactorization

set_option autoImplicit false
set_option relaxedAutoImplicit false

open D5.S3.Analytic.GoldenEulerBeta
open D5.S3.Analytic.EulerGerm.GoldenLocalFactor
open D5.S3.Analytic.EulerGerm.GermProductConvergence

noncomputable section

private theorem prime_real_pos (p : Nat.Primes) : 0 < (p : Real) := by
  exact_mod_cast p.prop.pos

private theorem o5_beta_three_add_ge (k : Nat) :
    Real.goldenRatio ^ 4 + (k : Real) <= o5Beta (k + 3) := by
  cases k with
  | zero => simpa using o5_beta_power_law.2.2.symm.le
  | succ k =>
      have hsqrt_sq : Real.sqrt 5 ^ 2 = (5 : Real) :=
        Real.sq_sqrt (by norm_num)
      have hsqrt_nonneg : 0 <= Real.sqrt 5 := Real.sqrt_nonneg 5
      have hsqrt_two : 2 < Real.sqrt 5 := by nlinarith
      have hphi_inv : 1 / Real.goldenRatio = Real.goldenRatio - 1 := by
        rw [one_div, Real.inv_goldenRatio]
        linarith [Real.goldenRatio_add_goldenConj]
      have hfourth : Real.goldenRatio ^ 4 = 3 * Real.goldenRatio + 2 := by
        calc
          Real.goldenRatio ^ 4 = (Real.goldenRatio ^ 2) ^ 2 := by ring
          _ = (Real.goldenRatio + 1) ^ 2 := by rw [Real.goldenRatio_sq]
          _ = 3 * Real.goldenRatio + 2 := by
            nlinarith [Real.goldenRatio_sq]
      apply le_trans _ (o5_beta_growth (k + 4))
      rw [hphi_inv, hfourth]
      push_cast
      have hk : 0 <= (k : Real) := by positivity
      rw [Real.goldenRatio]
      ring_nf
      nlinarith

private theorem fourth_tail_real_summable (sigma : Real)
    (hsigma : 1 / Real.goldenRatio ^ 4 < sigma) :
    Summable (fun q : Nat.Primes × Nat =>
      (q.1 : Real) ^ (-sigma * o5Beta (q.2 + 4))) := by
  have hphi : 0 < Real.goldenRatio ^ 4 := by positivity
  have hcritical : 1 < sigma * Real.goldenRatio ^ 4 :=
    (div_lt_iff₀ hphi).mp (by simpa [div_eq_mul_inv] using hsigma)
  have hsigma_pos : 0 < sigma := lt_trans (by positivity) hsigma
  let r : Real := -sigma * Real.goldenRatio ^ 4
  let q : Real := (2 : Real) ^ (-sigma)
  have hr : r < -1 := by dsimp [r]; linarith
  have hq_nonneg : 0 <= q := by dsimp [q]; positivity
  have hq_lt_one : q < 1 := by
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_neg_of_pos hsigma_pos)
  have hbase : Summable (fun p : Nat.Primes => (p : Real) ^ r) :=
    Nat.Primes.summable_rpow.mpr hr
  have hslice (k : Nat) :
      Summable (fun p : Nat.Primes =>
        (p : Real) ^ (-sigma * o5Beta (k + 4))) := by
    apply Nat.Primes.summable_rpow.mpr
    have hbeta := o5_beta_three_add_ge (k + 1)
    push_cast at hbeta
    nlinarith
  have hterm (k : Nat) (p : Nat.Primes) :
      (p : Real) ^ (-sigma * o5Beta (k + 4)) <=
        (p : Real) ^ r * q ^ k := by
    have hp_one : 1 <= (p : Real) := by exact_mod_cast p.prop.one_lt.le
    have hp_two : (2 : Real) <= (p : Real) := by exact_mod_cast p.prop.two_le
    have hbeta := o5_beta_three_add_ge (k + 1)
    push_cast at hbeta
    have hk : 0 <= (k : Real) := by positivity
    calc
      (p : Real) ^ (-sigma * o5Beta (k + 4)) <=
          (p : Real) ^ (-sigma * (Real.goldenRatio ^ 4 + (k : Real))) :=
        Real.rpow_le_rpow_of_exponent_le hp_one (by nlinarith)
      _ = (p : Real) ^ r * (p : Real) ^ (-sigma * (k : Real)) := by
        rw [← Real.rpow_add (prime_real_pos p)]
        dsimp [r]
        congr 1
        ring
      _ <= (p : Real) ^ r * (2 : Real) ^ (-sigma * (k : Real)) := by
        exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_nonpos (z := -sigma * (k : Real))
            (by norm_num) hp_two
            (mul_nonpos_of_nonpos_of_nonneg (by linarith) hk)) (by positivity)
      _ = (p : Real) ^ r * q ^ k := by
        dsimp [q]
        rw [← Real.rpow_mul_natCast (by norm_num : (0 : Real) <= 2)]
  have htsum (k : Nat) :
      (∑' p : Nat.Primes, (p : Real) ^ (-sigma * o5Beta (k + 4))) <=
        (∑' p : Nat.Primes, (p : Real) ^ r) * q ^ k := by
    calc
      (∑' p : Nat.Primes, (p : Real) ^ (-sigma * o5Beta (k + 4))) <=
          ∑' p : Nat.Primes, (p : Real) ^ r * q ^ k :=
        (hslice k).tsum_le_tsum (hterm k) (hbase.mul_right (q ^ k))
      _ = (∑' p : Nat.Primes, (p : Real) ^ r) * q ^ k := tsum_mul_right
  have houter : Summable (fun k : Nat =>
      ∑' p : Nat.Primes, (p : Real) ^ (-sigma * o5Beta (k + 4))) :=
    ((summable_geometric_of_lt_one hq_nonneg hq_lt_one).mul_left
      (∑' p : Nat.Primes, (p : Real) ^ r)).of_nonneg_of_le
        (fun _ => by positivity) htsum
  have hswapped : Summable (fun kp : Nat × Nat.Primes =>
      (kp.2 : Real) ^ (-sigma * o5Beta (kp.1 + 4))) :=
    (summable_prod_of_nonneg (fun _ => by positivity)).mpr ⟨hslice, houter⟩
  exact (Equiv.prodComm Nat.Primes Nat).summable_iff.mpr hswapped

private theorem fourth_tail_norm_summable (s : Complex)
    (hs : 1 / Real.goldenRatio ^ 4 < s.re) :
    Summable (fun q : Nat.Primes × Nat =>
      ‖(q.1 : Complex) ^ (-s * (o5Beta (q.2 + 4) : Complex))‖) := by
  refine (fourth_tail_real_summable s.re hs).congr fun q => ?_
  rw [Complex.norm_natCast_cpow_of_pos q.1.prop.pos]
  simp only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero]

private theorem local_factor_eq_second_order_and_tail (s : Complex)
    (hs : 1 / Real.goldenRatio ^ 4 < s.re) (p : Nat.Primes) :
    let x := (p : Complex) ^
      (-s * ((Real.goldenRatio ^ 2 : Real) : Complex))
    let y := (p : Complex) ^
      (-s * ((Real.goldenRatio ^ 3 : Real) : Complex))
    let tail := ∑' k : Nat,
      (p : Complex) ^ (-s * (o5Beta (k + 4) : Complex))
    germLocalFactor s p = (1 + x) * (1 + y) + tail := by
  dsimp only
  let f : Nat -> Complex := fun v =>
    (p : Complex) ^ (-s * (o5Beta v : Complex))
  have htail : Summable (fun k : Nat => f (k + 4)) := by
    exact ((fourth_tail_norm_summable s hs).prod_factor p).of_norm
  have hall : Summable f := (summable_nat_add_iff 4).1 (by
    simpa [f, Nat.add_comm] using htail)
  have hphi : Real.goldenRatio ^ 4 =
      Real.goldenRatio ^ 2 + Real.goldenRatio ^ 3 := by
    calc
      Real.goldenRatio ^ 4 =
          Real.goldenRatio ^ 2 * Real.goldenRatio ^ 2 := by ring
      _ = Real.goldenRatio ^ 2 * (Real.goldenRatio + 1) :=
        congrArg (fun x : Real => Real.goldenRatio ^ 2 * x)
          Real.goldenRatio_sq
      _ = Real.goldenRatio ^ 2 + Real.goldenRatio ^ 3 := by ring
  have hpow :
      (p : Complex) ^ (-s * ((Real.goldenRatio ^ 4 : Real) : Complex)) =
        (p : Complex) ^ (-s * ((Real.goldenRatio ^ 2 : Real) : Complex)) *
          (p : Complex) ^ (-s * ((Real.goldenRatio ^ 3 : Real) : Complex)) := by
    have hexponent :
        -s * ((Real.goldenRatio ^ 4 : Real) : Complex) =
          -s * ((Real.goldenRatio ^ 2 : Real) : Complex) +
            -s * ((Real.goldenRatio ^ 3 : Real) : Complex) := by
      rw [hphi]
      push_cast
      ring
    rw [hexponent, Complex.cpow_add _ _ (by
      exact_mod_cast p.prop.ne_zero)]
  have hprefix :
      (∑ v ∈ Finset.range 4, f v) =
        (1 + (p : Complex) ^
          (-s * ((Real.goldenRatio ^ 2 : Real) : Complex))) *
        (1 + (p : Complex) ^
          (-s * ((Real.goldenRatio ^ 3 : Real) : Complex))) := by
    have hf0 : f 0 = 1 := by simp [f, o5_beta_zero]
    have hf1 : f 1 = (p : Complex) ^
        (-s * ((Real.goldenRatio ^ 2 : Real) : Complex)) := by
      simp only [f, o5_beta_power_law.1]
    have hf2 : f 2 = (p : Complex) ^
        (-s * ((Real.goldenRatio ^ 3 : Real) : Complex)) := by
      simp only [f, o5_beta_power_law.2.1]
    have hf3 : f 3 = (p : Complex) ^
        (-s * ((Real.goldenRatio ^ 4 : Real) : Complex)) := by
      simp only [f, o5_beta_power_law.2.2]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero,
      hf0, hf1, hf2, hf3, zero_add]
    rw [hpow]
    ring
  rw [germLocalFactor, show (fun v : Nat =>
      (p : Complex) ^ (-s * (o5Beta v : Complex))) = f from rfl,
    ← hall.sum_add_tsum_nat_add 4, hprefix]

private theorem mode_norm_le_one (s : Complex)
    (hs : 1 / Real.goldenRatio ^ 4 < s.re) (c : Real) (hc : 0 < c)
    (p : Nat.Primes) :
    ‖(p : Complex) ^ (-s * (c : Complex))‖ <= 1 := by
  have hspos : 0 < s.re := lt_trans (by positivity) hs
  rw [Complex.norm_natCast_cpow_of_pos p.prop.pos]
  rw [show (-s * (c : Complex)).re = -s.re * c by norm_num]
  exact Real.rpow_le_one_of_one_le_of_nonpos
    (by exact_mod_cast p.prop.one_le) (by nlinarith)

private theorem first_mode_norm_lt_one (s : Complex)
    (hs : 1 / Real.goldenRatio ^ 4 < s.re) (p : Nat.Primes) :
    ‖(p : Complex) ^
        (-s * ((Real.goldenRatio ^ 2 : Real) : Complex))‖ < 1 := by
  have hspos : 0 < s.re := lt_trans (by positivity) hs
  rw [Complex.norm_natCast_cpow_of_pos p.prop.pos]
  rw [show (-s * ((Real.goldenRatio ^ 2 : Real) : Complex)).re =
      -s.re * Real.goldenRatio ^ 2 by norm_num]
  exact Real.rpow_lt_one_of_one_lt_of_neg
    (by exact_mod_cast p.prop.one_lt)
    (mul_neg_of_neg_of_pos (neg_neg_of_pos hspos)
      (sq_pos_of_pos Real.goldenRatio_pos))

private theorem first_mode_norm_le_two (s : Complex)
    (hs : 1 / Real.goldenRatio ^ 4 < s.re) (p : Nat.Primes) :
    ‖(p : Complex) ^
        (-s * ((Real.goldenRatio ^ 2 : Real) : Complex))‖ <=
      (2 : Real) ^ (-s.re * Real.goldenRatio ^ 2) := by
  have hspos : 0 < s.re := lt_trans (by positivity) hs
  rw [Complex.norm_natCast_cpow_of_pos p.prop.pos]
  rw [show (-s * ((Real.goldenRatio ^ 2 : Real) : Complex)).re =
      -s.re * Real.goldenRatio ^ 2 by norm_num]
  exact Real.rpow_le_rpow_of_nonpos (by norm_num)
    (by exact_mod_cast p.prop.two_le)
    (mul_nonpos_of_nonpos_of_nonneg (by linarith)
      (sq_nonneg Real.goldenRatio))

private theorem inverse_one_add_first_mode_norm_le (s : Complex)
    (hs : 1 / Real.goldenRatio ^ 4 < s.re) (p : Nat.Primes) :
    let q : Real := (2 : Real) ^ (-s.re * Real.goldenRatio ^ 2)
    ‖(1 + (p : Complex) ^
        (-s * ((Real.goldenRatio ^ 2 : Real) : Complex)))⁻¹‖ <=
      1 / (1 - q) := by
  dsimp only
  let x : Complex := (p : Complex) ^
    (-s * ((Real.goldenRatio ^ 2 : Real) : Complex))
  let q : Real := (2 : Real) ^ (-s.re * Real.goldenRatio ^ 2)
  have hspos : 0 < s.re := lt_trans (by positivity) hs
  have hq_lt : q < 1 := by
    dsimp [q]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num)
      (mul_neg_of_neg_of_pos (neg_neg_of_pos hspos)
        (sq_pos_of_pos Real.goldenRatio_pos))
  have hxq : ‖x‖ <= q := by
    simpa [x, q] using first_mode_norm_le_two s hs p
  have hlower : 1 - q <= ‖1 + x‖ := by
    calc
      1 - q <= 1 - ‖x‖ := sub_le_sub_left hxq 1
      _ = ‖(1 : Complex)‖ - ‖-x‖ := by simp
      _ <= ‖(1 : Complex) - (-x)‖ := norm_sub_norm_le _ _
      _ = ‖1 + x‖ := by simp only [sub_neg_eq_add]
  have hpositive : 0 < 1 - q := sub_pos.mpr hq_lt
  rw [norm_inv]
  simpa [x, q, one_div] using one_div_le_one_div_of_le hpositive hlower

private theorem third_mode_square_norm_summable (s : Complex)
    (hs : 1 / Real.goldenRatio ^ 4 < s.re) :
    Summable (fun p : Nat.Primes =>
      ‖((p : Complex) ^
        (-s * ((Real.goldenRatio ^ 3 : Real) : Complex))) ^ 2‖) := by
  have hspos : 0 < s.re := lt_trans (by positivity) hs
  have hphi4_lt : Real.goldenRatio ^ 4 < 2 * Real.goldenRatio ^ 3 := by
    have hphi3 : 0 < Real.goldenRatio ^ 3 := by positivity
    calc
      Real.goldenRatio ^ 4 = Real.goldenRatio ^ 3 * Real.goldenRatio := by ring
      _ < Real.goldenRatio ^ 3 * 2 :=
        mul_lt_mul_of_pos_left Real.goldenRatio_lt_two hphi3
      _ = 2 * Real.goldenRatio ^ 3 := by ring
  have hexponent : -s.re * Real.goldenRatio ^ 3 * 2 < -1 := by
    have hcritical : 1 < s.re * Real.goldenRatio ^ 4 :=
      (div_lt_iff₀ (by positivity : 0 < Real.goldenRatio ^ 4)).mp
        (by simpa [div_eq_mul_inv] using hs)
    have hscaled := mul_lt_mul_of_pos_left hphi4_lt hspos
    nlinarith
  refine (Nat.Primes.summable_rpow.mpr hexponent).congr fun p => ?_
  rw [norm_pow, Complex.norm_natCast_cpow_of_pos p.prop.pos]
  rw [show (-s * ((Real.goldenRatio ^ 3 : Real) : Complex)).re =
      -s.re * Real.goldenRatio ^ 3 by
        simp only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re,
          Complex.ofReal_im, mul_zero, sub_zero]]
  exact Real.rpow_mul_natCast (prime_real_pos p).le
    (-s.re * Real.goldenRatio ^ 3) 2

private theorem second_normalized_factor_deviation_norm_summable (s : Complex)
    (hs : 1 / Real.goldenRatio ^ 4 < s.re) :
    Summable (fun p : Nat.Primes =>
      ‖(1 - (p : Complex) ^
          (-s * ((Real.goldenRatio ^ 3 : Real) : Complex))) *
          (1 + (p : Complex) ^
            (-s * ((Real.goldenRatio ^ 2 : Real) : Complex)))⁻¹ *
          germLocalFactor s p - 1‖) := by
  let x : Nat.Primes -> Complex := fun p => (p : Complex) ^
    (-s * ((Real.goldenRatio ^ 2 : Real) : Complex))
  let y : Nat.Primes -> Complex := fun p => (p : Complex) ^
    (-s * ((Real.goldenRatio ^ 3 : Real) : Complex))
  let tail : Nat.Primes -> Complex := fun p => ∑' k : Nat,
    (p : Complex) ^ (-s * (o5Beta (k + 4) : Complex))
  let q : Real := (2 : Real) ^ (-s.re * Real.goldenRatio ^ 2)
  let C : Real := 1 / (1 - q)
  have hspos : 0 < s.re := lt_trans (by positivity) hs
  have hq_lt : q < 1 := by
    dsimp [q]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num)
      (mul_neg_of_neg_of_pos (neg_neg_of_pos hspos)
        (sq_pos_of_pos Real.goldenRatio_pos))
  have hCnonneg : 0 <= C := by dsimp [C]; positivity
  have hnorm := fourth_tail_norm_summable s hs
  have htailNorm : Summable (fun p : Nat.Primes => ‖tail p‖) := by
    refine hnorm.prod.of_nonneg_of_le (fun _ => norm_nonneg _) fun p => ?_
    exact norm_tsum_le_tsum_norm (hnorm.prod_factor p)
  have hySquareNorm : Summable (fun p : Nat.Primes => ‖y p ^ 2‖) := by
    simpa [y] using third_mode_square_norm_summable s hs
  have hmajor : Summable (fun p : Nat.Primes =>
      ‖y p ^ 2‖ + (2 * C) * ‖tail p‖) :=
    hySquareNorm.add (htailNorm.mul_left (2 * C))
  refine hmajor.of_norm_bounded fun p => ?_
  have hy : ‖y p‖ <= 1 := by
    change ‖(p : Complex) ^
      (-s * ((Real.goldenRatio ^ 3 : Real) : Complex))‖ <= 1
    exact mode_norm_le_one s hs (Real.goldenRatio ^ 3) (by positivity) p
  have hinv : ‖(1 + x p)⁻¹‖ <= C := by
    change ‖(1 + (p : Complex) ^
      (-s * ((Real.goldenRatio ^ 2 : Real) : Complex)))⁻¹‖ <=
        1 / (1 - (2 : Real) ^ (-s.re * Real.goldenRatio ^ 2))
    exact inverse_one_add_first_mode_norm_le s hs p
  have hne : 1 + x p ≠ 0 := by
    intro heq
    have hxlt : ‖x p‖ < 1 := by
      change ‖(p : Complex) ^
        (-s * ((Real.goldenRatio ^ 2 : Real) : Complex))‖ < 1
      exact first_mode_norm_lt_one s hs p
    have hxneg : x p = -1 := by linear_combination heq
    rw [hxneg, norm_neg, norm_one] at hxlt
    exact lt_irrefl 1 hxlt
  have hlocal : germLocalFactor s p =
      (1 + x p) * (1 + y p) + tail p := by
    simpa [x, y, tail] using local_factor_eq_second_order_and_tail s hs p
  have hdeviation :
      (1 - y p) * (1 + x p)⁻¹ * germLocalFactor s p - 1 =
        -(y p ^ 2) + (1 - y p) * (1 + x p)⁻¹ * tail p := by
    rw [hlocal]
    field_simp [hne]
    ring
  rw [hdeviation]
  rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  calc
    ‖-(y p ^ 2) + (1 - y p) * (1 + x p)⁻¹ * tail p‖ <=
        ‖y p ^ 2‖ + ‖(1 - y p) * (1 + x p)⁻¹ * tail p‖ := by
      simpa only [norm_neg] using norm_add_le (-(y p ^ 2))
        ((1 - y p) * (1 + x p)⁻¹ * tail p)
    _ <= ‖y p ^ 2‖ + (2 * C) * ‖tail p‖ := by
      gcongr
      rw [norm_mul, norm_mul]
      have hone : ‖1 - y p‖ <= 2 := by
        calc
          ‖1 - y p‖ <= ‖(1 : Complex)‖ + ‖y p‖ := norm_sub_le _ _
          _ <= 2 := by norm_num; linarith
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      exact mul_le_mul hone hinv (norm_nonneg _) (by norm_num)

private theorem zeta_reciprocal_euler_hasProd (w : Complex) (hw : 1 < w.re) :
    HasProd (fun p : Nat.Primes =>
      1 - (p : Complex) ^ (-w)) (riemannZeta w)⁻¹ := by
  have hnorm : Summable (fun p : Nat.Primes =>
      ‖-((p : Complex) ^ (-w))‖) := by
    have hexponent : -w.re < -1 := by linarith
    refine (Nat.Primes.summable_rpow.mpr hexponent).congr fun p => ?_
    rw [norm_neg, Complex.norm_natCast_cpow_of_pos p.prop.pos]
    simp only [Complex.neg_re]
  have hdirect : Multipliable (fun p : Nat.Primes =>
      1 - (p : Complex) ^ (-w)) := by
    have h := multipliable_one_add_of_summable hnorm
    refine h.congr fun p => ?_
    ring
  have hzeta := riemannZeta_eulerProduct_hasProd hw
  let directProduct : Complex :=
    ∏' p : Nat.Primes, (1 - (p : Complex) ^ (-w))
  have hlocal (p : Nat.Primes) :
      (1 - (p : Complex) ^ (-w)) *
        (1 - (p : Complex) ^ (-w))⁻¹ = 1 := by
    apply mul_inv_cancel₀
    rw [sub_ne_zero]
    intro heq
    have hnorm_lt : ‖(p : Complex) ^ (-w)‖ < 1 := by
      rw [Complex.norm_natCast_cpow_of_pos p.prop.pos]
      simp only [Complex.neg_re]
      exact Real.rpow_lt_one_of_one_lt_of_neg
        (by exact_mod_cast p.prop.one_lt) (by linarith)
    rw [← heq, norm_one] at hnorm_lt
    exact lt_irrefl 1 hnorm_lt
  have hcombined : HasProd (fun _ : Nat.Primes => (1 : Complex))
      (directProduct * riemannZeta w) := by
    dsimp [directProduct]
    exact (hdirect.hasProd.mul hzeta).congr_fun fun p => (hlocal p).symm
  have hvalue : directProduct * riemannZeta w = 1 :=
    HasProd.unique hcombined hasProd_one
  have hzeta_ne : riemannZeta w ≠ 0 :=
    riemannZeta_ne_zero_of_one_le_re hw.le
  have htprod : directProduct = (riemannZeta w)⁻¹ :=
    (mul_eq_one_iff_eq_inv₀ hzeta_ne).mp hvalue
  rw [← htprod]
  simpa [directProduct] using hdirect.hasProd

private theorem second_normalized_factor_multipliable (s : Complex)
    (hs : 1 / Real.goldenRatio ^ 4 < s.re) :
    Multipliable (fun p : Nat.Primes =>
      (1 - (p : Complex) ^
          (-s * ((Real.goldenRatio ^ 3 : Real) : Complex))) *
        (1 + (p : Complex) ^
          (-s * ((Real.goldenRatio ^ 2 : Real) : Complex)))⁻¹ *
        germLocalFactor s p) := by
  have hdev := second_normalized_factor_deviation_norm_summable s hs
  have hproduct := multipliable_one_add_of_summable hdev
  refine hproduct.congr fun p => ?_
  ring

private theorem germ_product_second_factorization (s : Complex)
    (hs : 1 / Real.goldenRatio ^ 2 < s.re) :
    (∏' p : Nat.Primes, germLocalFactor s p) =
      riemannZeta (((Real.goldenRatio ^ 2 : Real) : Complex) * s) *
        riemannZeta (((Real.goldenRatio ^ 3 : Real) : Complex) * s) *
        (riemannZeta (((2 * Real.goldenRatio ^ 2 : Real) : Complex) * s))⁻¹ *
        ∏' p : Nat.Primes,
          (1 - (p : Complex) ^
              (-s * ((Real.goldenRatio ^ 3 : Real) : Complex))) *
            (1 + (p : Complex) ^
              (-s * ((Real.goldenRatio ^ 2 : Real) : Complex)))⁻¹ *
            germLocalFactor s p := by
  have hphi2 : 0 < Real.goldenRatio ^ 2 := by positivity
  have hphi3 : 0 < Real.goldenRatio ^ 3 := by positivity
  have hphi2_lt_phi3 : Real.goldenRatio ^ 2 < Real.goldenRatio ^ 3 := by
    calc
      Real.goldenRatio ^ 2 < Real.goldenRatio ^ 2 * Real.goldenRatio :=
        (lt_mul_iff_one_lt_right hphi2).mpr Real.one_lt_goldenRatio
      _ = Real.goldenRatio ^ 3 := by ring
  have hphi2_lt_phi4 : Real.goldenRatio ^ 2 < Real.goldenRatio ^ 4 := by
    nlinarith [Real.goldenRatio_sq]
  have hs4 : 1 / Real.goldenRatio ^ 4 < s.re := by
    exact (one_div_lt_one_div_of_lt hphi2 hphi2_lt_phi4).trans hs
  have hdomain2 :
      1 < ((((Real.goldenRatio ^ 2 : Real) : Complex) * s).re) := by
    rw [Complex.mul_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    simpa [mul_comm] using (div_lt_iff₀ hphi2).mp hs
  have hdomain3 :
      1 < ((((Real.goldenRatio ^ 3 : Real) : Complex) * s).re) := by
    rw [Complex.mul_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    have hscaled := mul_lt_mul_of_pos_right hphi2_lt_phi3
      (lt_trans (by positivity) hs)
    have hbase := (div_lt_iff₀ hphi2).mp hs
    nlinarith
  have hdomainDouble :
      1 < ((((2 * Real.goldenRatio ^ 2 : Real) : Complex) * s).re) := by
    rw [Complex.mul_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    have hbase := (div_lt_iff₀ hphi2).mp hs
    nlinarith
  have hfirst := riemannZeta_eulerProduct_hasProd hdomain2
  have hsecond := riemannZeta_eulerProduct_hasProd hdomain3
  have hreciprocal := zeta_reciprocal_euler_hasProd
    (((2 * Real.goldenRatio ^ 2 : Real) : Complex) * s) hdomainDouble
  have hnormalized := second_normalized_factor_multipliable s hs4
  have hcombined := ((hfirst.mul hsecond).mul hreciprocal).mul hnormalized.hasProd
  have hlocal (p : Nat.Primes) :
      (1 - (p : Complex) ^
          (-(((Real.goldenRatio ^ 2 : Real) : Complex) * s)))⁻¹ *
        (1 - (p : Complex) ^
          (-(((Real.goldenRatio ^ 3 : Real) : Complex) * s)))⁻¹ *
        (1 - (p : Complex) ^
          (-(((2 * Real.goldenRatio ^ 2 : Real) : Complex) * s))) *
        ((1 - (p : Complex) ^
            (-s * ((Real.goldenRatio ^ 3 : Real) : Complex))) *
          (1 + (p : Complex) ^
            (-s * ((Real.goldenRatio ^ 2 : Real) : Complex)))⁻¹ *
          germLocalFactor s p) = germLocalFactor s p := by
    let x : Complex := (p : Complex) ^
      (-s * ((Real.goldenRatio ^ 2 : Real) : Complex))
    let y : Complex := (p : Complex) ^
      (-s * ((Real.goldenRatio ^ 3 : Real) : Complex))
    have hxlt : ‖x‖ < 1 := by
      simpa [x] using first_mode_norm_lt_one s hs4 p
    have hylt : ‖y‖ < 1 := by
      have hspos : 0 < s.re := lt_trans (by positivity) hs4
      dsimp [y]
      rw [Complex.norm_natCast_cpow_of_pos p.prop.pos]
      rw [show (-s * ((Real.goldenRatio ^ 3 : Real) : Complex)).re =
        -s.re * Real.goldenRatio ^ 3 by
          simp only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re,
            Complex.ofReal_im, mul_zero, sub_zero]]
      exact Real.rpow_lt_one_of_one_lt_of_neg
        (by exact_mod_cast p.prop.one_lt)
        (mul_neg_of_neg_of_pos (neg_neg_of_pos hspos) hphi3)
    have hxminus : 1 - x ≠ 0 := by
      rw [sub_ne_zero]
      intro hx
      rw [← hx, norm_one] at hxlt
      exact lt_irrefl 1 hxlt
    have hyminus : 1 - y ≠ 0 := by
      rw [sub_ne_zero]
      intro hy
      rw [← hy, norm_one] at hylt
      exact lt_irrefl 1 hylt
    have hxplus : 1 + x ≠ 0 := by
      intro hx
      have hxneg : x = -1 := by linear_combination hx
      rw [hxneg, norm_neg, norm_one] at hxlt
      exact lt_irrefl 1 hxlt
    have hfirstPower :
        (p : Complex) ^
          (-(((Real.goldenRatio ^ 2 : Real) : Complex) * s)) = x := by
      dsimp [x]
      congr 1
      ring
    have hsecondPower :
        (p : Complex) ^
          (-(((Real.goldenRatio ^ 3 : Real) : Complex) * s)) = y := by
      dsimp [y]
      congr 1
      ring
    have hdoublePower :
        (p : Complex) ^
          (-(((2 * Real.goldenRatio ^ 2 : Real) : Complex) * s)) = x ^ 2 := by
      have hexponent :
          -(((2 * Real.goldenRatio ^ 2 : Real) : Complex) * s) =
            (-s * ((Real.goldenRatio ^ 2 : Real) : Complex)) +
              (-s * ((Real.goldenRatio ^ 2 : Real) : Complex)) := by
        push_cast
        ring
      rw [hexponent, Complex.cpow_add _ _ (by
        exact_mod_cast p.prop.ne_zero)]
      change x * x = x ^ 2
      ring
    rw [hfirstPower, hsecondPower, hdoublePower]
    change (1 - x)⁻¹ * (1 - y)⁻¹ * (1 - x ^ 2) *
      ((1 - y) * (1 + x)⁻¹ * germLocalFactor s p) = germLocalFactor s p
    field_simp [hxminus, hyminus, hxplus]
    ring
  have hfactored : HasProd (fun p : Nat.Primes => germLocalFactor s p)
      (riemannZeta (((Real.goldenRatio ^ 2 : Real) : Complex) * s) *
        riemannZeta (((Real.goldenRatio ^ 3 : Real) : Complex) * s) *
        (riemannZeta (((2 * Real.goldenRatio ^ 2 : Real) : Complex) * s))⁻¹ *
        ∏' p : Nat.Primes,
          (1 - (p : Complex) ^
              (-s * ((Real.goldenRatio ^ 3 : Real) : Complex))) *
            (1 + (p : Complex) ^
              (-s * ((Real.goldenRatio ^ 2 : Real) : Complex)))⁻¹ *
            germLocalFactor s p) :=
    hcombined.congr_fun fun p => (hlocal p).symm
  exact (germLocalFactor_multipliable s hs).hasProd.unique hfactored

theorem golden_germ_second_order_factorization :
    let G3 : Complex -> Complex := fun s =>
      ∏' p : Nat.Primes,
        (1 - (p : Complex) ^
            (-s * ((Real.goldenRatio ^ 3 : Real) : Complex))) *
          (1 + (p : Complex) ^
            (-s * ((Real.goldenRatio ^ 2 : Real) : Complex)))⁻¹ *
          germLocalFactor s p
    (∃! continuedGerm :
        {s : Complex // 1 / Real.goldenRatio ^ 4 < s.re} -> Complex,
      (∀ s, 1 / Real.goldenRatio ^ 2 < s.1.re ->
        continuedGerm s = ∏' p : Nat.Primes, germLocalFactor s.1 p) ∧
      (∀ s, continuedGerm s =
        riemannZeta (((Real.goldenRatio ^ 2 : Real) : Complex) * s.1) *
          riemannZeta (((Real.goldenRatio ^ 3 : Real) : Complex) * s.1) *
          (riemannZeta (((2 * Real.goldenRatio ^ 2 : Real) : Complex) * s.1))⁻¹ *
          G3 s.1)) ∧
    (∀ s : Complex, 1 / Real.goldenRatio ^ 4 < s.re ->
      Summable (fun p : Nat.Primes =>
        ‖(1 - (p : Complex) ^
            (-s * ((Real.goldenRatio ^ 3 : Real) : Complex))) *
          (1 + (p : Complex) ^
            (-s * ((Real.goldenRatio ^ 2 : Real) : Complex)))⁻¹ *
          germLocalFactor s p - 1‖)) := by
  dsimp only
  let continuedGerm :
      {s : Complex // 1 / Real.goldenRatio ^ 4 < s.re} -> Complex := fun s =>
    riemannZeta (((Real.goldenRatio ^ 2 : Real) : Complex) * s.1) *
      riemannZeta (((Real.goldenRatio ^ 3 : Real) : Complex) * s.1) *
      (riemannZeta (((2 * Real.goldenRatio ^ 2 : Real) : Complex) * s.1))⁻¹ *
      ∏' p : Nat.Primes,
        (1 - (p : Complex) ^
            (-s.1 * ((Real.goldenRatio ^ 3 : Real) : Complex))) *
          (1 + (p : Complex) ^
            (-s.1 * ((Real.goldenRatio ^ 2 : Real) : Complex)))⁻¹ *
          germLocalFactor s.1 p
  refine ⟨?_, second_normalized_factor_deviation_norm_summable⟩
  refine ⟨continuedGerm, ?_, ?_⟩
  · constructor
    · intro s hs
      exact (germ_product_second_factorization s.1 hs).symm
    · intro s
      rfl
  · intro other hother
    funext s
    rw [hother.2 s]

end

end D5.S3.Analytic.EulerGerm.GoldenGermSecondOrderFactorization
