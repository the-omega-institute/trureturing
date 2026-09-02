/- GID: D5/S3/Analytic/EulerGerm/GoldenGermThirdOrderLedger
   generality: I
   mirror-B: D5/B/S3/Analytic/EulerGerm/GoldenGermThirdOrderLedger
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Explicit third-order golden Euler ledger and cancellation below phi^5. -/

import D5.S3.Analytic.GoldenEulerBeta
import D5.S3.Analytic.EulerGerm.GoldenLocalFactor
import Mathlib.Topology.Algebra.InfiniteSum.Group

/- Library-search audit trail (2026-09-03):
   * The frozen `golden_germ_second_order_factorization` supplies the global
     factorization and its unique continuation, but does not expose the local
     normalized remainder needed by this ledger.
   * This module therefore reuses the canonical definitions `germLocalFactor`
     and `o5Beta`, together with `o5_beta_zero`, `o5_beta_power_law`,
     `o5_beta_closed_form`, and `o5_beta_growth`, while proving the required
     local identity independently from the six-mode expansion.
   * Pinned Mathlib supplies floor bounds, complex-power addition, prime rpow
     summability, product summability, and natural head-tail splitting. -/

namespace D5.S3.Analytic.EulerGerm.GoldenGermThirdOrderLedger

set_option autoImplicit false
set_option relaxedAutoImplicit false

open D5.S3.Analytic.GoldenEulerBeta
open D5.S3.Analytic.EulerGerm.GoldenLocalFactor

noncomputable section

private theorem prime_real_pos (p : Nat.Primes) : 0 < (p : Real) := by
  exact_mod_cast p.prop.pos

private theorem goldenRatio_gt_eight_fifths :
    (8 : Real) / 5 < Real.goldenRatio := by
  rw [Real.goldenRatio]
  have hsqrt_sq : Real.sqrt 5 ^ 2 = (5 : Real) :=
    Real.sq_sqrt (by norm_num)
  have hsqrt_nonneg : 0 <= Real.sqrt 5 := Real.sqrt_nonneg 5
  nlinarith

private theorem goldenRatio_lt_five_thirds :
    Real.goldenRatio < (5 : Real) / 3 := by
  rw [Real.goldenRatio]
  have hsqrt_sq : Real.sqrt 5 ^ 2 = (5 : Real) :=
    Real.sq_sqrt (by norm_num)
  have hsqrt_nonneg : 0 <= Real.sqrt 5 := Real.sqrt_nonneg 5
  nlinarith

private theorem floor_five_mul_goldenRatio :
    ⌊(5 : Real) * Real.goldenRatio⌋ = (8 : Int) := by
  rw [Int.floor_eq_iff]
  constructor <;> norm_num at * <;>
    nlinarith [goldenRatio_gt_eight_fifths,
      goldenRatio_lt_five_thirds]

private theorem floor_six_mul_goldenRatio :
    ⌊(6 : Real) * Real.goldenRatio⌋ = (9 : Int) := by
  rw [Int.floor_eq_iff]
  constructor <;> norm_num at * <;>
    nlinarith [goldenRatio_gt_eight_fifths,
      goldenRatio_lt_five_thirds]

private theorem o5_beta_four :
    o5Beta 4 = 2 * Real.goldenRatio ^ 2 + Real.goldenRatio ^ 3 := by
  have hcube :
      Real.goldenRatio ^ 3 = 2 * Real.goldenRatio + 1 := by
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
  nlinarith [Real.goldenRatio_sq]

private theorem o5_beta_five :
    o5Beta 5 = Real.goldenRatio ^ 5 := by
  have hcube :
      Real.goldenRatio ^ 3 = 2 * Real.goldenRatio + 1 := by
    calc
      Real.goldenRatio ^ 3 =
          Real.goldenRatio * Real.goldenRatio ^ 2 := by ring
      _ = Real.goldenRatio * (Real.goldenRatio + 1) := by
        rw [Real.goldenRatio_sq]
      _ = 2 * Real.goldenRatio + 1 := by
        nlinarith [Real.goldenRatio_sq]
  have hfifth :
      Real.goldenRatio ^ 5 = 3 + 5 * Real.goldenRatio := by
    calc
      Real.goldenRatio ^ 5 =
          Real.goldenRatio ^ 3 * Real.goldenRatio ^ 2 := by ring
      _ = (2 * Real.goldenRatio + 1) *
          (Real.goldenRatio + 1) := by
        rw [hcube, Real.goldenRatio_sq]
      _ = 3 + 5 * Real.goldenRatio := by
        nlinarith [Real.goldenRatio_sq]
  rw [o5Beta]
  norm_num
  rw [floor_six_mul_goldenRatio, hfifth]
  ring

private theorem o5_beta_four_lt_fifth :
    o5Beta 4 < Real.goldenRatio ^ 5 := by
  have hcube :
      Real.goldenRatio ^ 3 = 2 * Real.goldenRatio + 1 := by
    calc
      Real.goldenRatio ^ 3 =
          Real.goldenRatio * Real.goldenRatio ^ 2 := by ring
      _ = Real.goldenRatio * (Real.goldenRatio + 1) := by
        rw [Real.goldenRatio_sq]
      _ = 2 * Real.goldenRatio + 1 := by
        nlinarith [Real.goldenRatio_sq]
  have hfifth :
      Real.goldenRatio ^ 5 = 3 + 5 * Real.goldenRatio := by
    calc
      Real.goldenRatio ^ 5 =
          Real.goldenRatio ^ 3 * Real.goldenRatio ^ 2 := by ring
      _ = (2 * Real.goldenRatio + 1) *
          (Real.goldenRatio + 1) := by
        rw [hcube, Real.goldenRatio_sq]
      _ = 3 + 5 * Real.goldenRatio := by
        nlinarith [Real.goldenRatio_sq]
  have hle : o5Beta 4 <= Real.goldenRatio ^ 5 := by
    rw [o5_beta_four, hfifth, hcube, Real.goldenRatio_sq]
    nlinarith [Real.one_lt_goldenRatio]
  exact lt_of_le_of_ne hle o5_beta_power_law_terminates

private theorem golden_fifth :
    Real.goldenRatio ^ 5 =
      Real.goldenRatio ^ 2 + 2 * Real.goldenRatio ^ 3 := by
  have hcube :
      Real.goldenRatio ^ 3 = 2 * Real.goldenRatio + 1 := by
    calc
      Real.goldenRatio ^ 3 =
          Real.goldenRatio * Real.goldenRatio ^ 2 := by ring
      _ = Real.goldenRatio * (Real.goldenRatio + 1) := by
        rw [Real.goldenRatio_sq]
      _ = 2 * Real.goldenRatio + 1 := by
        nlinarith [Real.goldenRatio_sq]
  have hfifth :
      Real.goldenRatio ^ 5 = 3 + 5 * Real.goldenRatio := by
    calc
      Real.goldenRatio ^ 5 =
          Real.goldenRatio ^ 3 * Real.goldenRatio ^ 2 := by ring
      _ = (2 * Real.goldenRatio + 1) *
          (Real.goldenRatio + 1) := by
        rw [hcube, Real.goldenRatio_sq]
      _ = 3 + 5 * Real.goldenRatio := by
        nlinarith [Real.goldenRatio_sq]
  rw [hfifth, hcube, Real.goldenRatio_sq]
  ring

private theorem one_tenth_in_third_order_domain :
    1 / Real.goldenRatio ^ 5 < (1 : Real) / 10 := by
  have hcube :
      Real.goldenRatio ^ 3 = 2 * Real.goldenRatio + 1 := by
    calc
      Real.goldenRatio ^ 3 =
          Real.goldenRatio * Real.goldenRatio ^ 2 := by ring
      _ = Real.goldenRatio * (Real.goldenRatio + 1) := by
        rw [Real.goldenRatio_sq]
      _ = 2 * Real.goldenRatio + 1 := by
        nlinarith [Real.goldenRatio_sq]
  have hfifth :
      Real.goldenRatio ^ 5 = 3 + 5 * Real.goldenRatio := by
    calc
      Real.goldenRatio ^ 5 =
          Real.goldenRatio ^ 3 * Real.goldenRatio ^ 2 := by ring
      _ = (2 * Real.goldenRatio + 1) *
          (Real.goldenRatio + 1) := by
        rw [hcube, Real.goldenRatio_sq]
      _ = 3 + 5 * Real.goldenRatio := by
        nlinarith [Real.goldenRatio_sq]
  have hten : (10 : Real) < Real.goldenRatio ^ 5 := by
    rw [hfifth]
    nlinarith [goldenRatio_gt_eight_fifths]
  exact one_div_lt_one_div_of_lt (by norm_num) hten

private theorem o5_beta_six_add_ge (k : Nat) :
    Real.goldenRatio ^ 5 + (k : Real) <= o5Beta (k + 6) := by
  have hsqrt_sq : Real.sqrt 5 ^ 2 = (5 : Real) :=
    Real.sq_sqrt (by norm_num)
  have hsqrt_nonneg : 0 <= Real.sqrt 5 := Real.sqrt_nonneg 5
  have hsqrt_two : 2 < Real.sqrt 5 := by nlinarith
  have hphi_inv :
      1 / Real.goldenRatio = Real.goldenRatio - 1 := by
    rw [one_div, Real.inv_goldenRatio]
    linarith [Real.goldenRatio_add_goldenConj]
  have hfifth :
      Real.goldenRatio ^ 5 = 3 + 5 * Real.goldenRatio := by
    rw [show Real.goldenRatio ^ 5 =
        (Real.goldenRatio ^ 2) ^ 2 * Real.goldenRatio by ring,
      Real.goldenRatio_sq]
    nlinarith [Real.goldenRatio_sq]
  apply le_trans _ (o5_beta_growth (k + 6))
  rw [hphi_inv, hfifth]
  push_cast
  have hk : 0 <= (k : Real) := by positivity
  rw [Real.goldenRatio]
  ring_nf
  nlinarith

private theorem mixed_mode_cpow (s : Complex) (p : Nat.Primes)
    (a b : Nat) :
    (p : Complex) ^
        (-s * ((((a : Real) * Real.goldenRatio ^ 2 +
          (b : Real) * Real.goldenRatio ^ 3) : Real) : Complex)) =
      ((p : Complex) ^
          (-s * ((Real.goldenRatio ^ 2 : Real) : Complex))) ^ a *
        ((p : Complex) ^
          (-s * ((Real.goldenRatio ^ 3 : Real) : Complex))) ^ b := by
  have hbase : (p : Complex) ≠ 0 := by
    exact_mod_cast p.prop.ne_zero
  have hexponent :
      -s * ((((a : Real) * Real.goldenRatio ^ 2 +
        (b : Real) * Real.goldenRatio ^ 3) : Real) : Complex) =
        (a : Complex) *
            (-s * ((Real.goldenRatio ^ 2 : Real) : Complex)) +
          (b : Complex) *
            (-s * ((Real.goldenRatio ^ 3 : Real) : Complex)) := by
    push_cast
    ring
  rw [hexponent, Complex.cpow_add _ _ hbase]
  exact congrArg₂ (fun z w : Complex => z * w)
    (Complex.cpow_nat_mul (p : Complex) a
      (-s * ((Real.goldenRatio ^ 2 : Real) : Complex)))
    (Complex.cpow_nat_mul (p : Complex) b
      (-s * ((Real.goldenRatio ^ 3 : Real) : Complex)))

private theorem mixed_mode_norm_summable (s : Complex)
    (hs : 1 / Real.goldenRatio ^ 5 < s.re) (a b : Nat)
    (hweight : Real.goldenRatio ^ 5 <=
      (a : Real) * Real.goldenRatio ^ 2 +
        (b : Real) * Real.goldenRatio ^ 3) :
    Summable (fun p : Nat.Primes =>
      ‖((p : Complex) ^
          (-s * ((Real.goldenRatio ^ 2 : Real) : Complex))) ^ a *
        ((p : Complex) ^
          (-s * ((Real.goldenRatio ^ 3 : Real) : Complex))) ^ b‖) := by
  let weight : Real :=
    (a : Real) * Real.goldenRatio ^ 2 +
      (b : Real) * Real.goldenRatio ^ 3
  have hspos : 0 < s.re := lt_trans (by positivity) hs
  have hcritical : 1 < s.re * Real.goldenRatio ^ 5 :=
    (div_lt_iff₀ (by positivity : 0 < Real.goldenRatio ^ 5)).mp
      (by simpa [div_eq_mul_inv] using hs)
  have hscaled : s.re * Real.goldenRatio ^ 5 <= s.re * weight :=
    mul_le_mul_of_nonneg_left (by simpa [weight] using hweight) hspos.le
  have hexponent : -s.re * weight < -1 := by linarith
  refine (Nat.Primes.summable_rpow.mpr hexponent).congr fun p => ?_
  rw [← mixed_mode_cpow s p a b]
  rw [Complex.norm_natCast_cpow_of_pos p.prop.pos]
  simp only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero]
  simp only [weight]

private theorem mixed_mode_norm_le_one (s : Complex)
    (hs : 1 / Real.goldenRatio ^ 5 < s.re) (p : Nat.Primes)
    (a b : Nat)
    (hweight : 0 < (a : Real) * Real.goldenRatio ^ 2 +
      (b : Real) * Real.goldenRatio ^ 3) :
    ‖((p : Complex) ^
        (-s * ((Real.goldenRatio ^ 2 : Real) : Complex))) ^ a *
      ((p : Complex) ^
        (-s * ((Real.goldenRatio ^ 3 : Real) : Complex))) ^ b‖ <= 1 := by
  have hspos : 0 < s.re := lt_trans (by positivity) hs
  rw [← mixed_mode_cpow s p a b]
  rw [Complex.norm_natCast_cpow_of_pos p.prop.pos]
  simp only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero]
  exact Real.rpow_le_one_of_one_le_of_nonpos
    (by exact_mod_cast p.prop.one_le) (by nlinarith)

private theorem mixed_mode_norm_lt_one (s : Complex)
    (hs : 1 / Real.goldenRatio ^ 5 < s.re) (p : Nat.Primes)
    (a b : Nat)
    (hweight : 0 < (a : Real) * Real.goldenRatio ^ 2 +
      (b : Real) * Real.goldenRatio ^ 3) :
    ‖((p : Complex) ^
        (-s * ((Real.goldenRatio ^ 2 : Real) : Complex))) ^ a *
      ((p : Complex) ^
        (-s * ((Real.goldenRatio ^ 3 : Real) : Complex))) ^ b‖ < 1 := by
  have hspos : 0 < s.re := lt_trans (by positivity) hs
  rw [← mixed_mode_cpow s p a b]
  rw [Complex.norm_natCast_cpow_of_pos p.prop.pos]
  simp only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero]
  exact Real.rpow_lt_one_of_one_lt_of_neg
    (by exact_mod_cast p.prop.one_lt) (by nlinarith)

private theorem mixed_mode_norm_le_two (s : Complex)
    (hs : 1 / Real.goldenRatio ^ 5 < s.re) (p : Nat.Primes)
    (a b : Nat)
    (hweight : 0 <= (a : Real) * Real.goldenRatio ^ 2 +
      (b : Real) * Real.goldenRatio ^ 3) :
    ‖((p : Complex) ^
        (-s * ((Real.goldenRatio ^ 2 : Real) : Complex))) ^ a *
      ((p : Complex) ^
        (-s * ((Real.goldenRatio ^ 3 : Real) : Complex))) ^ b‖ <=
      (2 : Real) ^
        (-s.re * ((a : Real) * Real.goldenRatio ^ 2 +
          (b : Real) * Real.goldenRatio ^ 3)) := by
  have hspos : 0 < s.re := lt_trans (by positivity) hs
  rw [← mixed_mode_cpow s p a b]
  rw [Complex.norm_natCast_cpow_of_pos p.prop.pos]
  simp only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero]
  exact Real.rpow_le_rpow_of_nonpos (by norm_num)
    (by exact_mod_cast p.prop.two_le) (by nlinarith)

private theorem sixth_tail_real_summable (sigma : Real)
    (hsigma : 1 / Real.goldenRatio ^ 5 < sigma) :
    Summable (fun q : Nat.Primes × Nat =>
      (q.1 : Real) ^ (-sigma * o5Beta (q.2 + 6))) := by
  have hphi : 0 < Real.goldenRatio ^ 5 := by positivity
  have hcritical : 1 < sigma * Real.goldenRatio ^ 5 :=
    (div_lt_iff₀ hphi).mp (by simpa [div_eq_mul_inv] using hsigma)
  have hsigma_pos : 0 < sigma := lt_trans (by positivity) hsigma
  let r : Real := -sigma * Real.goldenRatio ^ 5
  let q : Real := (2 : Real) ^ (-sigma)
  have hr : r < -1 := by dsimp [r]; linarith
  have hq_nonneg : 0 <= q := by dsimp [q]; positivity
  have hq_lt_one : q < 1 := by
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num)
      (neg_neg_of_pos hsigma_pos)
  have hbase : Summable (fun p : Nat.Primes => (p : Real) ^ r) :=
    Nat.Primes.summable_rpow.mpr hr
  have hslice (k : Nat) :
      Summable (fun p : Nat.Primes =>
        (p : Real) ^ (-sigma * o5Beta (k + 6))) := by
    apply Nat.Primes.summable_rpow.mpr
    have hbeta := o5_beta_six_add_ge k
    nlinarith
  have hterm (k : Nat) (p : Nat.Primes) :
      (p : Real) ^ (-sigma * o5Beta (k + 6)) <=
        (p : Real) ^ r * q ^ k := by
    have hp_one : 1 <= (p : Real) := by
      exact_mod_cast p.prop.one_lt.le
    have hp_two : (2 : Real) <= (p : Real) := by
      exact_mod_cast p.prop.two_le
    have hbeta := o5_beta_six_add_ge k
    have hk : 0 <= (k : Real) := by positivity
    calc
      (p : Real) ^ (-sigma * o5Beta (k + 6)) <=
          (p : Real) ^
            (-sigma * (Real.goldenRatio ^ 5 + (k : Real))) :=
        Real.rpow_le_rpow_of_exponent_le hp_one (by nlinarith)
      _ = (p : Real) ^ r *
          (p : Real) ^ (-sigma * (k : Real)) := by
        rw [← Real.rpow_add (prime_real_pos p)]
        dsimp [r]
        congr 1
        ring
      _ <= (p : Real) ^ r *
          (2 : Real) ^ (-sigma * (k : Real)) := by
        exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_nonpos (z := -sigma * (k : Real))
            (by norm_num) hp_two
            (mul_nonpos_of_nonpos_of_nonneg (by linarith) hk))
          (by positivity)
      _ = (p : Real) ^ r * q ^ k := by
        dsimp [q]
        rw [← Real.rpow_mul_natCast (by norm_num : (0 : Real) <= 2)]
  have htsum (k : Nat) :
      (∑' p : Nat.Primes,
          (p : Real) ^ (-sigma * o5Beta (k + 6))) <=
        (∑' p : Nat.Primes, (p : Real) ^ r) * q ^ k := by
    calc
      (∑' p : Nat.Primes,
          (p : Real) ^ (-sigma * o5Beta (k + 6))) <=
          ∑' p : Nat.Primes, (p : Real) ^ r * q ^ k :=
        (hslice k).tsum_le_tsum (hterm k) (hbase.mul_right (q ^ k))
      _ = (∑' p : Nat.Primes, (p : Real) ^ r) * q ^ k :=
        tsum_mul_right
  have houter : Summable (fun k : Nat =>
      ∑' p : Nat.Primes,
        (p : Real) ^ (-sigma * o5Beta (k + 6))) :=
    ((summable_geometric_of_lt_one hq_nonneg hq_lt_one).mul_left
      (∑' p : Nat.Primes, (p : Real) ^ r)).of_nonneg_of_le
        (fun _ => by positivity) htsum
  have hswapped : Summable (fun kp : Nat × Nat.Primes =>
      (kp.2 : Real) ^ (-sigma * o5Beta (kp.1 + 6))) :=
    (summable_prod_of_nonneg (fun _ => by positivity)).mpr
      ⟨hslice, houter⟩
  exact (Equiv.prodComm Nat.Primes Nat).summable_iff.mpr hswapped

private theorem sixth_tail_norm_summable (s : Complex)
    (hs : 1 / Real.goldenRatio ^ 5 < s.re) :
    Summable (fun q : Nat.Primes × Nat =>
      ‖(q.1 : Complex) ^
        (-s * (o5Beta (q.2 + 6) : Complex))‖) := by
  refine (sixth_tail_real_summable s.re hs).congr fun q => ?_
  rw [Complex.norm_natCast_cpow_of_pos q.1.prop.pos]
  simp only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero]

private theorem local_factor_eq_six_modes_and_tail (s : Complex)
    (hs : 1 / Real.goldenRatio ^ 5 < s.re) (p : Nat.Primes) :
    let x := (p : Complex) ^
      (-s * ((Real.goldenRatio ^ 2 : Real) : Complex))
    let y := (p : Complex) ^
      (-s * ((Real.goldenRatio ^ 3 : Real) : Complex))
    let tail := ∑' k : Nat,
      (p : Complex) ^ (-s * (o5Beta (k + 6) : Complex))
    germLocalFactor s p =
      1 + x + y + x * y + x ^ 2 * y + x * y ^ 2 + tail := by
  dsimp only
  let x : Complex := (p : Complex) ^
    (-s * ((Real.goldenRatio ^ 2 : Real) : Complex))
  let y : Complex := (p : Complex) ^
    (-s * ((Real.goldenRatio ^ 3 : Real) : Complex))
  let f : Nat -> Complex := fun v =>
    (p : Complex) ^ (-s * (o5Beta v : Complex))
  have htail : Summable (fun k : Nat => f (k + 6)) := by
    exact ((sixth_tail_norm_summable s hs).prod_factor p).of_norm
  have hall : Summable f := (summable_nat_add_iff 6).1 (by
    simpa [f, Nat.add_comm] using htail)
  have hphi4 : Real.goldenRatio ^ 4 =
      Real.goldenRatio ^ 2 + Real.goldenRatio ^ 3 := by
    calc
      Real.goldenRatio ^ 4 =
          Real.goldenRatio ^ 2 * Real.goldenRatio ^ 2 := by ring
      _ = Real.goldenRatio ^ 2 * (Real.goldenRatio + 1) := by
        rw [Real.goldenRatio_sq]
      _ = Real.goldenRatio ^ 2 + Real.goldenRatio ^ 3 := by ring
  have hf0 : f 0 = 1 := by simp [f, o5_beta_zero]
  have hf1 : f 1 = x := by
    simp only [f, o5_beta_power_law.1]
    rfl
  have hf2 : f 2 = y := by
    simp only [f, o5_beta_power_law.2.1]
    rfl
  have hf3 : f 3 = x * y := by
    simp only [f, o5_beta_power_law.2.2]
    rw [hphi4]
    simpa [x, y] using mixed_mode_cpow s p 1 1
  have hf4 : f 4 = x ^ 2 * y := by
    simp only [f, o5_beta_four]
    simpa [x, y] using mixed_mode_cpow s p 2 1
  have hf5 : f 5 = x * y ^ 2 := by
    simp only [f, o5_beta_five]
    rw [golden_fifth]
    simpa [x, y] using mixed_mode_cpow s p 1 2
  have hprefix :
      (∑ v ∈ Finset.range 6, f v) =
        1 + x + y + x * y + x ^ 2 * y + x * y ^ 2 := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero,
      hf0, hf1, hf2, hf3, hf4, hf5, zero_add]
  rw [germLocalFactor, show (fun v : Nat =>
      (p : Complex) ^ (-s * (o5Beta v : Complex))) = f from rfl,
    ← hall.sum_add_tsum_nat_add 6, hprefix]

private theorem second_normalized_explicit_remainder (s : Complex)
    (hs : 1 / Real.goldenRatio ^ 5 < s.re) (p : Nat.Primes) :
    let x := (p : Complex) ^
      (-s * ((Real.goldenRatio ^ 2 : Real) : Complex))
    let y := (p : Complex) ^
      (-s * ((Real.goldenRatio ^ 3 : Real) : Complex))
    let tail := ∑' k : Nat,
      (p : Complex) ^ (-s * (o5Beta (k + 6) : Complex))
    (1 - y) * (1 + x)⁻¹ * germLocalFactor s p =
      1 - y ^ 2 + x ^ 2 * y +
        (1 + x)⁻¹ *
          (x * y ^ 2 - x ^ 3 * y - x ^ 2 * y ^ 2 - x * y ^ 3 +
            (1 - y) * tail) := by
  dsimp only
  let x : Complex := (p : Complex) ^
    (-s * ((Real.goldenRatio ^ 2 : Real) : Complex))
  let y : Complex := (p : Complex) ^
    (-s * ((Real.goldenRatio ^ 3 : Real) : Complex))
  let tail : Complex := ∑' k : Nat,
    (p : Complex) ^ (-s * (o5Beta (k + 6) : Complex))
  change (1 - y) * (1 + x)⁻¹ * germLocalFactor s p =
    1 - y ^ 2 + x ^ 2 * y +
      (1 + x)⁻¹ *
        (x * y ^ 2 - x ^ 3 * y - x ^ 2 * y ^ 2 - x * y ^ 3 +
          (1 - y) * tail)
  have hxlt : ‖x‖ < 1 := by
    simpa [x] using mixed_mode_norm_lt_one s hs p 1 0 (by positivity)
  have hx : 1 + x ≠ 0 := by
    intro hzero
    have hneg : x = -1 := by linear_combination hzero
    rw [hneg, norm_neg, norm_one] at hxlt
    exact lt_irrefl 1 hxlt
  have hlocal : germLocalFactor s p =
      1 + x + y + x * y + x ^ 2 * y + x * y ^ 2 + tail := by
    simpa [x, y, tail] using local_factor_eq_six_modes_and_tail s hs p
  rw [hlocal]
  field_simp [hx]
  ring

theorem golden_third_normalized_factor_deviation_norm_summable
    (s : Complex) (hs : 1 / Real.goldenRatio ^ 5 < s.re) :
    let x : Nat.Primes -> Complex := fun p =>
      (p : Complex) ^
        (-s * ((Real.goldenRatio ^ 2 : Real) : Complex))
    let y : Nat.Primes -> Complex := fun p =>
      (p : Complex) ^
        (-s * ((Real.goldenRatio ^ 3 : Real) : Complex))
    Summable (fun p : Nat.Primes =>
      ‖(1 - y p ^ 2)⁻¹ * (1 - x p ^ 2 * y p) *
        (1 - y p) * (1 + x p)⁻¹ * germLocalFactor s p - 1‖) := by
  dsimp only
  let x : Nat.Primes -> Complex := fun p =>
    (p : Complex) ^
      (-s * ((Real.goldenRatio ^ 2 : Real) : Complex))
  let y : Nat.Primes -> Complex := fun p =>
    (p : Complex) ^
      (-s * ((Real.goldenRatio ^ 3 : Real) : Complex))
  let tail : Nat.Primes -> Complex := fun p => ∑' k : Nat,
    (p : Complex) ^ (-s * (o5Beta (k + 6) : Complex))
  let remainder : Nat.Primes -> Complex := fun p =>
    (1 + x p)⁻¹ *
      (x p * y p ^ 2 - x p ^ 3 * y p - x p ^ 2 * y p ^ 2 -
        x p * y p ^ 3 + (1 - y p) * tail p)
  let qx : Real := (2 : Real) ^ (-s.re * Real.goldenRatio ^ 2)
  let qy : Real := (2 : Real) ^ (-s.re * (2 * Real.goldenRatio ^ 3))
  let Cx : Real := 1 / (1 - qx)
  let Cy : Real := 1 / (1 - qy)
  change Summable (fun p : Nat.Primes =>
    ‖(1 - y p ^ 2)⁻¹ * (1 - x p ^ 2 * y p) *
      (1 - y p) * (1 + x p)⁻¹ * germLocalFactor s p - 1‖)
  have hspos : 0 < s.re := lt_trans (by positivity) hs
  have hcritical : 1 < s.re * Real.goldenRatio ^ 5 :=
    (div_lt_iff₀ (by positivity : 0 < Real.goldenRatio ^ 5)).mp
      (by simpa [div_eq_mul_inv] using hs)
  have hcube :
      Real.goldenRatio ^ 3 = 2 * Real.goldenRatio + 1 := by
    calc
      Real.goldenRatio ^ 3 =
          Real.goldenRatio * Real.goldenRatio ^ 2 := by ring
      _ = Real.goldenRatio * (Real.goldenRatio + 1) := by
        rw [Real.goldenRatio_sq]
      _ = 2 * Real.goldenRatio + 1 := by
        nlinarith [Real.goldenRatio_sq]
  have h12 : Real.goldenRatio ^ 5 <=
      ((1 : Nat) : Real) * Real.goldenRatio ^ 2 +
        ((2 : Nat) : Real) * Real.goldenRatio ^ 3 := by
    simpa using golden_fifth.le
  have h31 : Real.goldenRatio ^ 5 <=
      ((3 : Nat) : Real) * Real.goldenRatio ^ 2 +
        ((1 : Nat) : Real) * Real.goldenRatio ^ 3 := by
    rw [golden_fifth, hcube, Real.goldenRatio_sq]
    norm_num
    nlinarith
  have h22 : Real.goldenRatio ^ 5 <=
      ((2 : Nat) : Real) * Real.goldenRatio ^ 2 +
        ((2 : Nat) : Real) * Real.goldenRatio ^ 3 := by
    rw [golden_fifth]
    norm_num
    nlinarith [sq_pos_of_pos Real.goldenRatio_pos]
  have h13 : Real.goldenRatio ^ 5 <=
      ((1 : Nat) : Real) * Real.goldenRatio ^ 2 +
        ((3 : Nat) : Real) * Real.goldenRatio ^ 3 := by
    rw [golden_fifth]
    norm_num
    nlinarith [show 0 < Real.goldenRatio ^ 3 by positivity]
  have h23 : Real.goldenRatio ^ 5 <=
      ((2 : Nat) : Real) * Real.goldenRatio ^ 2 +
        ((3 : Nat) : Real) * Real.goldenRatio ^ 3 := by
    rw [golden_fifth]
    norm_num
    nlinarith [sq_pos_of_pos Real.goldenRatio_pos,
      show 0 < Real.goldenRatio ^ 3 by positivity]
  have h42 : Real.goldenRatio ^ 5 <=
      ((4 : Nat) : Real) * Real.goldenRatio ^ 2 +
        ((2 : Nat) : Real) * Real.goldenRatio ^ 3 := by
    rw [golden_fifth]
    norm_num
    nlinarith [sq_pos_of_pos Real.goldenRatio_pos]
  have hqxlt : qx < 1 := by
    dsimp [qx]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num)
      (mul_neg_of_neg_of_pos (neg_neg_of_pos hspos)
        (sq_pos_of_pos Real.goldenRatio_pos))
  have hqylt : qy < 1 := by
    dsimp [qy]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num)
      (mul_neg_of_neg_of_pos (neg_neg_of_pos hspos) (by positivity))
  have hCx : 0 <= Cx := by dsimp [Cx]; positivity
  have hCy : 0 <= Cy := by dsimp [Cy]; positivity
  have hxInv (p : Nat.Primes) : ‖(1 + x p)⁻¹‖ <= Cx := by
    have hxq : ‖x p‖ <= qx := by
      simpa [x, qx] using
        mixed_mode_norm_le_two s hs p 1 0 (by positivity)
    have hlower : 1 - qx <= ‖1 + x p‖ := by
      calc
        1 - qx <= 1 - ‖x p‖ := sub_le_sub_left hxq 1
        _ = ‖(1 : Complex)‖ - ‖-x p‖ := by simp
        _ <= ‖(1 : Complex) - (-x p)‖ := norm_sub_norm_le _ _
        _ = ‖1 + x p‖ := by simp only [sub_neg_eq_add]
    rw [norm_inv]
    simpa [Cx, one_div] using
      one_div_le_one_div_of_le (sub_pos.mpr hqxlt) hlower
  have hyInv (p : Nat.Primes) : ‖(1 - y p ^ 2)⁻¹‖ <= Cy := by
    have hyq : ‖y p ^ 2‖ <= qy := by
      simpa [x, y, qy] using
        mixed_mode_norm_le_two s hs p 0 2 (by positivity)
    have hlower : 1 - qy <= ‖1 - y p ^ 2‖ := by
      calc
        1 - qy <= 1 - ‖y p ^ 2‖ := sub_le_sub_left hyq 1
        _ = ‖(1 : Complex)‖ - ‖y p ^ 2‖ := by simp
        _ <= ‖(1 : Complex) - y p ^ 2‖ := norm_sub_norm_le _ _
    rw [norm_inv]
    simpa [Cy, one_div] using
      one_div_le_one_div_of_le (sub_pos.mpr hqylt) hlower
  have hyNorm (p : Nat.Primes) : ‖y p‖ <= 1 := by
    simpa [x, y] using
      mixed_mode_norm_le_one s hs p 0 1 (by positivity)
  have haNorm (p : Nat.Primes) : ‖x p ^ 2 * y p‖ <= 1 := by
    simpa [x, y] using
      mixed_mode_norm_le_one s hs p 2 1 (by positivity)
  have hyMinus (p : Nat.Primes) : 1 - y p ^ 2 ≠ 0 := by
    rw [sub_ne_zero]
    intro heq
    have hlt : ‖y p ^ 2‖ < 1 := by
      simpa [x, y] using
        mixed_mode_norm_lt_one s hs p 0 2 (by positivity)
    rw [← heq, norm_one] at hlt
    exact lt_irrefl 1 hlt
  have htailJoint := sixth_tail_norm_summable s hs
  have htailNorm : Summable (fun p : Nat.Primes => ‖tail p‖) := by
    refine htailJoint.prod.of_nonneg_of_le (fun _ => norm_nonneg _) fun p => ?_
    exact norm_tsum_le_tsum_norm (by
      simpa [tail] using htailJoint.prod_factor p)
  have hm12 : Summable (fun p : Nat.Primes => ‖x p * y p ^ 2‖) := by
    simpa [x, y] using mixed_mode_norm_summable s hs 1 2 h12
  have hm31 : Summable (fun p : Nat.Primes => ‖x p ^ 3 * y p‖) := by
    simpa [x, y] using mixed_mode_norm_summable s hs 3 1 h31
  have hm22 : Summable (fun p : Nat.Primes => ‖x p ^ 2 * y p ^ 2‖) := by
    simpa [x, y] using mixed_mode_norm_summable s hs 2 2 h22
  have hm13 : Summable (fun p : Nat.Primes => ‖x p * y p ^ 3‖) := by
    simpa [x, y] using mixed_mode_norm_summable s hs 1 3 h13
  have hm23 : Summable (fun p : Nat.Primes => ‖x p ^ 2 * y p ^ 3‖) := by
    simpa [x, y] using mixed_mode_norm_summable s hs 2 3 h23
  have hm42 : Summable (fun p : Nat.Primes => ‖x p ^ 4 * y p ^ 2‖) := by
    simpa [x, y] using mixed_mode_norm_summable s hs 4 2 h42
  have hremMajor : Summable (fun p : Nat.Primes =>
      ‖x p * y p ^ 2‖ + ‖x p ^ 3 * y p‖ +
        ‖x p ^ 2 * y p ^ 2‖ + ‖x p * y p ^ 3‖ +
        2 * ‖tail p‖) :=
    (((hm12.add hm31).add hm22).add hm13).add (htailNorm.mul_left 2)
  have hremNorm : Summable (fun p : Nat.Primes => ‖remainder p‖) := by
    refine (hremMajor.mul_left Cx).of_norm_bounded fun p => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    have htailPart : ‖(1 - y p) * tail p‖ <= 2 * ‖tail p‖ := by
      rw [norm_mul]
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      calc
        ‖1 - y p‖ <= ‖(1 : Complex)‖ + ‖y p‖ := norm_sub_le _ _
        _ <= 2 := by norm_num; linarith [hyNorm p]
    have hinside :
        ‖x p * y p ^ 2 - x p ^ 3 * y p - x p ^ 2 * y p ^ 2 -
            x p * y p ^ 3 + (1 - y p) * tail p‖ <=
          ‖x p * y p ^ 2‖ + ‖x p ^ 3 * y p‖ +
            ‖x p ^ 2 * y p ^ 2‖ + ‖x p * y p ^ 3‖ +
            2 * ‖tail p‖ := by
      calc
        ‖x p * y p ^ 2 - x p ^ 3 * y p - x p ^ 2 * y p ^ 2 -
            x p * y p ^ 3 + (1 - y p) * tail p‖ <=
            ‖x p * y p ^ 2 - x p ^ 3 * y p - x p ^ 2 * y p ^ 2 -
              x p * y p ^ 3‖ + ‖(1 - y p) * tail p‖ := norm_add_le _ _
        _ <=
            ‖x p * y p ^ 2‖ + ‖x p ^ 3 * y p‖ +
              ‖x p ^ 2 * y p ^ 2‖ + ‖x p * y p ^ 3‖ +
              2 * ‖tail p‖ := by
          have hpoly := norm_sub_le
            (x p * y p ^ 2 - x p ^ 3 * y p - x p ^ 2 * y p ^ 2)
            (x p * y p ^ 3)
          have hpoly2 := norm_sub_le
            (x p * y p ^ 2 - x p ^ 3 * y p)
            (x p ^ 2 * y p ^ 2)
          have hpoly3 := norm_sub_le (x p * y p ^ 2) (x p ^ 3 * y p)
          linarith
    rw [show remainder p = (1 + x p)⁻¹ *
        (x p * y p ^ 2 - x p ^ 3 * y p - x p ^ 2 * y p ^ 2 -
          x p * y p ^ 3 + (1 - y p) * tail p) from rfl,
      norm_mul]
    exact mul_le_mul (hxInv p) hinside (norm_nonneg _) hCx
  have hSecond (p : Nat.Primes) :
      (1 - y p) * (1 + x p)⁻¹ * germLocalFactor s p =
        1 - y p ^ 2 + x p ^ 2 * y p + remainder p := by
    simpa [x, y, tail, remainder] using
      second_normalized_explicit_remainder s hs p
  have hdeviation (p : Nat.Primes) :
      (1 - y p ^ 2)⁻¹ * (1 - x p ^ 2 * y p) *
          (1 - y p) * (1 + x p)⁻¹ * germLocalFactor s p - 1 =
        (1 - y p ^ 2)⁻¹ *
          (remainder p - (x p ^ 2 * y p) * remainder p +
            (x p ^ 2 * y p) * y p ^ 2 - (x p ^ 2 * y p) ^ 2) := by
    calc
      (1 - y p ^ 2)⁻¹ * (1 - x p ^ 2 * y p) *
          (1 - y p) * (1 + x p)⁻¹ * germLocalFactor s p - 1 =
          (1 - y p ^ 2)⁻¹ * (1 - x p ^ 2 * y p) *
            ((1 - y p) * (1 + x p)⁻¹ * germLocalFactor s p) - 1 := by ring
      _ = (1 - y p ^ 2)⁻¹ *
          (remainder p - (x p ^ 2 * y p) * remainder p +
            (x p ^ 2 * y p) * y p ^ 2 - (x p ^ 2 * y p) ^ 2) := by
        rw [hSecond]
        field_simp [hyMinus p]
        ring
  have haY2 : Summable (fun p : Nat.Primes =>
      ‖(x p ^ 2 * y p) * y p ^ 2‖) :=
    hm23.congr fun p => by
      congr 1
      ring
  have haSquare : Summable (fun p : Nat.Primes =>
      ‖(x p ^ 2 * y p) ^ 2‖) :=
    hm42.congr fun p => by
      congr 1
      ring
  have hmajor : Summable (fun p : Nat.Primes =>
      Cy * (2 * ‖remainder p‖ + ‖(x p ^ 2 * y p) * y p ^ 2‖ +
        ‖(x p ^ 2 * y p) ^ 2‖)) :=
    (((hremNorm.mul_left 2).add haY2).add haSquare).mul_left Cy
  refine hmajor.of_norm_bounded fun p => ?_
  rw [hdeviation p, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), norm_mul]
  have haRem : ‖(x p ^ 2 * y p) * remainder p‖ <= ‖remainder p‖ := by
    rw [norm_mul]
    simpa using mul_le_of_le_one_left (norm_nonneg _) (haNorm p)
  have hinside :
      ‖remainder p - (x p ^ 2 * y p) * remainder p +
          (x p ^ 2 * y p) * y p ^ 2 - (x p ^ 2 * y p) ^ 2‖ <=
        2 * ‖remainder p‖ + ‖(x p ^ 2 * y p) * y p ^ 2‖ +
          ‖(x p ^ 2 * y p) ^ 2‖ := by
    have h1 := norm_sub_le (remainder p)
      ((x p ^ 2 * y p) * remainder p)
    have h2 := norm_add_le
      (remainder p - (x p ^ 2 * y p) * remainder p)
      ((x p ^ 2 * y p) * y p ^ 2)
    have h3 := norm_sub_le
      (remainder p - (x p ^ 2 * y p) * remainder p +
        (x p ^ 2 * y p) * y p ^ 2)
      ((x p ^ 2 * y p) ^ 2)
    linarith
  exact mul_le_mul (hyInv p) hinside (norm_nonneg _) hCy

#print axioms golden_third_normalized_factor_deviation_norm_summable

end

end D5.S3.Analytic.EulerGerm.GoldenGermThirdOrderLedger
