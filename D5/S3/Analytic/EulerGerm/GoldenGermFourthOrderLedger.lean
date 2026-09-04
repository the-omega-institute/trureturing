/- GID: D5/S3/Analytic/EulerGerm/GoldenGermFourthOrderLedger
   generality: I
   mirror-B: D5/B/S3/Analytic/EulerGerm/GoldenGermFourthOrderLedger
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Finite fourth-order golden Euler correction and beta-six summability. -/

import D5.S3.Analytic.EulerGerm.GoldenGermThirdOrderFactorization
import D5.S3.Analytic.EulerGerm.GoldenGermFourthOrderExponentCensus
import Mathlib.Topology.Algebra.InfiniteSum.Group

/- Library-search audit trail (2026-09-03):
   * The frozen fourth-order census supplies the public beta-six threshold,
     beta-seven separation, and the complete mixed-weight census through the
     beta-six boundary.  No exponent census is recomputed here.
   * The frozen third-order factorization supplies the exact normalized local
     family `K3` and its summable-deviation contract on `Re s > 1 / phi^5`;
     its first conjunct is reused below.  That contract is proved by the
     frozen third-order ledger.
   * The predecessor's local six-mode expansion and beta-four/beta-five
     evaluations are private.  They cannot be referenced across the module
     boundary, so only those definition-level calculations are repeated in
     order to expose the seventh mode and the explicit local identity.
   * Pinned Mathlib supplies `Complex.cpow_add`,
     `Nat.Primes.summable_rpow`, geometric summability, product summability,
     and norm bounds for `tsum`.  Repository and pinned-library searches found
     no existing fourth-order signed correction or beta-six certificate. -/

namespace D5.S3.Analytic.EulerGerm.GoldenGermFourthOrderLedger

set_option autoImplicit false
set_option relaxedAutoImplicit false

open D5.S3.Analytic.GoldenEulerBeta
open D5.S3.Analytic.EulerGerm.GoldenLocalFactor
open D5.S3.Analytic.EulerGerm.GoldenGermThirdOrderFactorization
open D5.S3.Analytic.EulerGerm.GoldenGermFourthOrderExponentCensus

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

private theorem golden_cube :
    Real.goldenRatio ^ 3 = 2 * Real.goldenRatio + 1 := by
  calc
    Real.goldenRatio ^ 3 =
        Real.goldenRatio * Real.goldenRatio ^ 2 := by ring
    _ = Real.goldenRatio * (Real.goldenRatio + 1) := by
      rw [Real.goldenRatio_sq]
    _ = 2 * Real.goldenRatio + 1 := by
      nlinarith [Real.goldenRatio_sq]

private theorem golden_fourth :
    Real.goldenRatio ^ 4 = 3 * Real.goldenRatio + 2 := by
  calc
    Real.goldenRatio ^ 4 = (Real.goldenRatio ^ 2) ^ 2 := by ring
    _ = (Real.goldenRatio + 1) ^ 2 := by
      rw [Real.goldenRatio_sq]
    _ = 3 * Real.goldenRatio + 2 := by
      nlinarith [Real.goldenRatio_sq]

private theorem golden_fourth_mixed :
    Real.goldenRatio ^ 4 =
      Real.goldenRatio ^ 2 + Real.goldenRatio ^ 3 := by
  rw [golden_cube, golden_fourth, Real.goldenRatio_sq]
  ring

private theorem golden_fifth :
    Real.goldenRatio ^ 5 =
      Real.goldenRatio ^ 2 + 2 * Real.goldenRatio ^ 3 := by
  rw [show Real.goldenRatio ^ 5 =
      Real.goldenRatio ^ 3 * Real.goldenRatio ^ 2 by ring,
    golden_cube, Real.goldenRatio_sq]
  nlinarith [Real.goldenRatio_sq]

private theorem o5_beta_four :
    o5Beta 4 = 2 * Real.goldenRatio ^ 2 + Real.goldenRatio ^ 3 := by
  rw [o5Beta]
  norm_num
  rw [floor_five_mul_goldenRatio, golden_cube]
  norm_num
  nlinarith [Real.goldenRatio_sq]

private theorem o5_beta_five :
    o5Beta 5 = Real.goldenRatio ^ 5 := by
  rw [o5Beta]
  norm_num
  rw [floor_six_mul_goldenRatio]
  rw [show Real.goldenRatio ^ 5 = 5 * Real.goldenRatio + 3 by
    rw [golden_fifth, golden_cube, Real.goldenRatio_sq]
    ring]
  ring

private theorem o5_beta_six :
    o5Beta 6 = 2 * Real.goldenRatio ^ 4 :=
  golden_germ_fourth_order_exponent_census.1

private theorem o5_beta_six_pos : 0 < o5Beta 6 := by
  rw [o5_beta_six]
  positivity

private theorem positive_of_beta_six_reciprocal_lt {sigma : Real}
    (hsigma : 1 / o5Beta 6 < sigma) : 0 < sigma :=
  (one_div_pos.mpr o5_beta_six_pos).trans hsigma

private theorem one_tenth_in_fourth_order_domain :
    1 / o5Beta 6 < (1 : Real) / 10 := by
  have hten : (10 : Real) < o5Beta 6 := by
    rw [o5_beta_six, golden_fourth]
    nlinarith [goldenRatio_gt_eight_fifths]
  exact one_div_lt_one_div_of_lt (by norm_num) hten

private theorem o5_beta_seven_add_ge (k : Nat) :
    o5Beta 6 + (k : Real) <= o5Beta (k + 7) := by
  have hsqrt_sq : Real.sqrt 5 ^ 2 = (5 : Real) :=
    Real.sq_sqrt (by norm_num)
  have hsqrt_nonneg : 0 <= Real.sqrt 5 := Real.sqrt_nonneg 5
  have hsqrt_two : 2 < Real.sqrt 5 := by nlinarith
  have hphi_inv : 1 / Real.goldenRatio = Real.goldenRatio - 1 := by
    rw [one_div, Real.inv_goldenRatio]
    linarith [Real.goldenRatio_add_goldenConj]
  apply le_trans _ (o5_beta_growth (k + 7))
  rw [o5_beta_six, golden_fourth, hphi_inv]
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
    (hs : 1 / o5Beta 6 < s.re) (a b : Nat)
    (hweight : o5Beta 6 <=
      (a : Real) * Real.goldenRatio ^ 2 +
        (b : Real) * Real.goldenRatio ^ 3) :
    Summable (fun p : Nat.Primes =>
      norm (((p : Complex) ^
          (-s * ((Real.goldenRatio ^ 2 : Real) : Complex))) ^ a *
        ((p : Complex) ^
          (-s * ((Real.goldenRatio ^ 3 : Real) : Complex))) ^ b)) := by
  let weight : Real :=
    (a : Real) * Real.goldenRatio ^ 2 +
      (b : Real) * Real.goldenRatio ^ 3
  have hspos : 0 < s.re := positive_of_beta_six_reciprocal_lt hs
  have hcritical : 1 < s.re * o5Beta 6 :=
    (div_lt_iff₀ o5_beta_six_pos).mp
      (by simpa [div_eq_mul_inv] using hs)
  have hscaled : s.re * o5Beta 6 <= s.re * weight :=
    mul_le_mul_of_nonneg_left (by simpa [weight] using hweight) hspos.le
  have hexponent : -s.re * weight < -1 := by linarith
  refine (Nat.Primes.summable_rpow.mpr hexponent).congr fun p => ?_
  rw [← mixed_mode_cpow s p a b]
  rw [Complex.norm_natCast_cpow_of_pos p.prop.pos]
  simp only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero]
  simp only [weight]

private theorem mixed_mode_norm_le_one (s : Complex)
    (hs : 1 / o5Beta 6 < s.re) (p : Nat.Primes) (a b : Nat)
    (hweight : 0 < (a : Real) * Real.goldenRatio ^ 2 +
      (b : Real) * Real.goldenRatio ^ 3) :
    norm (((p : Complex) ^
        (-s * ((Real.goldenRatio ^ 2 : Real) : Complex))) ^ a *
      ((p : Complex) ^
        (-s * ((Real.goldenRatio ^ 3 : Real) : Complex))) ^ b) <= 1 := by
  have hspos : 0 < s.re := positive_of_beta_six_reciprocal_lt hs
  rw [← mixed_mode_cpow s p a b]
  rw [Complex.norm_natCast_cpow_of_pos p.prop.pos]
  simp only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero]
  exact Real.rpow_le_one_of_one_le_of_nonpos
    (by exact_mod_cast p.prop.one_le) (by nlinarith)

private theorem mixed_mode_norm_lt_one (s : Complex)
    (hs : 1 / o5Beta 6 < s.re) (p : Nat.Primes) (a b : Nat)
    (hweight : 0 < (a : Real) * Real.goldenRatio ^ 2 +
      (b : Real) * Real.goldenRatio ^ 3) :
    norm (((p : Complex) ^
        (-s * ((Real.goldenRatio ^ 2 : Real) : Complex))) ^ a *
      ((p : Complex) ^
        (-s * ((Real.goldenRatio ^ 3 : Real) : Complex))) ^ b) < 1 := by
  have hspos : 0 < s.re := positive_of_beta_six_reciprocal_lt hs
  rw [← mixed_mode_cpow s p a b]
  rw [Complex.norm_natCast_cpow_of_pos p.prop.pos]
  simp only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero]
  exact Real.rpow_lt_one_of_one_lt_of_neg
    (by exact_mod_cast p.prop.one_lt) (by nlinarith)

private theorem mixed_mode_norm_le_two (s : Complex)
    (hs : 1 / o5Beta 6 < s.re) (p : Nat.Primes) (a b : Nat)
    (hweight : 0 <= (a : Real) * Real.goldenRatio ^ 2 +
      (b : Real) * Real.goldenRatio ^ 3) :
    norm (((p : Complex) ^
        (-s * ((Real.goldenRatio ^ 2 : Real) : Complex))) ^ a *
      ((p : Complex) ^
        (-s * ((Real.goldenRatio ^ 3 : Real) : Complex))) ^ b) <=
      (2 : Real) ^
        (-s.re * ((a : Real) * Real.goldenRatio ^ 2 +
          (b : Real) * Real.goldenRatio ^ 3)) := by
  have hspos : 0 < s.re := positive_of_beta_six_reciprocal_lt hs
  rw [← mixed_mode_cpow s p a b]
  rw [Complex.norm_natCast_cpow_of_pos p.prop.pos]
  simp only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero]
  exact Real.rpow_le_rpow_of_nonpos (by norm_num)
    (by exact_mod_cast p.prop.two_le) (by nlinarith)

private theorem seventh_tail_real_summable (sigma : Real)
    (hsigma : 1 / o5Beta 6 < sigma) :
    Summable (fun q : Nat.Primes × Nat =>
      (q.1 : Real) ^ (-sigma * o5Beta (q.2 + 7))) := by
  have hcritical : 1 < sigma * o5Beta 6 :=
    (div_lt_iff₀ o5_beta_six_pos).mp
      (by simpa [div_eq_mul_inv] using hsigma)
  have hsigma_pos : 0 < sigma := positive_of_beta_six_reciprocal_lt hsigma
  let r : Real := -sigma * o5Beta 6
  let q : Real := (2 : Real) ^ (-sigma)
  have hr : r < -1 := by dsimp [r]; linarith
  have hq_nonneg : 0 <= q := by dsimp [q]; positivity
  have hq_lt_one : q < 1 := by
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num)
      (neg_neg_of_pos hsigma_pos)
  have hbase : Summable (fun p : Nat.Primes => (p : Real) ^ r) :=
    Nat.Primes.summable_rpow.mpr hr
  have hslice (k : Nat) : Summable (fun p : Nat.Primes =>
      (p : Real) ^ (-sigma * o5Beta (k + 7))) := by
    apply Nat.Primes.summable_rpow.mpr
    have hbeta := o5_beta_seven_add_ge k
    nlinarith
  have hterm (k : Nat) (p : Nat.Primes) :
      (p : Real) ^ (-sigma * o5Beta (k + 7)) <=
        (p : Real) ^ r * q ^ k := by
    have hp_one : 1 <= (p : Real) := by
      exact_mod_cast p.prop.one_lt.le
    have hp_two : (2 : Real) <= (p : Real) := by
      exact_mod_cast p.prop.two_le
    have hbeta := o5_beta_seven_add_ge k
    have hk : 0 <= (k : Real) := by positivity
    calc
      (p : Real) ^ (-sigma * o5Beta (k + 7)) <=
          (p : Real) ^ (-sigma * (o5Beta 6 + (k : Real))) :=
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
          (p : Real) ^ (-sigma * o5Beta (k + 7))) <=
        (∑' p : Nat.Primes, (p : Real) ^ r) * q ^ k := by
    calc
      (∑' p : Nat.Primes,
          (p : Real) ^ (-sigma * o5Beta (k + 7))) <=
          ∑' p : Nat.Primes, (p : Real) ^ r * q ^ k :=
        (hslice k).tsum_le_tsum (hterm k) (hbase.mul_right (q ^ k))
      _ = (∑' p : Nat.Primes, (p : Real) ^ r) * q ^ k :=
        tsum_mul_right
  have houter : Summable (fun k : Nat =>
      ∑' p : Nat.Primes,
        (p : Real) ^ (-sigma * o5Beta (k + 7))) :=
    ((summable_geometric_of_lt_one hq_nonneg hq_lt_one).mul_left
      (∑' p : Nat.Primes, (p : Real) ^ r)).of_nonneg_of_le
        (fun _ => by positivity) htsum
  have hswapped : Summable (fun kp : Nat × Nat.Primes =>
      (kp.2 : Real) ^ (-sigma * o5Beta (kp.1 + 7))) :=
    (summable_prod_of_nonneg (fun _ => by positivity)).mpr
      ⟨hslice, houter⟩
  exact (Equiv.prodComm Nat.Primes Nat).summable_iff.mpr hswapped

private theorem seventh_tail_norm_summable (s : Complex)
    (hs : 1 / o5Beta 6 < s.re) :
    Summable (fun q : Nat.Primes × Nat =>
      norm ((q.1 : Complex) ^
        (-s * (o5Beta (q.2 + 7) : Complex)))) := by
  refine (seventh_tail_real_summable s.re hs).congr fun q => ?_
  rw [Complex.norm_natCast_cpow_of_pos q.1.prop.pos]
  simp only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero]

private theorem local_factor_eq_seven_modes_and_tail (s : Complex)
    (hs : 1 / o5Beta 6 < s.re) (p : Nat.Primes) :
    let x := (p : Complex) ^
      (-s * ((Real.goldenRatio ^ 2 : Real) : Complex))
    let y := (p : Complex) ^
      (-s * ((Real.goldenRatio ^ 3 : Real) : Complex))
    let tail := ∑' k : Nat,
      (p : Complex) ^ (-s * (o5Beta (k + 7) : Complex))
    germLocalFactor s p =
      1 + x + y + x * y + x ^ 2 * y + x * y ^ 2 +
        x ^ 2 * y ^ 2 + tail := by
  dsimp only
  let x : Complex := (p : Complex) ^
    (-s * ((Real.goldenRatio ^ 2 : Real) : Complex))
  let y : Complex := (p : Complex) ^
    (-s * ((Real.goldenRatio ^ 3 : Real) : Complex))
  let f : Nat -> Complex := fun v =>
    (p : Complex) ^ (-s * (o5Beta v : Complex))
  have htail : Summable (fun k : Nat => f (k + 7)) := by
    exact ((seventh_tail_norm_summable s hs).prod_factor p).of_norm
  have hall : Summable f := (summable_nat_add_iff 7).1 (by
    simpa [f, Nat.add_comm] using htail)
  have hf0 : f 0 = 1 := by simp [f, o5_beta_zero]
  have hf1 : f 1 = x := by
    simp only [f, o5_beta_power_law.1]
    rfl
  have hf2 : f 2 = y := by
    simp only [f, o5_beta_power_law.2.1]
    rfl
  have hf3 : f 3 = x * y := by
    simp only [f, o5_beta_power_law.2.2]
    rw [golden_fourth_mixed]
    simpa [x, y] using mixed_mode_cpow s p 1 1
  have hf4 : f 4 = x ^ 2 * y := by
    simp only [f, o5_beta_four]
    simpa [x, y] using mixed_mode_cpow s p 2 1
  have hf5 : f 5 = x * y ^ 2 := by
    simp only [f, o5_beta_five]
    rw [golden_fifth]
    simpa [x, y] using mixed_mode_cpow s p 1 2
  have hf6 : f 6 = x ^ 2 * y ^ 2 := by
    simp only [f, o5_beta_six]
    rw [show 2 * Real.goldenRatio ^ 4 =
        2 * Real.goldenRatio ^ 2 + 2 * Real.goldenRatio ^ 3 by
      rw [golden_fourth_mixed]
      ring]
    simpa [x, y] using mixed_mode_cpow s p 2 2
  have hprefix : (∑ v ∈ Finset.range 7, f v) =
      1 + x + y + x * y + x ^ 2 * y + x * y ^ 2 +
        x ^ 2 * y ^ 2 := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero,
      hf0, hf1, hf2, hf3, hf4, hf5, hf6, zero_add]
  rw [germLocalFactor, show (fun v : Nat =>
      (p : Complex) ^ (-s * (o5Beta v : Complex))) = f from rfl,
    ← hall.sum_add_tsum_nat_add 7, hprefix]

private theorem one_sub_ne_zero_of_norm_lt_one {z : Complex}
    (hz : norm z < 1) : 1 - z ≠ 0 := by
  rw [sub_ne_zero]
  intro h
  rw [← h, norm_one] at hz
  exact lt_irrefl 1 hz

private theorem inverse_one_sub_norm_le {z : Complex} {q : Real}
    (hq : q < 1) (hz : norm z <= q) :
    norm ((1 - z)⁻¹) <= 1 / (1 - q) := by
  have hlower : 1 - q <= norm (1 - z) := by
    calc
      1 - q <= 1 - norm z := sub_le_sub_left hz 1
      _ = norm (1 : Complex) - norm z := by simp
      _ <= norm ((1 : Complex) - z) := norm_sub_norm_le _ _
  rw [norm_inv]
  simpa [one_div] using
    one_div_le_one_div_of_le (sub_pos.mpr hq) hlower

private theorem fourth_remainder_weight_certificate :
    forall a b : Nat,
      (a, b) ∈ [(5, 6), (5, 4), (4, 6), (4, 4), (4, 2), (4, 1),
        (3, 4), (3, 3), (2, 5), (2, 2), (1, 4), (1, 3)] ->
      o5Beta 6 <= (a : Real) * Real.goldenRatio ^ 2 +
        (b : Real) * Real.goldenRatio ^ 3 := by
  intro a b hab
  simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hab
  rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ <;>
    rw [o5_beta_six, golden_fourth, golden_cube,
      Real.goldenRatio_sq] <;>
    norm_num <;> nlinarith [Real.one_lt_goldenRatio]

private theorem fourth_correction_weights :
    (1 : Real) * Real.goldenRatio ^ 2 +
        (2 : Real) * Real.goldenRatio ^ 3 < o5Beta 6 ∧
      (3 : Real) * Real.goldenRatio ^ 2 +
        (1 : Real) * Real.goldenRatio ^ 3 < o5Beta 6 := by
  rw [o5_beta_six, golden_fourth, golden_cube,
    Real.goldenRatio_sq]
  constructor <;> norm_num <;> nlinarith [Real.goldenRatio_pos]

private theorem fourth_local_identity (s : Complex)
    (hs : 1 / o5Beta 6 < s.re) (p : Nat.Primes) :
    let x := (p : Complex) ^
      (-s * ((Real.goldenRatio ^ 2 : Real) : Complex))
    let y := (p : Complex) ^
      (-s * ((Real.goldenRatio ^ 3 : Real) : Complex))
    let tail := ∑' k : Nat,
      (p : Complex) ^ (-s * (o5Beta (k + 7) : Complex))
    let K3 := (1 - y ^ 2)⁻¹ * (1 - x ^ 2 * y) *
      (1 - y) * (1 + x)⁻¹ * germLocalFactor s p
    let C4 := (1 - x * y ^ 2) * (1 - x ^ 3 * y)⁻¹
    let H4 :=
      -(x ^ 5 * y ^ 6) + x ^ 5 * y ^ 4 - x ^ 4 * y ^ 6 +
        x ^ 4 * y ^ 4 - x ^ 4 * y ^ 2 + x ^ 4 * y +
        x ^ 3 * y ^ 4 - x ^ 3 * y ^ 3 + x ^ 2 * y ^ 5 -
        x ^ 2 * y ^ 2 + x * y ^ 4 - x * y ^ 3
    let R4 := (1 - x ^ 3 * y)⁻¹ * (1 - y ^ 2)⁻¹ * (1 + x)⁻¹ *
      (H4 + (1 - x * y ^ 2) * (1 - x ^ 2 * y) * (1 - y) * tail)
    C4 * K3 = 1 + R4 := by
  dsimp only
  let x : Complex := (p : Complex) ^
    (-s * ((Real.goldenRatio ^ 2 : Real) : Complex))
  let y : Complex := (p : Complex) ^
    (-s * ((Real.goldenRatio ^ 3 : Real) : Complex))
  let tail : Complex := ∑' k : Nat,
    (p : Complex) ^ (-s * (o5Beta (k + 7) : Complex))
  change
    (1 - x * y ^ 2) * (1 - x ^ 3 * y)⁻¹ *
        ((1 - y ^ 2)⁻¹ * (1 - x ^ 2 * y) *
          (1 - y) * (1 + x)⁻¹ * germLocalFactor s p) =
      1 + (1 - x ^ 3 * y)⁻¹ * (1 - y ^ 2)⁻¹ * (1 + x)⁻¹ *
        (-(x ^ 5 * y ^ 6) + x ^ 5 * y ^ 4 - x ^ 4 * y ^ 6 +
          x ^ 4 * y ^ 4 - x ^ 4 * y ^ 2 + x ^ 4 * y +
          x ^ 3 * y ^ 4 - x ^ 3 * y ^ 3 + x ^ 2 * y ^ 5 -
          x ^ 2 * y ^ 2 + x * y ^ 4 - x * y ^ 3 +
          (1 - x * y ^ 2) * (1 - x ^ 2 * y) * (1 - y) * tail)
  have hxlt : norm x < 1 := by
    simpa [x] using mixed_mode_norm_lt_one s hs p 1 0 (by positivity)
  have hylt : norm (y ^ 2) < 1 := by
    simpa [x, y] using mixed_mode_norm_lt_one s hs p 0 2 (by positivity)
  have hwlt : norm (x ^ 3 * y) < 1 := by
    simpa [x, y] using mixed_mode_norm_lt_one s hs p 3 1 (by positivity)
  have hx : 1 + x ≠ 0 := by
    simpa [sub_neg_eq_add] using
      one_sub_ne_zero_of_norm_lt_one (z := -x) (by simpa using hxlt)
  have hy : 1 - y ^ 2 ≠ 0 :=
    one_sub_ne_zero_of_norm_lt_one hylt
  have hw : 1 - x ^ 3 * y ≠ 0 :=
    one_sub_ne_zero_of_norm_lt_one hwlt
  have hlocal : germLocalFactor s p =
      1 + x + y + x * y + x ^ 2 * y + x * y ^ 2 +
        x ^ 2 * y ^ 2 + tail := by
    simpa [x, y, tail] using local_factor_eq_seven_modes_and_tail s hs p
  rw [hlocal]
  field_simp [hx, hy, hw]
  ring

/-- The finite fourth-order correction is
`(1 - x*y^2) * (1 - x^3*y)^(-1)`.  Multiplying it by the frozen third-order
local factor gives `1 + R4` exactly.  The displayed finite numerator support,
the shifted tail, and every nonnegative denominator expansion lie at or above
`beta6`; consequently the corrected deviations are norm-summable on
`Re s > 1 / beta6`.  This is a finite local certificate only. -/
theorem golden_fourth_normalized_factor_deviation_norm_summable
    (s : Complex) (hs : 1 / o5Beta 6 < s.re) :
    let x : Nat.Primes -> Complex := fun p =>
      (p : Complex) ^ (-s * ((Real.goldenRatio ^ 2 : Real) : Complex))
    let y : Nat.Primes -> Complex := fun p =>
      (p : Complex) ^ (-s * ((Real.goldenRatio ^ 3 : Real) : Complex))
    let tail : Nat.Primes -> Complex := fun p => ∑' k : Nat,
      (p : Complex) ^ (-s * (o5Beta (k + 7) : Complex))
    let K3 : Nat.Primes -> Complex := fun p =>
      (1 - y p ^ 2)⁻¹ * (1 - x p ^ 2 * y p) *
        (1 - y p) * (1 + x p)⁻¹ * germLocalFactor s p
    let C4 : Nat.Primes -> Complex := fun p =>
      (1 - x p * y p ^ 2) * (1 - x p ^ 3 * y p)⁻¹
    let H4 : Nat.Primes -> Complex := fun p =>
      -(x p ^ 5 * y p ^ 6) + x p ^ 5 * y p ^ 4 -
        x p ^ 4 * y p ^ 6 + x p ^ 4 * y p ^ 4 -
        x p ^ 4 * y p ^ 2 + x p ^ 4 * y p +
        x p ^ 3 * y p ^ 4 - x p ^ 3 * y p ^ 3 +
        x p ^ 2 * y p ^ 5 - x p ^ 2 * y p ^ 2 +
        x p * y p ^ 4 - x p * y p ^ 3
    let R4 : Nat.Primes -> Complex := fun p =>
      (1 - x p ^ 3 * y p)⁻¹ * (1 - y p ^ 2)⁻¹ * (1 + x p)⁻¹ *
        (H4 p + (1 - x p * y p ^ 2) * (1 - x p ^ 2 * y p) *
          (1 - y p) * tail p)
    (1 / Real.goldenRatio ^ 5 < s.re ->
      Summable (fun p : Nat.Primes => norm (K3 p - 1))) ∧
    ((1 : Real) * Real.goldenRatio ^ 2 +
        (2 : Real) * Real.goldenRatio ^ 3 < o5Beta 6 ∧
      (3 : Real) * Real.goldenRatio ^ 2 +
        (1 : Real) * Real.goldenRatio ^ 3 < o5Beta 6) ∧
    (forall a b : Nat,
      (a, b) ∈ [(5, 6), (5, 4), (4, 6), (4, 4), (4, 2), (4, 1),
        (3, 4), (3, 3), (2, 5), (2, 2), (1, 4), (1, 3)] ->
      o5Beta 6 <= (a : Real) * Real.goldenRatio ^ 2 +
        (b : Real) * Real.goldenRatio ^ 3) ∧
    (forall k i j l m n r : Nat,
      o5Beta 6 <= o5Beta (k + 7) +
        (i : Real) * (Real.goldenRatio ^ 2 + 2 * Real.goldenRatio ^ 3) +
        (j : Real) * (2 * Real.goldenRatio ^ 2 + Real.goldenRatio ^ 3) +
        (l : Real) * Real.goldenRatio ^ 3 +
        (m : Real) * (3 * Real.goldenRatio ^ 2 + Real.goldenRatio ^ 3) +
        (n : Real) * (2 * Real.goldenRatio ^ 3) +
        (r : Real) * Real.goldenRatio ^ 2) ∧
    (forall p : Nat.Primes, C4 p * K3 p = 1 + R4 p) ∧
    Summable (fun p : Nat.Primes => norm (C4 p * K3 p - 1)) ∧
    1 / o5Beta 6 < (1 : Real) / 10 := by
  fail_if_success rfl
  fail_if_success (solve | simp)
  fail_if_success (solve | trivial)
  dsimp only
  let x : Nat.Primes -> Complex := fun p =>
    (p : Complex) ^ (-s * ((Real.goldenRatio ^ 2 : Real) : Complex))
  let y : Nat.Primes -> Complex := fun p =>
    (p : Complex) ^ (-s * ((Real.goldenRatio ^ 3 : Real) : Complex))
  let tail : Nat.Primes -> Complex := fun p => ∑' k : Nat,
    (p : Complex) ^ (-s * (o5Beta (k + 7) : Complex))
  let K3 : Nat.Primes -> Complex := fun p =>
    (1 - y p ^ 2)⁻¹ * (1 - x p ^ 2 * y p) *
      (1 - y p) * (1 + x p)⁻¹ * germLocalFactor s p
  let C4 : Nat.Primes -> Complex := fun p =>
    (1 - x p * y p ^ 2) * (1 - x p ^ 3 * y p)⁻¹
  let H4 : Nat.Primes -> Complex := fun p =>
    -(x p ^ 5 * y p ^ 6) + x p ^ 5 * y p ^ 4 -
      x p ^ 4 * y p ^ 6 + x p ^ 4 * y p ^ 4 -
      x p ^ 4 * y p ^ 2 + x p ^ 4 * y p +
      x p ^ 3 * y p ^ 4 - x p ^ 3 * y p ^ 3 +
      x p ^ 2 * y p ^ 5 - x p ^ 2 * y p ^ 2 +
      x p * y p ^ 4 - x p * y p ^ 3
  let R4 : Nat.Primes -> Complex := fun p =>
    (1 - x p ^ 3 * y p)⁻¹ * (1 - y p ^ 2)⁻¹ * (1 + x p)⁻¹ *
      (H4 p + (1 - x p * y p ^ 2) * (1 - x p ^ 2 * y p) *
        (1 - y p) * tail p)
  change
    (1 / Real.goldenRatio ^ 5 < s.re ->
      Summable (fun p : Nat.Primes => norm (K3 p - 1))) ∧ _
  constructor
  · intro hs5
    have hthird := golden_germ_third_order_factorization
    dsimp only at hthird
    simpa [x, y, K3] using hthird.1 s hs5
  constructor
  · exact fourth_correction_weights
  constructor
  · exact fourth_remainder_weight_certificate
  constructor
  · intro k i j l m n r
    have hk := o5_beta_seven_add_ge k
    have hi : 0 <= (i : Real) := by positivity
    have hj : 0 <= (j : Real) := by positivity
    have hl : 0 <= (l : Real) := by positivity
    have hm : 0 <= (m : Real) := by positivity
    have hn : 0 <= (n : Real) := by positivity
    have hr : 0 <= (r : Real) := by positivity
    have hphi2 : 0 < Real.goldenRatio ^ 2 := by positivity
    have hphi3 : 0 < Real.goldenRatio ^ 3 := by positivity
    nlinarith
  have hidentity (p : Nat.Primes) : C4 p * K3 p = 1 + R4 p := by
    simpa [x, y, tail, K3, C4, H4, R4] using
      fourth_local_identity s hs p
  constructor
  · exact hidentity
  have hweights := fourth_remainder_weight_certificate
  have hmonoNorm (a b : Nat)
      (hab : (a, b) ∈
        [(5, 6), (5, 4), (4, 6), (4, 4), (4, 2), (4, 1),
          (3, 4), (3, 3), (2, 5), (2, 2), (1, 4), (1, 3)]) :
      Summable (fun p : Nat.Primes => norm (x p ^ a * y p ^ b)) := by
    simpa [x, y] using mixed_mode_norm_summable s hs a b
      (hweights a b hab)
  have hm56 := (hmonoNorm 5 6 (by simp)).of_norm
  have hm54 := (hmonoNorm 5 4 (by simp)).of_norm
  have hm46 := (hmonoNorm 4 6 (by simp)).of_norm
  have hm44 := (hmonoNorm 4 4 (by simp)).of_norm
  have hm42 := (hmonoNorm 4 2 (by simp)).of_norm
  have hm41 := (hmonoNorm 4 1 (by simp)).of_norm
  have hm34 := (hmonoNorm 3 4 (by simp)).of_norm
  have hm33 := (hmonoNorm 3 3 (by simp)).of_norm
  have hm25 := (hmonoNorm 2 5 (by simp)).of_norm
  have hm22 := (hmonoNorm 2 2 (by simp)).of_norm
  have hm14 := (hmonoNorm 1 4 (by simp)).of_norm
  have hm13 := (hmonoNorm 1 3 (by simp)).of_norm
  have hp1 := hm56.neg.add hm54
  have hp2 := hp1.sub hm46
  have hp3 := hp2.add hm44
  have hp4 := hp3.sub hm42
  have hp5 := hp4.add hm41
  have hp6 := hp5.add hm34
  have hp7 := hp6.sub hm33
  have hp8 := hp7.add hm25
  have hp9 := hp8.sub hm22
  have hp10 := hp9.add hm14
  have hp11 := hp10.sub hm13
  have hpoly : Summable H4 := by
    simpa only [H4, pow_one] using hp11
  have htailJoint := seventh_tail_norm_summable s hs
  have htailNorm : Summable (fun p : Nat.Primes => norm (tail p)) := by
    refine htailJoint.prod.of_nonneg_of_le (fun _ => norm_nonneg _) fun p => ?_
    exact norm_tsum_le_tsum_norm (by
      simpa [tail] using htailJoint.prod_factor p)
  have huNorm (p : Nat.Primes) : norm (x p * y p ^ 2) <= 1 := by
    simpa [x, y] using mixed_mode_norm_le_one s hs p 1 2 (by positivity)
  have haNorm (p : Nat.Primes) : norm (x p ^ 2 * y p) <= 1 := by
    simpa [x, y] using mixed_mode_norm_le_one s hs p 2 1 (by positivity)
  have hyNorm (p : Nat.Primes) : norm (y p) <= 1 := by
    simpa [x, y] using mixed_mode_norm_le_one s hs p 0 1 (by positivity)
  have htailProduct : Summable (fun p : Nat.Primes =>
      (1 - x p * y p ^ 2) * (1 - x p ^ 2 * y p) *
        (1 - y p) * tail p) := by
    refine (htailNorm.mul_left 8).of_norm_bounded fun p => ?_
    have huMinus : norm (1 - x p * y p ^ 2) <= 2 := by
      calc
        norm (1 - x p * y p ^ 2) <=
            norm (1 : Complex) + norm (x p * y p ^ 2) := norm_sub_le _ _
        _ <= 1 + 1 := add_le_add (by norm_num) (huNorm p)
        _ = 2 := by norm_num
    have haMinus : norm (1 - x p ^ 2 * y p) <= 2 := by
      calc
        norm (1 - x p ^ 2 * y p) <=
            norm (1 : Complex) + norm (x p ^ 2 * y p) := norm_sub_le _ _
        _ <= 1 + 1 := add_le_add (by norm_num) (haNorm p)
        _ = 2 := by norm_num
    have hyMinus : norm (1 - y p) <= 2 := by
      calc
        norm (1 - y p) <=
            norm (1 : Complex) + norm (y p) := norm_sub_le _ _
        _ <= 1 + 1 := add_le_add (by norm_num) (hyNorm p)
        _ = 2 := by norm_num
    have hfirst :
        norm ((1 - x p * y p ^ 2) * (1 - x p ^ 2 * y p)) <= 4 := by
      calc
        norm ((1 - x p * y p ^ 2) * (1 - x p ^ 2 * y p)) =
            norm (1 - x p * y p ^ 2) * norm (1 - x p ^ 2 * y p) :=
          norm_mul _ _
        _ <= 2 * 2 :=
          mul_le_mul huMinus haMinus (norm_nonneg _) (by norm_num)
        _ = 4 := by norm_num
    have hthree : norm ((1 - x p * y p ^ 2) *
        (1 - x p ^ 2 * y p) * (1 - y p)) <= 8 := by
      calc
        norm ((1 - x p * y p ^ 2) * (1 - x p ^ 2 * y p) *
            (1 - y p)) =
            norm ((1 - x p * y p ^ 2) * (1 - x p ^ 2 * y p)) *
              norm (1 - y p) := norm_mul _ _
        _ <= 4 * 2 :=
          mul_le_mul hfirst hyMinus (norm_nonneg _) (by norm_num)
        _ = 8 := by norm_num
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right hthree (norm_nonneg _)
  have hnum : Summable (fun p : Nat.Primes =>
      H4 p + (1 - x p * y p ^ 2) * (1 - x p ^ 2 * y p) *
        (1 - y p) * tail p) := hpoly.add htailProduct
  have hnumNorm := hnum.norm
  let qx : Real := (2 : Real) ^ (-s.re * Real.goldenRatio ^ 2)
  let qy : Real := (2 : Real) ^ (-s.re * (2 * Real.goldenRatio ^ 3))
  let qw : Real := (2 : Real) ^
    (-s.re * (3 * Real.goldenRatio ^ 2 + Real.goldenRatio ^ 3))
  let Cx : Real := 1 / (1 - qx)
  let Cy : Real := 1 / (1 - qy)
  let Cw : Real := 1 / (1 - qw)
  have hspos : 0 < s.re := positive_of_beta_six_reciprocal_lt hs
  have hqxlt : qx < 1 := by
    dsimp [qx]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num)
      (mul_neg_of_neg_of_pos (neg_neg_of_pos hspos) (by positivity))
  have hqylt : qy < 1 := by
    dsimp [qy]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num)
      (mul_neg_of_neg_of_pos (neg_neg_of_pos hspos) (by positivity))
  have hqwlt : qw < 1 := by
    dsimp [qw]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num)
      (mul_neg_of_neg_of_pos (neg_neg_of_pos hspos) (by positivity))
  have hCx : 0 <= Cx := by dsimp [Cx]; positivity
  have hCy : 0 <= Cy := by dsimp [Cy]; positivity
  have hCw : 0 <= Cw := by dsimp [Cw]; positivity
  have hxInv (p : Nat.Primes) : norm ((1 + x p)⁻¹) <= Cx := by
    have hxq : norm (x p) <= qx := by
      simpa [x, qx] using mixed_mode_norm_le_two s hs p 1 0 (by positivity)
    simpa [Cx, sub_neg_eq_add] using
      inverse_one_sub_norm_le (z := -x p) hqxlt (by simpa using hxq)
  have hyInv (p : Nat.Primes) : norm ((1 - y p ^ 2)⁻¹) <= Cy := by
    have hyq : norm (y p ^ 2) <= qy := by
      simpa [x, y, qy] using
        mixed_mode_norm_le_two s hs p 0 2 (by positivity)
    simpa [Cy] using inverse_one_sub_norm_le hqylt hyq
  have hwInv (p : Nat.Primes) : norm ((1 - x p ^ 3 * y p)⁻¹) <= Cw := by
    have hwq : norm (x p ^ 3 * y p) <= qw := by
      simpa [x, y, qw] using
        mixed_mode_norm_le_two s hs p 3 1 (by positivity)
    simpa [Cw] using inverse_one_sub_norm_le hqwlt hwq
  have hRNorm : Summable (fun p : Nat.Primes => norm (R4 p)) := by
    refine (hnumNorm.mul_left (Cw * Cy * Cx)).of_nonneg_of_le
      (fun _ => norm_nonneg _) fun p => ?_
    have hwy : norm ((1 - x p ^ 3 * y p)⁻¹ * (1 - y p ^ 2)⁻¹) <=
        Cw * Cy := by
      rw [norm_mul]
      exact mul_le_mul (hwInv p) (hyInv p) (norm_nonneg _) hCw
    have hwyx : norm ((1 - x p ^ 3 * y p)⁻¹ * (1 - y p ^ 2)⁻¹ *
        (1 + x p)⁻¹) <= Cw * Cy * Cx := by
      rw [norm_mul]
      exact mul_le_mul hwy (hxInv p) (norm_nonneg _) (mul_nonneg hCw hCy)
    dsimp [R4]
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right hwyx (norm_nonneg _)
  constructor
  · refine hRNorm.congr fun p => ?_
    rw [hidentity p, add_sub_cancel_left]
  · exact one_tenth_in_fourth_order_domain

#print axioms golden_fourth_normalized_factor_deviation_norm_summable

end

end D5.S3.Analytic.EulerGerm.GoldenGermFourthOrderLedger
