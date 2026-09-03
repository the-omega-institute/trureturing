/- GID: D5/S3/Analytic/Regularity/GoldenGermThirdNormalizedFactorMajorant
   generality: I
   mirror-B: D5/B/S3/Analytic/Regularity/GoldenGermThirdNormalizedFactorMajorant
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The third normalized golden germ has a locally uniform prime majorant. -/
import D5.S3.Analytic.EulerGerm.GoldenGermThirdOrderFactorization
import D5.S3.Analytic.EulerGerm.GermProductBound
import D5.S3.Analytic.EulerGerm.LocalFactorZeroDivisor
/- Library-search audit trail (2026-09-03):
   Repository search found the frozen pointwise third-order deviation theorem
   but no locally uniform majorant. Pinned Mathlib supplies the locally uniform
   product M-test and the complex-power, rpow, tsum, and differentiability API. -/
namespace D5.S3.Analytic.Regularity.GoldenGermThirdNormalizedFactorMajorant
set_option autoImplicit false
set_option relaxedAutoImplicit false
open D5.S3.Analytic.GoldenEulerBeta
open D5.S3.Analytic.EulerGerm.GoldenLocalFactor
open D5.S3.Analytic.EulerGerm.GoldenGermThirdOrderFactorization
open D5.S3.Analytic.EulerGerm.GoldenGermThirdOrderLedger
open D5.S3.Analytic.EulerGerm.LocalFactorZeroDivisor
noncomputable section
private theorem prime_real_pos (p : Nat.Primes) : 0 < (p : Real) := by
  exact_mod_cast p.prop.pos
private theorem o5_beta_six_add_ge (k : Nat) :
    Real.goldenRatio ^ 5 + (k : Real) <= o5Beta (k + 6) := by
  have hsqrt_sq : Real.sqrt 5 ^ 2 = (5 : Real) :=
    Real.sq_sqrt (by norm_num)
  have hsqrt_nonneg : 0 <= Real.sqrt 5 := Real.sqrt_nonneg 5
  have hsqrt_two : 2 < Real.sqrt 5 := by nlinarith
  have hphi_inv : 1 / Real.goldenRatio = Real.goldenRatio - 1 := by
    rw [one_div, Real.inv_goldenRatio]
    linarith [Real.goldenRatio_add_goldenConj]
  have hfifth : Real.goldenRatio ^ 5 = 3 + 5 * Real.goldenRatio := by
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
    (p : Complex) ^ (-s * ((((a : Real) * Real.goldenRatio ^ 2 +
      (b : Real) * Real.goldenRatio ^ 3) : Real) : Complex)) =
    ((p : Complex) ^ (-s * ((Real.goldenRatio ^ 2 : Real) : Complex))) ^ a *
    ((p : Complex) ^ (-s * ((Real.goldenRatio ^ 3 : Real) : Complex))) ^ b := by
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
    (hweight : Real.goldenRatio ^ 5 <= (a : Real) * Real.goldenRatio ^ 2 +
      (b : Real) * Real.goldenRatio ^ 3) :
    Summable (fun p : Nat.Primes =>
      ‖((p : Complex) ^ (-s * ((Real.goldenRatio ^ 2 : Real) : Complex))) ^ a *
       ((p : Complex) ^ (-s * ((Real.goldenRatio ^ 3 : Real) : Complex))) ^ b‖) := by
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
    ‖((p : Complex) ^ (-s * ((Real.goldenRatio ^ 2 : Real) : Complex))) ^ a *
     ((p : Complex) ^ (-s * ((Real.goldenRatio ^ 3 : Real) : Complex))) ^ b‖ <= 1 := by
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
    ‖((p : Complex) ^ (-s * ((Real.goldenRatio ^ 2 : Real) : Complex))) ^ a *
     ((p : Complex) ^ (-s * ((Real.goldenRatio ^ 3 : Real) : Complex))) ^ b‖ < 1 := by
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
    ‖((p : Complex) ^ (-s * ((Real.goldenRatio ^ 2 : Real) : Complex))) ^ a *
     ((p : Complex) ^ (-s * ((Real.goldenRatio ^ 3 : Real) : Complex))) ^ b‖ <=
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
private theorem mixed_mode_norm_le_boundary (sigma : Real) (s : Complex)
    (hssigma : sigma <= s.re) (p : Nat.Primes) (a b : Nat)
    (hweight : 0 <= (a : Real) * Real.goldenRatio ^ 2 +
      (b : Real) * Real.goldenRatio ^ 3) :
    ‖((p : Complex) ^ (-s * ((Real.goldenRatio ^ 2 : Real) : Complex))) ^ a *
     ((p : Complex) ^ (-s * ((Real.goldenRatio ^ 3 : Real) : Complex))) ^ b‖ <=
    ‖((p : Complex) ^ (-(sigma : Complex) *
      ((Real.goldenRatio ^ 2 : Real) : Complex))) ^ a *
     ((p : Complex) ^ (-(sigma : Complex) *
      ((Real.goldenRatio ^ 3 : Real) : Complex))) ^ b‖ := by
  rw [← mixed_mode_cpow s p a b,
    ← mixed_mode_cpow (sigma : Complex) p a b]
  apply Complex.norm_natCast_cpow_le_norm_natCast_cpow_of_pos p.prop.pos
  simp only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero]
  nlinarith
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
      _ = Real.goldenRatio ^ 2 * (Real.goldenRatio + 1) :=
        congrArg (fun z : Real => Real.goldenRatio ^ 2 * z)
          Real.goldenRatio_sq
      _ = Real.goldenRatio ^ 2 + Real.goldenRatio ^ 3 := by ring
  have hcube : Real.goldenRatio ^ 3 = 2 * Real.goldenRatio + 1 := by
    calc
      Real.goldenRatio ^ 3 =
          Real.goldenRatio * Real.goldenRatio ^ 2 := by ring
      _ = Real.goldenRatio * (Real.goldenRatio + 1) := by
        rw [Real.goldenRatio_sq]
      _ = 2 * Real.goldenRatio + 1 := by
        nlinarith [Real.goldenRatio_sq]
  have hgoldenLower : (8 : Real) / 5 < Real.goldenRatio := by
    rw [Real.goldenRatio]
    have hsqrt_sq : Real.sqrt 5 ^ 2 = (5 : Real) :=
      Real.sq_sqrt (by norm_num)
    nlinarith [Real.sqrt_nonneg 5]
  have hgoldenUpper : Real.goldenRatio < (5 : Real) / 3 := by
    rw [Real.goldenRatio]
    have hsqrt_sq : Real.sqrt 5 ^ 2 = (5 : Real) :=
      Real.sq_sqrt (by norm_num)
    nlinarith [Real.sqrt_nonneg 5]
  have hfloorFive : ⌊(5 : Real) * Real.goldenRatio⌋ = (8 : Int) := by
    rw [Int.floor_eq_iff]
    constructor <;> norm_num at * <;>
      nlinarith [hgoldenLower, hgoldenUpper]
  have hfloorSix : ⌊(6 : Real) * Real.goldenRatio⌋ = (9 : Int) := by
    rw [Int.floor_eq_iff]
    constructor <;> norm_num at * <;>
      nlinarith [hgoldenLower, hgoldenUpper]
  have hbetaFour :
      o5Beta 4 = 2 * Real.goldenRatio ^ 2 + Real.goldenRatio ^ 3 := by
    rw [o5Beta]
    norm_num
    rw [hfloorFive, hcube]
    norm_num
    nlinarith [Real.goldenRatio_sq]
  have hfifth : Real.goldenRatio ^ 5 = 3 + 5 * Real.goldenRatio := by
    calc
      Real.goldenRatio ^ 5 =
          Real.goldenRatio ^ 3 * Real.goldenRatio ^ 2 := by ring
      _ = (2 * Real.goldenRatio + 1) *
          (Real.goldenRatio + 1) := by
        rw [hcube, Real.goldenRatio_sq]
      _ = 3 + 5 * Real.goldenRatio := by
        nlinarith [Real.goldenRatio_sq]
  have hbetaFive : o5Beta 5 = Real.goldenRatio ^ 5 := by
    rw [o5Beta]
    norm_num
    rw [hfloorSix, hfifth]
    ring
  have hgoldenFifth : Real.goldenRatio ^ 5 =
      Real.goldenRatio ^ 2 + 2 * Real.goldenRatio ^ 3 := by
    rw [hfifth, hcube, Real.goldenRatio_sq]
    ring
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
    simp only [f, hbetaFour]
    simpa [x, y] using mixed_mode_cpow s p 2 1
  have hf5 : f 5 = x * y ^ 2 := by
    simp only [f, hbetaFive]
    rw [hgoldenFifth]
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
set_option maxHeartbeats 1200000 in
-- The six-mode remainder estimate contains the full fixed cancellation ledger.
private theorem uniform_majorant (sigma : Real)
    (hsigma : 1 / Real.goldenRatio ^ 5 < sigma) :
    ∃ u : Nat.Primes -> Real, Summable u ∧
      ∀ p : Nat.Primes, ∀ s : Complex, sigma <= s.re ->
        let x := (p : Complex) ^
          (-s * ((Real.goldenRatio ^ 2 : Real) : Complex))
        let y := (p : Complex) ^
          (-s * ((Real.goldenRatio ^ 3 : Real) : Complex))
        ‖(1 - y ^ 2)⁻¹ * (1 - x ^ 2 * y) *
            (1 - y) * (1 + x)⁻¹ * germLocalFactor s p - 1‖ <= u p := by
  let tailBound : Nat.Primes -> Real := fun p =>
    ∑' k : Nat,
      ‖(p : Complex) ^
        (-(sigma : Complex) * (o5Beta (k + 6) : Complex))‖
  let modeBound : Nat -> Nat -> Nat.Primes -> Real := fun a b p =>
    ‖((p : Complex) ^
        (-(sigma : Complex) *
          ((Real.goldenRatio ^ 2 : Real) : Complex))) ^ a *
      ((p : Complex) ^
        (-(sigma : Complex) *
          ((Real.goldenRatio ^ 3 : Real) : Complex))) ^ b‖
  let qx : Real := (2 : Real) ^ (-sigma * Real.goldenRatio ^ 2)
  let qy : Real := (2 : Real) ^ (-sigma * (2 * Real.goldenRatio ^ 3))
  let Cx : Real := 1 / (1 - qx)
  let Cy : Real := 1 / (1 - qy)
  let remainderBound : Nat.Primes -> Real := fun p =>
    Cx * (modeBound 1 2 p + modeBound 3 1 p + modeBound 2 2 p +
      modeBound 1 3 p + 2 * tailBound p)
  let u : Nat.Primes -> Real := fun p =>
    Cy * (2 * remainderBound p + modeBound 2 3 p + modeBound 4 2 p)
  have hsigma_pos : 0 < sigma := lt_trans (by positivity) hsigma
  have hcube : Real.goldenRatio ^ 3 = 2 * Real.goldenRatio + 1 := by
    calc
      Real.goldenRatio ^ 3 =
          Real.goldenRatio * Real.goldenRatio ^ 2 := by ring
      _ = Real.goldenRatio * (Real.goldenRatio + 1) := by
        rw [Real.goldenRatio_sq]
      _ = 2 * Real.goldenRatio + 1 := by
        nlinarith [Real.goldenRatio_sq]
  have hgoldenFifth : Real.goldenRatio ^ 5 =
      Real.goldenRatio ^ 2 + 2 * Real.goldenRatio ^ 3 := by
    have hfifth : Real.goldenRatio ^ 5 = 3 + 5 * Real.goldenRatio := by
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
  have h12 : Real.goldenRatio ^ 5 <=
      ((1 : Nat) : Real) * Real.goldenRatio ^ 2 +
        ((2 : Nat) : Real) * Real.goldenRatio ^ 3 := by
    simpa using hgoldenFifth.le
  have h31 : Real.goldenRatio ^ 5 <=
      ((3 : Nat) : Real) * Real.goldenRatio ^ 2 +
        ((1 : Nat) : Real) * Real.goldenRatio ^ 3 := by
    rw [hgoldenFifth, hcube, Real.goldenRatio_sq]
    norm_num
    nlinarith
  have h22 : Real.goldenRatio ^ 5 <=
      ((2 : Nat) : Real) * Real.goldenRatio ^ 2 +
        ((2 : Nat) : Real) * Real.goldenRatio ^ 3 := by
    rw [hgoldenFifth]
    norm_num
    nlinarith [sq_pos_of_pos Real.goldenRatio_pos]
  have h13 : Real.goldenRatio ^ 5 <=
      ((1 : Nat) : Real) * Real.goldenRatio ^ 2 +
        ((3 : Nat) : Real) * Real.goldenRatio ^ 3 := by
    rw [hgoldenFifth]
    norm_num
    nlinarith [show 0 < Real.goldenRatio ^ 3 by positivity]
  have h23 : Real.goldenRatio ^ 5 <=
      ((2 : Nat) : Real) * Real.goldenRatio ^ 2 +
        ((3 : Nat) : Real) * Real.goldenRatio ^ 3 := by
    rw [hgoldenFifth]
    norm_num
    nlinarith [sq_pos_of_pos Real.goldenRatio_pos,
      show 0 < Real.goldenRatio ^ 3 by positivity]
  have h42 : Real.goldenRatio ^ 5 <=
      ((4 : Nat) : Real) * Real.goldenRatio ^ 2 +
        ((2 : Nat) : Real) * Real.goldenRatio ^ 3 := by
    rw [hgoldenFifth]
    norm_num
    nlinarith [sq_pos_of_pos Real.goldenRatio_pos]
  have hqxlt : qx < 1 := by
    dsimp [qx]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num)
      (mul_neg_of_neg_of_pos (neg_neg_of_pos hsigma_pos)
        (sq_pos_of_pos Real.goldenRatio_pos))
  have hqylt : qy < 1 := by
    dsimp [qy]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num)
      (mul_neg_of_neg_of_pos (neg_neg_of_pos hsigma_pos) (by positivity))
  have hCx : 0 <= Cx := by dsimp [Cx]; positivity
  have hCy : 0 <= Cy := by dsimp [Cy]; positivity
  have hsigmaNorm := sixth_tail_norm_summable
    (sigma : Complex) (by simpa using hsigma)
  have htailBound : Summable tailBound := by
    simpa [tailBound] using hsigmaNorm.prod
  have hm12 : Summable (modeBound 1 2) := by
    simpa [modeBound] using
      mixed_mode_norm_summable (sigma : Complex) (by simpa using hsigma) 1 2 h12
  have hm31 : Summable (modeBound 3 1) := by
    simpa [modeBound] using
      mixed_mode_norm_summable (sigma : Complex) (by simpa using hsigma) 3 1 h31
  have hm22 : Summable (modeBound 2 2) := by
    simpa [modeBound] using
      mixed_mode_norm_summable (sigma : Complex) (by simpa using hsigma) 2 2 h22
  have hm13 : Summable (modeBound 1 3) := by
    simpa [modeBound] using
      mixed_mode_norm_summable (sigma : Complex) (by simpa using hsigma) 1 3 h13
  have hm23 : Summable (modeBound 2 3) := by
    simpa [modeBound] using
      mixed_mode_norm_summable (sigma : Complex) (by simpa using hsigma) 2 3 h23
  have hm42 : Summable (modeBound 4 2) := by
    simpa [modeBound] using
      mixed_mode_norm_summable (sigma : Complex) (by simpa using hsigma) 4 2 h42
  have hremMajor : Summable (fun p : Nat.Primes =>
      modeBound 1 2 p + modeBound 3 1 p + modeBound 2 2 p +
        modeBound 1 3 p + 2 * tailBound p) :=
    (((hm12.add hm31).add hm22).add hm13).add (htailBound.mul_left 2)
  have hremBound : Summable remainderBound := by
    simpa [remainderBound] using hremMajor.mul_left Cx
  have hu : Summable u := by
    simpa [u] using
      (((hremBound.mul_left 2).add hm23).add hm42).mul_left Cy
  refine ⟨u, hu, ?_⟩
  intro p s hssigma
  dsimp only
  have hs : 1 / Real.goldenRatio ^ 5 < s.re :=
    hsigma.trans_le hssigma
  let x : Complex := (p : Complex) ^
    (-s * ((Real.goldenRatio ^ 2 : Real) : Complex))
  let y : Complex := (p : Complex) ^
    (-s * ((Real.goldenRatio ^ 3 : Real) : Complex))
  let tail : Complex := ∑' k : Nat,
    (p : Complex) ^ (-s * (o5Beta (k + 6) : Complex))
  let remainder : Complex := (1 + x)⁻¹ *
    (x * y ^ 2 - x ^ 3 * y - x ^ 2 * y ^ 2 - x * y ^ 3 +
      (1 - y) * tail)
  have hsNorm := sixth_tail_norm_summable s hs
  have htail : ‖tail‖ <= tailBound p := by
    refine (norm_tsum_le_tsum_norm (hsNorm.prod_factor p)).trans ?_
    exact (hsNorm.prod_factor p).tsum_le_tsum
      (fun k =>
        D5.S3.Analytic.EulerGerm.GermProductBound.germ_mode_norm_le
          sigma s hssigma p (k + 6))
      (hsigmaNorm.prod_factor p)
  have hxInv : ‖(1 + x)⁻¹‖ <= Cx := by
    have hxq : ‖x‖ <= qx := by
      calc
        ‖x‖ <= modeBound 1 0 p := by
          simpa [x, modeBound] using
            mixed_mode_norm_le_boundary sigma s hssigma p 1 0 (by positivity)
        _ <= qx := by
          simpa [modeBound, qx] using
            mixed_mode_norm_le_two (sigma : Complex)
              (by simpa using hsigma) p 1 0 (by positivity)
    have hlower : 1 - qx <= ‖1 + x‖ := by
      calc
        1 - qx <= 1 - ‖x‖ := sub_le_sub_left hxq 1
        _ = ‖(1 : Complex)‖ - ‖-x‖ := by simp
        _ <= ‖(1 : Complex) - (-x)‖ := norm_sub_norm_le _ _
        _ = ‖1 + x‖ := by simp only [sub_neg_eq_add]
    rw [norm_inv]
    simpa [Cx, one_div] using
      one_div_le_one_div_of_le (sub_pos.mpr hqxlt) hlower
  have hyInv : ‖(1 - y ^ 2)⁻¹‖ <= Cy := by
    have hyq : ‖y ^ 2‖ <= qy := by
      calc
        ‖y ^ 2‖ <= modeBound 0 2 p := by
          simpa [x, y, modeBound] using
            mixed_mode_norm_le_boundary sigma s hssigma p 0 2 (by positivity)
        _ <= qy := by
          simpa [modeBound, qy] using
            mixed_mode_norm_le_two (sigma : Complex)
              (by simpa using hsigma) p 0 2 (by positivity)
    have hlower : 1 - qy <= ‖1 - y ^ 2‖ := by
      calc
        1 - qy <= 1 - ‖y ^ 2‖ := sub_le_sub_left hyq 1
        _ = ‖(1 : Complex)‖ - ‖y ^ 2‖ := by simp
        _ <= ‖(1 : Complex) - y ^ 2‖ := norm_sub_norm_le _ _
    rw [norm_inv]
    simpa [Cy, one_div] using
      one_div_le_one_div_of_le (sub_pos.mpr hqylt) hlower
  have hyNorm : ‖y‖ <= 1 := by
    simpa [x, y] using mixed_mode_norm_le_one s hs p 0 1 (by positivity)
  have haNorm : ‖x ^ 2 * y‖ <= 1 := by
    simpa [x, y] using mixed_mode_norm_le_one s hs p 2 1 (by positivity)
  have hyMinus : 1 - y ^ 2 ≠ 0 := by
    rw [sub_ne_zero]
    intro heq
    have hlt : ‖y ^ 2‖ < 1 := by
      simpa [x, y] using mixed_mode_norm_lt_one s hs p 0 2 (by positivity)
    rw [← heq, norm_one] at hlt
    exact lt_irrefl 1 hlt
  have hm12Bound : ‖x * y ^ 2‖ <= modeBound 1 2 p := by
    simpa [x, y, modeBound] using
      mixed_mode_norm_le_boundary sigma s hssigma p 1 2 (by positivity)
  have hm31Bound : ‖x ^ 3 * y‖ <= modeBound 3 1 p := by
    simpa [x, y, modeBound] using
      mixed_mode_norm_le_boundary sigma s hssigma p 3 1 (by positivity)
  have hm22Bound : ‖x ^ 2 * y ^ 2‖ <= modeBound 2 2 p := by
    simpa [x, y, modeBound] using
      mixed_mode_norm_le_boundary sigma s hssigma p 2 2 (by positivity)
  have hm13Bound : ‖x * y ^ 3‖ <= modeBound 1 3 p := by
    simpa [x, y, modeBound] using
      mixed_mode_norm_le_boundary sigma s hssigma p 1 3 (by positivity)
  have htailPart : ‖(1 - y) * tail‖ <= 2 * ‖tail‖ := by
    rw [norm_mul]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    calc
      ‖1 - y‖ <= ‖(1 : Complex)‖ + ‖y‖ := norm_sub_le _ _
      _ <= 2 := by norm_num; linarith
  have hinside :
      ‖x * y ^ 2 - x ^ 3 * y - x ^ 2 * y ^ 2 - x * y ^ 3 +
          (1 - y) * tail‖ <=
        modeBound 1 2 p + modeBound 3 1 p + modeBound 2 2 p +
          modeBound 1 3 p + 2 * tailBound p := by
    calc
      ‖x * y ^ 2 - x ^ 3 * y - x ^ 2 * y ^ 2 - x * y ^ 3 +
          (1 - y) * tail‖ <=
          ‖x * y ^ 2 - x ^ 3 * y - x ^ 2 * y ^ 2 - x * y ^ 3‖ +
            ‖(1 - y) * tail‖ := norm_add_le _ _
      _ <= (‖x * y ^ 2‖ + ‖x ^ 3 * y‖ + ‖x ^ 2 * y ^ 2‖ +
          ‖x * y ^ 3‖) + 2 * ‖tail‖ := by
        have h1 := norm_sub_le (x * y ^ 2) (x ^ 3 * y)
        have h2 := norm_sub_le (x * y ^ 2 - x ^ 3 * y) (x ^ 2 * y ^ 2)
        have h3 := norm_sub_le
          (x * y ^ 2 - x ^ 3 * y - x ^ 2 * y ^ 2) (x * y ^ 3)
        linarith
      _ <= modeBound 1 2 p + modeBound 3 1 p + modeBound 2 2 p +
          modeBound 1 3 p + 2 * tailBound p := by
        gcongr
  have hremBound : ‖remainder‖ <= remainderBound p := by
    rw [show remainder = (1 + x)⁻¹ *
        (x * y ^ 2 - x ^ 3 * y - x ^ 2 * y ^ 2 - x * y ^ 3 +
          (1 - y) * tail) from rfl, norm_mul]
    exact mul_le_mul hxInv hinside (norm_nonneg _) hCx
  have hSecond :
      (1 - y) * (1 + x)⁻¹ * germLocalFactor s p =
        1 - y ^ 2 + x ^ 2 * y + remainder := by
    simpa [x, y, tail, remainder] using
      second_normalized_explicit_remainder s hs p
  have hdeviation :
      (1 - y ^ 2)⁻¹ * (1 - x ^ 2 * y) *
          (1 - y) * (1 + x)⁻¹ * germLocalFactor s p - 1 =
        (1 - y ^ 2)⁻¹ *
          (remainder - (x ^ 2 * y) * remainder +
            (x ^ 2 * y) * y ^ 2 - (x ^ 2 * y) ^ 2) := by
    calc
      (1 - y ^ 2)⁻¹ * (1 - x ^ 2 * y) *
          (1 - y) * (1 + x)⁻¹ * germLocalFactor s p - 1 =
          (1 - y ^ 2)⁻¹ * (1 - x ^ 2 * y) *
            ((1 - y) * (1 + x)⁻¹ * germLocalFactor s p) - 1 := by ring
      _ = (1 - y ^ 2)⁻¹ *
          (remainder - (x ^ 2 * y) * remainder +
            (x ^ 2 * y) * y ^ 2 - (x ^ 2 * y) ^ 2) := by
        rw [hSecond]
        field_simp [hyMinus]
        ring
  have hm23Bound : ‖(x ^ 2 * y) * y ^ 2‖ <= modeBound 2 3 p := by
    have heq : (x ^ 2 * y) * y ^ 2 = x ^ 2 * y ^ 3 := by ring
    rw [heq]
    simpa [x, y, modeBound] using
      mixed_mode_norm_le_boundary sigma s hssigma p 2 3 (by positivity)
  have hm42Bound : ‖(x ^ 2 * y) ^ 2‖ <= modeBound 4 2 p := by
    have heq : (x ^ 2 * y) ^ 2 = x ^ 4 * y ^ 2 := by ring
    rw [heq]
    simpa [x, y, modeBound] using
      mixed_mode_norm_le_boundary sigma s hssigma p 4 2 (by positivity)
  rw [hdeviation, norm_mul]
  have haRem : ‖(x ^ 2 * y) * remainder‖ <= ‖remainder‖ := by
    rw [norm_mul]
    simpa using mul_le_of_le_one_left (norm_nonneg remainder) haNorm
  have hfinalInside :
      ‖remainder - (x ^ 2 * y) * remainder +
          (x ^ 2 * y) * y ^ 2 - (x ^ 2 * y) ^ 2‖ <=
        2 * remainderBound p + modeBound 2 3 p + modeBound 4 2 p := by
    have h1 := norm_sub_le remainder ((x ^ 2 * y) * remainder)
    have h2 := norm_add_le
      (remainder - (x ^ 2 * y) * remainder) ((x ^ 2 * y) * y ^ 2)
    have h3 := norm_sub_le
      (remainder - (x ^ 2 * y) * remainder + (x ^ 2 * y) * y ^ 2)
      ((x ^ 2 * y) ^ 2)
    linarith
  exact mul_le_mul hyInv hfinalInside (norm_nonneg _) hCy
/- The public split boundary packages every fact the downstream regularity
module needs; no private declaration in this file is part of that dependency. -/
/-- Above the phi-fifth threshold, the third-normalized local deviations admit
a prime-summable uniform majorant. Their factors are differentiable and their
prime product converges locally uniformly on the corresponding open half-plane. -/
theorem golden_germ_third_normalized_factor_majorant (sigma : Real)
    (hsigma : 1 / Real.goldenRatio ^ 5 < sigma) :
    let Kp : Complex -> Nat.Primes -> Complex := fun s p =>
        let x := (p : Complex) ^
          (-s * ((Real.goldenRatio ^ 2 : Real) : Complex))
        let y := (p : Complex) ^
          (-s * ((Real.goldenRatio ^ 3 : Real) : Complex))
        (1 - y ^ 2)⁻¹ * (1 - x ^ 2 * y) * (1 - y) * (1 + x)⁻¹ *
          germLocalFactor s p
    let f : Nat.Primes -> Complex -> Complex := fun p s => Kp s p - 1
    let G3 : Complex -> Complex := fun s => ∏' p : Nat.Primes, Kp s p
    let U : Set Complex := {s : Complex | sigma < s.re}
    (∃ u : Nat.Primes -> Real, Summable u ∧
      ∀ p : Nat.Primes, ∀ s : Complex, sigma <= s.re -> ‖f p s‖ <= u p) ∧
    (∀ p : Nat.Primes, DifferentiableOn Complex (f p) U) ∧
    HasProdLocallyUniformlyOn (fun p s => 1 + f p s) G3 U := by
  dsimp only
  let U : Set Complex := {s : Complex | sigma < s.re}
  let f : Nat.Primes -> Complex -> Complex := fun p s =>
    let x := (p : Complex) ^
      (-s * ((Real.goldenRatio ^ 2 : Real) : Complex))
    let y := (p : Complex) ^
      (-s * ((Real.goldenRatio ^ 3 : Real) : Complex))
    (1 - y ^ 2)⁻¹ * (1 - x ^ 2 * y) *
      (1 - y) * (1 + x)⁻¹ * germLocalFactor s p - 1
  have hmajor := uniform_majorant sigma hsigma
  obtain ⟨u, hu, hbound⟩ := hmajor
  have hU : IsOpen U :=
    isOpen_lt continuous_const Complex.continuous_re
  have hfactor : ∀ p : Nat.Primes,
      DifferentiableOn Complex (f p) U := by
    intro p
    have hbase : (p : Complex) ≠ 0 := by
      exact_mod_cast p.prop.ne_zero
    have hx : Differentiable Complex (fun s : Complex =>
        (p : Complex) ^
          (-s * ((Real.goldenRatio ^ 2 : Real) : Complex))) :=
      (differentiable_id.neg.mul_const
        ((Real.goldenRatio ^ 2 : Real) : Complex)).const_cpow (.inl hbase)
    have hy : Differentiable Complex (fun s : Complex =>
        (p : Complex) ^
          (-s * ((Real.goldenRatio ^ 3 : Real) : Complex))) :=
      (differentiable_id.neg.mul_const
        ((Real.goldenRatio ^ 3 : Real) : Complex)).const_cpow (.inl hbase)
    have hone : DifferentiableOn Complex (fun _ : Complex => (1 : Complex)) U :=
      differentiableOn_const (c := (1 : Complex))
    have hySquareMinus : ∀ s ∈ U,
        1 - ((p : Complex) ^
          (-s * ((Real.goldenRatio ^ 3 : Real) : Complex))) ^ 2 ≠ 0 := by
      intro s hsU hzero
      have hdomain : 1 / Real.goldenRatio ^ 5 < s.re :=
        hsigma.trans hsU
      have hlt : ‖((p : Complex) ^
          (-s * ((Real.goldenRatio ^ 3 : Real) : Complex))) ^ 2‖ < 1 := by
        simpa using mixed_mode_norm_lt_one s hdomain p 0 2 (by positivity)
      rw [← sub_eq_zero.mp hzero, norm_one] at hlt
      exact lt_irrefl 1 hlt
    have hxPlus : ∀ s ∈ U,
        1 + (p : Complex) ^
          (-s * ((Real.goldenRatio ^ 2 : Real) : Complex)) ≠ 0 := by
      intro s hsU hzero
      have hdomain : 1 / Real.goldenRatio ^ 5 < s.re :=
        hsigma.trans hsU
      have hlt : ‖(p : Complex) ^
          (-s * ((Real.goldenRatio ^ 2 : Real) : Complex))‖ < 1 := by
        simpa using mixed_mode_norm_lt_one s hdomain p 1 0 (by positivity)
      have heq : (p : Complex) ^
          (-s * ((Real.goldenRatio ^ 2 : Real) : Complex)) = -1 := by
        linear_combination hzero
      rw [heq, norm_neg, norm_one] at hlt
      exact lt_irrefl 1 hlt
    have hlocal : DifferentiableOn Complex
        (fun s : Complex => germLocalFactor s p) U := by
      apply (germLocalFactor_analyticOnNhd_pos p p.prop).differentiableOn.mono
      intro s hsU
      change 0 < s.re
      exact lt_trans (by positivity) (hsigma.trans hsU)
    have hinvY : DifferentiableOn Complex (fun s : Complex =>
        (1 - ((p : Complex) ^
          (-s * ((Real.goldenRatio ^ 3 : Real) : Complex))) ^ 2)⁻¹) U :=
      (hone.sub (hy.pow 2).differentiableOn).inv hySquareMinus
    have hinvX : DifferentiableOn Complex (fun s : Complex =>
        (1 + (p : Complex) ^
          (-s * ((Real.goldenRatio ^ 2 : Real) : Complex)))⁻¹) U :=
      (hone.add hx.differentiableOn).inv hxPlus
    exact (((((hinvY.mul
      (hone.sub ((hx.pow 2).mul hy).differentiableOn)).mul
        (hone.sub hy.differentiableOn)).mul hinvX).mul hlocal).sub hone)
  have hcts : ∀ p : Nat.Primes, ContinuousOn (f p) U := fun p =>
    (hfactor p).continuousOn
  have hprod := hu.hasProdLocallyUniformlyOn_one_add hU
    (Filter.Eventually.of_forall fun p s hsU => hbound p s hsU.le) hcts
  exact ⟨⟨u, hu, hbound⟩, hfactor, by simpa [f, U] using hprod⟩
#print axioms golden_germ_third_normalized_factor_majorant
end
end D5.S3.Analytic.Regularity.GoldenGermThirdNormalizedFactorMajorant
