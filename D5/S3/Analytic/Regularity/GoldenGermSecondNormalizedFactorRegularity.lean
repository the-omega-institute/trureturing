/- GID: D5/S3/Analytic/Regularity/GoldenGermSecondNormalizedFactorRegularity
   generality: I
   mirror-B: D5/B/S3/Analytic/Regularity/GoldenGermSecondNormalizedFactorRegularity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The second normalized golden germ is regular and nonzero at its structural pole. -/

import D5.S3.Analytic.EulerGerm.GoldenGermSecondOrderFactorization
import D5.S3.Analytic.EulerGerm.GermProductBound

/- Library-search audit trail (2026-09-03):
   * Repository searches found the frozen pointwise deviation summability and
     factorization in `GoldenGermSecondOrderFactorization`, and the first-order
     locally uniform architecture in `GoldenGermNormalizedFactorRegularity`.
     No second-normalized regularity or structural-pole nonvanishing theorem
     was present.
   * The required frozen inputs were checked at their exact public names:
     `golden_germ_second_order_factorization`, `o5_beta_power_law`, and
     `germLocalFactor`. The factorization exposes pointwise summability but its
     fourth-tail expansion and bounds are private, so this module reuses the
     canonical definitions and rebuilds only the uniform local estimates.
   * Pinned Mathlib supplies `hasProdLocallyUniformlyOn_one_add`,
     `TendstoLocallyUniformlyOn.differentiableOn`,
     `Complex.differentiableOn_tsum_of_summable_norm`, and
     `tprod_one_add_ne_zero_of_summable`. The proposed qualified name
     `HasProdLocallyUniformlyOn.differentiableOn` is not a constant; method
     projection reaches the former theorem through the defining abbreviation.

   STOPPING JUSTIFICATION: this theorem closes regularity and nonvanishing of
   the second normalized factor at the structural pole. It does not assert a
   pole there for the continued germ, does not extend to the boundary
   `Re s = 1 / phi^4`, and implies neither O-5 nor the Riemann hypothesis. -/

namespace D5.S3.Analytic.Regularity.GoldenGermSecondNormalizedFactorRegularity

set_option autoImplicit false
set_option relaxedAutoImplicit false

open D5.S3.Analytic.GoldenEulerBeta
open D5.S3.Analytic.EulerGerm.GoldenLocalFactor
open D5.S3.Analytic.EulerGerm.GoldenGermSecondOrderFactorization

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
      have hfourth : Real.goldenRatio ^ 4 =
          3 * Real.goldenRatio + 2 := by
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
    exact Real.rpow_lt_one_of_one_lt_of_neg
      (by norm_num) (neg_neg_of_pos hsigma_pos)
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
    have hp_one : 1 <= (p : Real) := by
      exact_mod_cast p.prop.one_lt.le
    have hp_two : (2 : Real) <= (p : Real) := by
      exact_mod_cast p.prop.two_le
    have hbeta := o5_beta_three_add_ge (k + 1)
    push_cast at hbeta
    have hk : 0 <= (k : Real) := by positivity
    calc
      (p : Real) ^ (-sigma * o5Beta (k + 4)) <=
          (p : Real) ^
            (-sigma * (Real.goldenRatio ^ 4 + (k : Real))) :=
        Real.rpow_le_rpow_of_exponent_le hp_one (by nlinarith)
      _ = (p : Real) ^ r * (p : Real) ^ (-sigma * (k : Real)) := by
        rw [← Real.rpow_add (prime_real_pos p)]
        dsimp [r]
        congr 1
        ring
      _ <= (p : Real) ^ r * (2 : Real) ^ (-sigma * (k : Real)) := by
        exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_nonpos
            (z := -sigma * (k : Real)) (by norm_num) hp_two
            (mul_nonpos_of_nonpos_of_nonneg (by linarith) hk))
          (by positivity)
      _ = (p : Real) ^ r * q ^ k := by
        dsimp [q]
        rw [← Real.rpow_mul_natCast (by norm_num : (0 : Real) <= 2)]
  have htsum (k : Nat) :
      (∑' p : Nat.Primes,
        (p : Real) ^ (-sigma * o5Beta (k + 4))) <=
        (∑' p : Nat.Primes, (p : Real) ^ r) * q ^ k := by
    calc
      (∑' p : Nat.Primes,
          (p : Real) ^ (-sigma * o5Beta (k + 4))) <=
          ∑' p : Nat.Primes, (p : Real) ^ r * q ^ k :=
        (hslice k).tsum_le_tsum (hterm k) (hbase.mul_right (q ^ k))
      _ = (∑' p : Nat.Primes, (p : Real) ^ r) * q ^ k :=
        tsum_mul_right
  have houter : Summable (fun k : Nat =>
      ∑' p : Nat.Primes,
        (p : Real) ^ (-sigma * o5Beta (k + 4))) :=
    ((summable_geometric_of_lt_one hq_nonneg hq_lt_one).mul_left
      (∑' p : Nat.Primes, (p : Real) ^ r)).of_nonneg_of_le
        (fun _ => by positivity) htsum
  have hswapped : Summable (fun kp : Nat × Nat.Primes =>
      (kp.2 : Real) ^ (-sigma * o5Beta (kp.1 + 4))) :=
    (summable_prod_of_nonneg (fun _ => by positivity)).mpr
      ⟨hslice, houter⟩
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
      (p : Complex) ^
          (-s * ((Real.goldenRatio ^ 4 : Real) : Complex)) =
        (p : Complex) ^
            (-s * ((Real.goldenRatio ^ 2 : Real) : Complex)) *
          (p : Complex) ^
            (-s * ((Real.goldenRatio ^ 3 : Real) : Complex)) := by
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

private theorem mode_norm_lt_one (s : Complex)
    (hs : 1 / Real.goldenRatio ^ 4 < s.re) (c : Real) (hc : 0 < c)
    (p : Nat.Primes) :
    ‖(p : Complex) ^ (-s * (c : Complex))‖ < 1 := by
  have hspos : 0 < s.re := lt_trans (by positivity) hs
  rw [Complex.norm_natCast_cpow_of_pos p.prop.pos]
  rw [show (-s * (c : Complex)).re = -s.re * c by norm_num]
  exact Real.rpow_lt_one_of_one_lt_of_neg
    (by exact_mod_cast p.prop.one_lt)
    (mul_neg_of_neg_of_pos (neg_neg_of_pos hspos) hc)

private theorem mode_norm_le_one (s : Complex)
    (hs : 1 / Real.goldenRatio ^ 4 < s.re) (c : Real) (hc : 0 < c)
    (p : Nat.Primes) :
    ‖(p : Complex) ^ (-s * (c : Complex))‖ <= 1 :=
  (mode_norm_lt_one s hs c hc p).le

private theorem third_mode_square_norm_summable (sigma : Real)
    (hsigma : 1 / Real.goldenRatio ^ 4 < sigma) :
    Summable (fun p : Nat.Primes =>
      ‖((p : Complex) ^
        (-(sigma : Complex) *
          ((Real.goldenRatio ^ 3 : Real) : Complex))) ^ 2‖) := by
  have hsigma_pos : 0 < sigma := lt_trans (by positivity) hsigma
  have hphi4_lt : Real.goldenRatio ^ 4 <
      2 * Real.goldenRatio ^ 3 := by
    have hphi3 : 0 < Real.goldenRatio ^ 3 := by positivity
    calc
      Real.goldenRatio ^ 4 =
          Real.goldenRatio ^ 3 * Real.goldenRatio := by ring
      _ < Real.goldenRatio ^ 3 * 2 :=
        mul_lt_mul_of_pos_left Real.goldenRatio_lt_two hphi3
      _ = 2 * Real.goldenRatio ^ 3 := by ring
  have hexponent : -sigma * Real.goldenRatio ^ 3 * 2 < -1 := by
    have hcritical : 1 < sigma * Real.goldenRatio ^ 4 :=
      (div_lt_iff₀ (by positivity : 0 < Real.goldenRatio ^ 4)).mp
        (by simpa [div_eq_mul_inv] using hsigma)
    have hscaled := mul_lt_mul_of_pos_left hphi4_lt hsigma_pos
    nlinarith
  refine (Nat.Primes.summable_rpow.mpr hexponent).congr fun p => ?_
  rw [norm_pow, Complex.norm_natCast_cpow_of_pos p.prop.pos]
  rw [show (-(sigma : Complex) *
      ((Real.goldenRatio ^ 3 : Real) : Complex)).re =
        -sigma * Real.goldenRatio ^ 3 by
      simp only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, mul_zero, sub_zero]]
  exact Real.rpow_mul_natCast (prime_real_pos p).le
    (-sigma * Real.goldenRatio ^ 3) 2

private theorem inverse_one_add_first_mode_norm_le (sigma : Real)
    (hsigma : 1 / Real.goldenRatio ^ 4 < sigma) (s : Complex)
    (hssigma : sigma < s.re) (p : Nat.Primes) :
    let q : Real := (2 : Real) ^ (-sigma * Real.goldenRatio ^ 2)
    ‖(1 + (p : Complex) ^
        (-s * ((Real.goldenRatio ^ 2 : Real) : Complex)))⁻¹‖ <=
      1 / (1 - q) := by
  dsimp only
  let x : Complex := (p : Complex) ^
    (-s * ((Real.goldenRatio ^ 2 : Real) : Complex))
  let q : Real := (2 : Real) ^ (-sigma * Real.goldenRatio ^ 2)
  have hsigma_pos : 0 < sigma := lt_trans (by positivity) hsigma
  have hq_lt : q < 1 := by
    dsimp [q]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num)
      (mul_neg_of_neg_of_pos (neg_neg_of_pos hsigma_pos)
        (sq_pos_of_pos Real.goldenRatio_pos))
  have hxSigma :=
    D5.S3.Analytic.EulerGerm.GermProductBound.germ_mode_norm_le
      sigma s hssigma.le p 1
  rw [o5_beta_power_law.1] at hxSigma
  have hxq : ‖x‖ <= q := by
    calc
      ‖x‖ <= ‖(p : Complex) ^
          (-(sigma : Complex) *
            ((Real.goldenRatio ^ 2 : Real) : Complex))‖ := by
        simpa [x] using hxSigma
      _ <= q := by
        rw [Complex.norm_natCast_cpow_of_pos p.prop.pos]
        simp only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re,
          Complex.ofReal_im, mul_zero, sub_zero]
        dsimp [q]
        exact Real.rpow_le_rpow_of_nonpos (by norm_num)
          (by exact_mod_cast p.prop.two_le)
          (mul_nonpos_of_nonpos_of_nonneg (by linarith)
            (sq_nonneg Real.goldenRatio))
  have hlower : 1 - q <= ‖1 + x‖ := by
    calc
      1 - q <= 1 - ‖x‖ := sub_le_sub_left hxq 1
      _ = ‖(1 : Complex)‖ - ‖-x‖ := by simp
      _ <= ‖(1 : Complex) - (-x)‖ := norm_sub_norm_le _ _
      _ = ‖1 + x‖ := by simp only [sub_neg_eq_add]
  have hpositive : 0 < 1 - q := sub_pos.mpr hq_lt
  rw [norm_inv]
  simpa [x, q, one_div] using
    one_div_le_one_div_of_le hpositive hlower

set_option maxHeartbeats 800000 in
-- The uniform bound combines the fourth-tail expansion with two norm majorants.
private theorem uniform_majorant (sigma : Real)
    (hsigma : 1 / Real.goldenRatio ^ 4 < sigma) :
    ∃ u : Nat.Primes -> Real, Summable u ∧
      ∀ p : Nat.Primes, ∀ s : Complex, sigma < s.re ->
        ‖(1 - (p : Complex) ^
              (-s * ((Real.goldenRatio ^ 3 : Real) : Complex))) *
            (1 + (p : Complex) ^
              (-s * ((Real.goldenRatio ^ 2 : Real) : Complex)))⁻¹ *
            germLocalFactor s p - 1‖ <= u p := by
  let tailBound : Nat.Primes -> Real := fun p =>
    ∑' k : Nat,
      ‖(p : Complex) ^
        (-(sigma : Complex) * (o5Beta (k + 4) : Complex))‖
  let squareBound : Nat.Primes -> Real := fun p =>
    ‖((p : Complex) ^
      (-(sigma : Complex) *
        ((Real.goldenRatio ^ 3 : Real) : Complex))) ^ 2‖
  let q : Real := (2 : Real) ^ (-sigma * Real.goldenRatio ^ 2)
  let C : Real := 1 / (1 - q)
  let u : Nat.Primes -> Real := fun p =>
    squareBound p + (2 * C) * tailBound p
  have hsigma_pos : 0 < sigma := lt_trans (by positivity) hsigma
  have hq_lt : q < 1 := by
    dsimp [q]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num)
      (mul_neg_of_neg_of_pos (neg_neg_of_pos hsigma_pos)
        (sq_pos_of_pos Real.goldenRatio_pos))
  have hCnonneg : 0 <= C := by
    dsimp [C]
    positivity
  have hsigmaNorm := fourth_tail_norm_summable
    (sigma : Complex) (by simpa using hsigma)
  have htailBound : Summable tailBound := by
    simpa [tailBound] using hsigmaNorm.prod
  have hsquareBound : Summable squareBound := by
    simpa [squareBound] using
      third_mode_square_norm_summable sigma hsigma
  have hu : Summable u :=
    hsquareBound.add (htailBound.mul_left (2 * C))
  refine ⟨u, hu, ?_⟩
  intro p s hssigma
  have hs : 1 / Real.goldenRatio ^ 4 < s.re := hsigma.trans hssigma
  let x : Complex := (p : Complex) ^
    (-s * ((Real.goldenRatio ^ 2 : Real) : Complex))
  let y : Complex := (p : Complex) ^
    (-s * ((Real.goldenRatio ^ 3 : Real) : Complex))
  let tail : Complex := ∑' k : Nat,
    (p : Complex) ^ (-s * (o5Beta (k + 4) : Complex))
  have hsNorm := fourth_tail_norm_summable s hs
  have htail : ‖tail‖ <= tailBound p := by
    refine (norm_tsum_le_tsum_norm (hsNorm.prod_factor p)).trans ?_
    exact (hsNorm.prod_factor p).tsum_le_tsum
      (fun k =>
        D5.S3.Analytic.EulerGerm.GermProductBound.germ_mode_norm_le
          sigma s hssigma.le p (k + 4))
      (hsigmaNorm.prod_factor p)
  have hySigma :=
    D5.S3.Analytic.EulerGerm.GermProductBound.germ_mode_norm_le
      sigma s hssigma.le p 2
  rw [o5_beta_power_law.2.1] at hySigma
  have hySquare : ‖y ^ 2‖ <= squareBound p := by
    dsimp [squareBound]
    simp only [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg y)
      (by simpa [y] using hySigma) 2
  have hyOne : ‖y‖ <= 1 := by
    change ‖(p : Complex) ^
      (-s * ((Real.goldenRatio ^ 3 : Real) : Complex))‖ <= 1
    exact mode_norm_le_one s hs
      (Real.goldenRatio ^ 3) (by positivity) p
  have hinv : ‖(1 + x)⁻¹‖ <= C := by
    change ‖(1 + (p : Complex) ^
        (-s * ((Real.goldenRatio ^ 2 : Real) : Complex)))⁻¹‖ <=
      1 / (1 - (2 : Real) ^
        (-sigma * Real.goldenRatio ^ 2))
    exact inverse_one_add_first_mode_norm_le
      sigma hsigma s hssigma p
  have hne : 1 + x ≠ 0 := by
    intro heq
    have hxlt : ‖x‖ < 1 := by
      change ‖(p : Complex) ^
        (-s * ((Real.goldenRatio ^ 2 : Real) : Complex))‖ < 1
      exact mode_norm_lt_one s hs
        (Real.goldenRatio ^ 2) (by positivity) p
    have hxneg : x = -1 := by linear_combination heq
    rw [hxneg, norm_neg, norm_one] at hxlt
    exact lt_irrefl 1 hxlt
  have hlocal : germLocalFactor s p =
      (1 + x) * (1 + y) + tail := by
    simpa [x, y, tail] using
      local_factor_eq_second_order_and_tail s hs p
  have hdeviation :
      (1 - y) * (1 + x)⁻¹ * germLocalFactor s p - 1 =
        -(y ^ 2) + (1 - y) * (1 + x)⁻¹ * tail := by
    rw [hlocal]
    field_simp [hne]
    ring
  rw [hdeviation]
  calc
    ‖-(y ^ 2) + (1 - y) * (1 + x)⁻¹ * tail‖ <=
        ‖y ^ 2‖ + ‖(1 - y) * (1 + x)⁻¹ * tail‖ := by
      simpa only [norm_neg] using
        norm_add_le (-(y ^ 2)) ((1 - y) * (1 + x)⁻¹ * tail)
    _ <= ‖y ^ 2‖ + (2 * C) * ‖tail‖ := by
      gcongr
      rw [norm_mul, norm_mul]
      have hone : ‖1 - y‖ <= 2 := by
        calc
          ‖1 - y‖ <= ‖(1 : Complex)‖ + ‖y‖ := norm_sub_le _ _
          _ <= 2 := by norm_num; linarith
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      exact mul_le_mul hone hinv (norm_nonneg _) (by norm_num)
    _ <= squareBound p + (2 * C) * tailBound p := by
      exact add_le_add hySquare
        (mul_le_mul_of_nonneg_left htail
          (mul_nonneg (by norm_num) hCnonneg))
    _ = u p := rfl

private theorem germLocalFactor_differentiableOn (p : Nat.Primes)
    (sigma : Real) (hsigma : 1 / Real.goldenRatio ^ 4 < sigma) :
    DifferentiableOn Complex (fun s : Complex => germLocalFactor s p)
      {s : Complex | sigma < s.re} := by
  let U : Set Complex := {s : Complex | sigma < s.re}
  let v : Nat -> Real := fun k =>
    ‖(p : Complex) ^ (-(sigma : Complex) * (o5Beta k : Complex))‖
  have htail : Summable (fun k : Nat => v (k + 4)) := by
    simpa [v] using
      (fourth_tail_norm_summable (sigma : Complex)
        (by simpa using hsigma)).prod_factor p
  have hv : Summable v := (summable_nat_add_iff 4).1 htail
  have hU : IsOpen U :=
    isOpen_lt continuous_const Complex.continuous_re
  have hterms : ∀ k : Nat, DifferentiableOn Complex
      (fun s : Complex => (p : Complex) ^
        (-s * (o5Beta k : Complex))) U := by
    intro k
    have hbase : (p : Complex) ≠ 0 := by
      exact_mod_cast p.prop.ne_zero
    exact ((differentiable_id.neg.mul_const (o5Beta k : Complex)).const_cpow
      (.inl hbase)).differentiableOn
  have hsum := Complex.differentiableOn_tsum_of_summable_norm
    hv hterms hU (fun k s hs =>
      D5.S3.Analytic.EulerGerm.GermProductBound.germ_mode_norm_le
        sigma s hs.le p k)
  simpa [germLocalFactor, U, v] using hsum

private theorem normalized_product_differentiableOn (sigma : Real)
    (hsigma : 1 / Real.goldenRatio ^ 4 < sigma) :
    DifferentiableOn Complex
      (fun s : Complex => ∏' p : Nat.Primes,
        (1 - (p : Complex) ^
            (-s * ((Real.goldenRatio ^ 3 : Real) : Complex))) *
          (1 + (p : Complex) ^
            (-s * ((Real.goldenRatio ^ 2 : Real) : Complex)))⁻¹ *
          germLocalFactor s p)
      {s : Complex | sigma < s.re} := by
  let U : Set Complex := {s : Complex | sigma < s.re}
  let f : Nat.Primes -> Complex -> Complex := fun p s =>
    (1 - (p : Complex) ^
        (-s * ((Real.goldenRatio ^ 3 : Real) : Complex))) *
      (1 + (p : Complex) ^
        (-s * ((Real.goldenRatio ^ 2 : Real) : Complex)))⁻¹ *
      germLocalFactor s p - 1
  obtain ⟨u, hu, hbound⟩ := uniform_majorant sigma hsigma
  have hU : IsOpen U :=
    isOpen_lt continuous_const Complex.continuous_re
  have hfactor : ∀ p : Nat.Primes,
      DifferentiableOn Complex (f p) U := by
    intro p
    have hbase : (p : Complex) ≠ 0 := by
      exact_mod_cast p.prop.ne_zero
    have hcubed : Differentiable Complex (fun s : Complex =>
        (p : Complex) ^
          (-s * ((Real.goldenRatio ^ 3 : Real) : Complex))) :=
      (differentiable_id.neg.mul_const
        ((Real.goldenRatio ^ 3 : Real) : Complex)).const_cpow
          (.inl hbase)
    have hsquared : Differentiable Complex (fun s : Complex =>
        (p : Complex) ^
          (-s * ((Real.goldenRatio ^ 2 : Real) : Complex))) :=
      (differentiable_id.neg.mul_const
        ((Real.goldenRatio ^ 2 : Real) : Complex)).const_cpow
          (.inl hbase)
    have hone : DifferentiableOn Complex (fun _ : Complex => (1 : Complex)) U :=
      differentiableOn_const (c := (1 : Complex))
    have hplus_ne : ∀ s ∈ U,
        1 + (p : Complex) ^
          (-s * ((Real.goldenRatio ^ 2 : Real) : Complex)) ≠ 0 := by
      intro s hs hzero
      have hxlt := mode_norm_lt_one s (hsigma.trans hs)
        (Real.goldenRatio ^ 2) (by positivity) p
      have hxneg : (p : Complex) ^
          (-s * ((Real.goldenRatio ^ 2 : Real) : Complex)) = -1 := by
        linear_combination hzero
      rw [hxneg, norm_neg, norm_one] at hxlt
      exact lt_irrefl 1 hxlt
    have hinverse : DifferentiableOn Complex
        (fun s : Complex => (1 + (p : Complex) ^
          (-s * ((Real.goldenRatio ^ 2 : Real) : Complex)))⁻¹) U :=
      (hone.add hsquared.differentiableOn).inv hplus_ne
    exact ((((hone.sub hcubed.differentiableOn).mul hinverse).mul
      (germLocalFactor_differentiableOn p sigma hsigma)).sub hone)
  have hcts : ∀ p : Nat.Primes, ContinuousOn (f p) U := fun p =>
    (hfactor p).continuousOn
  have hprod := hu.hasProdLocallyUniformlyOn_one_add hU
    (Filter.Eventually.of_forall fun p s hs => hbound p s hs) hcts
  have hfinite : ∀ J : Finset Nat.Primes,
      DifferentiableOn Complex
        (fun s : Complex => ∏ p ∈ J, (1 + f p s)) U := by
    intro J
    induction J using Finset.induction_on with
    | empty =>
        simp only [Finset.prod_empty]
        exact differentiableOn_const (c := (1 : Complex))
    | @insert p J hp ih =>
        simp only [Finset.prod_insert hp]
        have hone : DifferentiableOn Complex
            (fun _ : Complex => (1 : Complex)) U :=
          differentiableOn_const (c := (1 : Complex))
        exact ((hone.add (hfactor p)).mul ih)
  have hlimit := hprod.differentiableOn
    (Filter.Eventually.of_forall hfinite) hU
  simpa [f, U] using hlimit

private theorem real_local_factor_summable (sigma : Real)
    (hsigma : 1 / Real.goldenRatio ^ 4 < sigma) (p : Nat.Primes) :
    Summable (fun v : Nat => (p : Real) ^ (-sigma * o5Beta v)) := by
  have htail : Summable (fun k : Nat =>
      (p : Real) ^ (-sigma * o5Beta (k + 4))) :=
    (fourth_tail_real_summable sigma hsigma).prod_factor p
  exact (summable_nat_add_iff 4).1 (by
    simpa [Nat.add_comm] using htail)

private theorem real_local_factor_pos (sigma : Real)
    (hsigma : 1 / Real.goldenRatio ^ 4 < sigma) (p : Nat.Primes) :
    0 < ∑' v : Nat, (p : Real) ^ (-sigma * o5Beta v) := by
  have hsum := real_local_factor_summable sigma hsigma p
  refine hsum.tsum_pos
    (fun _ => Real.rpow_nonneg (by positivity) _) 0 ?_
  simp [o5_beta_zero]

private theorem ofReal_real_local_factor_eq (sigma : Real)
    (p : Nat.Primes) :
    ((∑' v : Nat,
      (p : Real) ^ (-sigma * o5Beta v) : Real) : Complex) =
      germLocalFactor (sigma : Complex) p := by
  rw [germLocalFactor, Complex.ofReal_tsum]
  congr 1 with v
  rw [Complex.ofReal_cpow (by positivity)]
  congr 1
  norm_num

private theorem real_point_local_factor_ne_zero (sigma : Real)
    (hsigma : 1 / Real.goldenRatio ^ 4 < sigma) (p : Nat.Primes) :
    germLocalFactor (sigma : Complex) p ≠ 0 := by
  rw [← ofReal_real_local_factor_eq sigma p]
  exact_mod_cast (real_local_factor_pos sigma hsigma p).ne'

private theorem real_second_normalized_local_factor_ne_zero (sigma : Real)
    (hsigma : 1 / Real.goldenRatio ^ 4 < sigma) (p : Nat.Primes) :
    (1 - (p : Complex) ^
        (-(sigma : Complex) *
          ((Real.goldenRatio ^ 3 : Real) : Complex))) *
      (1 + (p : Complex) ^
        (-(sigma : Complex) *
          ((Real.goldenRatio ^ 2 : Real) : Complex)))⁻¹ *
      germLocalFactor (sigma : Complex) p ≠ 0 := by
  have hminus : 1 - (p : Complex) ^
      (-(sigma : Complex) *
        ((Real.goldenRatio ^ 3 : Real) : Complex)) ≠ 0 := by
    rw [sub_ne_zero]
    intro heq
    have hylt := mode_norm_lt_one (sigma : Complex) (by simpa using hsigma)
      (Real.goldenRatio ^ 3) (by positivity) p
    rw [← heq, norm_one] at hylt
    exact lt_irrefl 1 hylt
  have hplus : 1 + (p : Complex) ^
      (-(sigma : Complex) *
        ((Real.goldenRatio ^ 2 : Real) : Complex)) ≠ 0 := by
    intro hzero
    have hxlt := mode_norm_lt_one (sigma : Complex) (by simpa using hsigma)
      (Real.goldenRatio ^ 2) (by positivity) p
    have hxneg : (p : Complex) ^
        (-(sigma : Complex) *
          ((Real.goldenRatio ^ 2 : Real) : Complex)) = -1 := by
      linear_combination hzero
    rw [hxneg, norm_neg, norm_one] at hxlt
    exact lt_irrefl 1 hxlt
  exact mul_ne_zero (mul_ne_zero hminus (inv_ne_zero hplus))
    (real_point_local_factor_ne_zero sigma hsigma p)

private theorem fourth_threshold_lt_third_threshold :
    1 / Real.goldenRatio ^ 4 < 1 / Real.goldenRatio ^ 3 := by
  have hphi3 : 0 < Real.goldenRatio ^ 3 := by positivity
  have hphi3_lt_phi4 :
      Real.goldenRatio ^ 3 < Real.goldenRatio ^ 4 := by
    calc
      Real.goldenRatio ^ 3 <
          Real.goldenRatio ^ 3 * Real.goldenRatio :=
        (lt_mul_iff_one_lt_right hphi3).mpr Real.one_lt_goldenRatio
      _ = Real.goldenRatio ^ 4 := by ring
  exact one_div_lt_one_div_of_lt hphi3 hphi3_lt_phi4

/-- The second signed cancellation makes the normalized golden Euler product
holomorphic above `1 / phi^4`; at the structural pole `1 / phi^3` it is
continuous and nonzero. -/
theorem golden_germ_second_normalized_factor_regularity :
    let H : Complex -> Complex := fun s =>
      ∏' p : Nat.Primes,
        (1 - (p : Complex) ^
            (-s * ((Real.goldenRatio ^ 3 : Real) : Complex))) *
          (1 + (p : Complex) ^
            (-s * ((Real.goldenRatio ^ 2 : Real) : Complex)))⁻¹ *
          germLocalFactor s p
    AnalyticOnNhd Complex H
        {s : Complex | 1 / Real.goldenRatio ^ 4 < s.re} ∧
      ContinuousAt H ((1 / Real.goldenRatio ^ 3 : Real) : Complex) ∧
      H ((1 / Real.goldenRatio ^ 3 : Real) : Complex) ≠ 0 := by
  fail_if_success rfl
  fail_if_success (solve | simp)
  fail_if_success (solve | trivial)
  dsimp only
  let K : Set Complex :=
    {s : Complex | 1 / Real.goldenRatio ^ 4 < s.re}
  have hK : IsOpen K :=
    isOpen_lt continuous_const Complex.continuous_re
  have hanalytic : AnalyticOnNhd Complex
      (fun s : Complex => ∏' p : Nat.Primes,
        (1 - (p : Complex) ^
            (-s * ((Real.goldenRatio ^ 3 : Real) : Complex))) *
          (1 + (p : Complex) ^
            (-s * ((Real.goldenRatio ^ 2 : Real) : Complex)))⁻¹ *
          germLocalFactor s p) K := by
    intro s hs
    change 1 / Real.goldenRatio ^ 4 < s.re at hs
    let sigma : Real := (1 / Real.goldenRatio ^ 4 + s.re) / 2
    have hsigma : 1 / Real.goldenRatio ^ 4 < sigma := by
      dsimp [sigma]
      linarith
    have hssigma : sigma < s.re := by
      dsimp [sigma]
      linarith
    have hU : IsOpen {z : Complex | sigma < z.re} :=
      isOpen_lt continuous_const Complex.continuous_re
    exact (normalized_product_differentiableOn sigma hsigma).analyticAt
      (hU.mem_nhds hssigma)
  have hpole :
      1 / Real.goldenRatio ^ 4 <
        (((1 / Real.goldenRatio ^ 3 : Real) : Complex)).re := by
    change 1 / Real.goldenRatio ^ 4 < 1 / Real.goldenRatio ^ 3
    exact fourth_threshold_lt_third_threshold
  have hcontinuous : ContinuousAt
      (fun s : Complex => ∏' p : Nat.Primes,
        (1 - (p : Complex) ^
            (-s * ((Real.goldenRatio ^ 3 : Real) : Complex))) *
          (1 + (p : Complex) ^
            (-s * ((Real.goldenRatio ^ 2 : Real) : Complex)))⁻¹ *
          germLocalFactor s p)
      ((1 / Real.goldenRatio ^ 3 : Real) : Complex) :=
    hanalytic.continuousOn.continuousAt (hK.mem_nhds hpole)
  let pole : Complex := ((1 / Real.goldenRatio ^ 3 : Real) : Complex)
  let factor : Nat.Primes -> Complex := fun p =>
    (1 - (p : Complex) ^
        (-pole * ((Real.goldenRatio ^ 3 : Real) : Complex))) *
      (1 + (p : Complex) ^
        (-pole * ((Real.goldenRatio ^ 2 : Real) : Complex)))⁻¹ *
      germLocalFactor pole p
  have hpole' : 1 / Real.goldenRatio ^ 4 < pole.re := by
    dsimp [pole]
    exact fourth_threshold_lt_third_threshold
  have hsecond := golden_germ_second_order_factorization
  dsimp only at hsecond
  have hsum : Summable (fun p : Nat.Primes => ‖factor p - 1‖) := by
    simpa [factor] using hsecond.2 pole hpole'
  have hlocal : ∀ p : Nat.Primes, factor p ≠ 0 := by
    intro p
    simpa [factor, pole] using
      real_second_normalized_local_factor_ne_zero
        (1 / Real.goldenRatio ^ 3) fourth_threshold_lt_third_threshold p
  have hnonzeroAux := tprod_one_add_ne_zero_of_summable
    (f := fun p : Nat.Primes => factor p - 1)
    (fun p => by
      rw [show 1 + (factor p - 1) = factor p by ring]
      exact hlocal p)
    hsum
  have hfun : (fun p : Nat.Primes => 1 + (factor p - 1)) = factor := by
    funext p
    ring
  rw [hfun] at hnonzeroAux
  have hnonzero :
      (∏' p : Nat.Primes,
        (1 - (p : Complex) ^
            (-((1 / Real.goldenRatio ^ 3 : Real) : Complex) *
              ((Real.goldenRatio ^ 3 : Real) : Complex))) *
          (1 + (p : Complex) ^
            (-((1 / Real.goldenRatio ^ 3 : Real) : Complex) *
              ((Real.goldenRatio ^ 2 : Real) : Complex)))⁻¹ *
          germLocalFactor
            ((1 / Real.goldenRatio ^ 3 : Real) : Complex) p) ≠ 0 := by
    simpa [factor, pole] using hnonzeroAux
  exact ⟨hanalytic, hcontinuous, hnonzero⟩

#print axioms golden_germ_second_normalized_factor_regularity

end

end D5.S3.Analytic.Regularity.GoldenGermSecondNormalizedFactorRegularity
