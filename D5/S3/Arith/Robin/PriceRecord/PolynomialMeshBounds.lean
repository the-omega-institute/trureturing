/- GID: D5/S3/Arith/Robin/PriceRecord/PolynomialMeshBounds
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/PriceRecord/PolynomialMeshBounds
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Polynomial mesh geometry and full-clock weighted pressure interpolation. -/

import D5.S3.Arith.Robin.ActualTwoPriceDefect
import D5.S3.Arith.Robin.ActualRobinInterval
import Mathlib.Tactic

/-! Polynomial mesh bounds consumed by the full canonical-record strip criterion. -/

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Filter Set MeasureTheory
open scoped Topology
open D5.S3.Arith.Robin.ActualTwoPriceDefect
open D5.S3.Arith.Robin.ActualTwoPriceDefect (price)

namespace D5.S3.Arith.Robin.PriceRecord.PolynomialMeshBounds

lemma power_large (r : ℕ) (hr : 2 ≤ r) {k : ℕ} (hk : 4 ≤ k) :
    16 ≤ k ^ r := by
  calc
    16 ≤ k ^ 2 := by simpa using Nat.pow_le_pow_left hk 2
    _ ≤ k ^ r := pow_le_pow_right₀ (by omega : 1 ≤ k) hr

lemma power_atTop (r : ℕ) (hr : 2 ≤ r) :
    Tendsto (fun k : ℕ => ((k ^ r : ℕ) : ℝ)) atTop atTop := by
  simpa only [Nat.cast_pow, Function.comp_def] using
    (tendsto_pow_atTop (by omega : r ≠ 0)).comp
      (tendsto_natCast_atTop_atTop : Tendsto (fun k : ℕ => (k : ℝ)) atTop atTop)


lemma price_gap {a b : ℝ} (ha : 1 < a) (hab : a ≤ b)
    (hlog : 1 ≤ Real.log a) :
    price a - price b ≤ 2 * (b - a) / (a ^ 2 * Real.log a) := by
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := ha0.trans_le hab
  have hla : 0 < Real.log a := Real.log_pos ha
  have hlb : 0 < Real.log b := Real.log_pos (ha.trans_le hab)
  have hlogs : Real.log a ≤ Real.log b := Real.log_le_log ha0 hab
  have ht := Real.log_le_sub_one_of_pos (div_pos hb0 ha0)
  rw [Real.log_div hb0.ne' ha0.ne'] at ht
  have ht' : a * (Real.log b - Real.log a) ≤ b - a := by
    have hh := (le_div_iff₀ ha0).mp (show Real.log b - Real.log a ≤ (b - a) / a by
      convert ht using 1 <;> field_simp [ha0.ne'] <;> ring)
    nlinarith only [hh]
  have hdiff : 0 ≤ b - a := sub_nonneg.mpr hab
  have hsplit : price a - price b =
      (b - a) / (a * b * Real.log a) +
        (Real.log b - Real.log a) / (b * Real.log a * Real.log b) := by
    dsimp only [price]
    field_simp [ha0.ne', hb0.ne', hla.ne', hlb.ne'] <;> ring
  have hfirst : (b - a) / (a * b * Real.log a) ≤
      (b - a) / (a ^ 2 * Real.log a) := by
    apply div_le_div_of_nonneg_left hdiff (by positivity)
    have hh := mul_le_mul_of_nonneg_left hab (mul_nonneg ha0.le hla.le)
    nlinarith only [hh]
  have hsecond : (Real.log b - Real.log a) / (b * Real.log a * Real.log b) ≤
      (b - a) / (a ^ 2 * Real.log a) := by
    apply (div_le_div_iff₀ (by positivity : 0 < b * Real.log a * Real.log b)
      (by positivity : 0 < a ^ 2 * Real.log a)).mpr
    have h1 := mul_le_mul_of_nonneg_right ht'
      (show 0 ≤ a * Real.log a by positivity)
    have hablog : a ≤ b * Real.log b := by
      calc
        a ≤ b := hab
        _ ≤ b * Real.log b := by
          simpa only [mul_one] using mul_le_mul_of_nonneg_left (hlog.trans hlogs) hb0.le
    have h2 := mul_le_mul_of_nonneg_left hablog
      (mul_nonneg hdiff hla.le)
    nlinarith only [h1, h2]
  rw [hsplit]
  have hid : 2 * (b - a) / (a ^ 2 * Real.log a) =
      (b - a) / (a ^ 2 * Real.log a) + (b - a) / (a ^ 2 * Real.log a) := by ring
  linarith only [hfirst, hsecond, hid]

lemma pow_step (t : ℝ) (ht : 0 ≤ t) (n : ℕ) :
    (t + 1) ^ (n + 1) - t ^ (n + 1) ≤ ((n + 1 : ℕ) : ℝ) * (t + 1) ^ n := by
  have ht1 : 0 ≤ t + 1 := by linarith
  have h := (le_abs_self ((t + 1) ^ (n + 1) - t ^ (n + 1))).trans
    (abs_pow_sub_pow_le (a := t + 1) (b := t) (n := n + 1))
  simpa [abs_of_nonneg ht, abs_of_nonneg ht1,
    max_eq_left (show t ≤ t + 1 by linarith)] using h

/- The mesh pays both a constant multiplicative enclosure and its shrinking
relative width. No prime gaps occur in this calculation. -/
lemma mesh_geometry (r : ℕ) (hr : 2 ≤ r) {k : ℕ} (hk : 4 ≤ k) :
    let N : ℝ := ((k ^ r : ℕ) : ℝ)
    let H : ℝ := (2 : ℝ) ^ r
    let G : ℝ := (r : ℝ) * (2 : ℝ) ^ (r - 1)
    (((k + 1) ^ r : ℕ) : ℝ) ≤ H * N ∧
      (((k + 1) ^ r : ℕ) : ℝ) - N ≤ G * (N / (k : ℝ)) ∧
      (((k + 1) ^ r : ℕ) : ℝ) ≤ N ^ 2 := by
  dsimp only
  push_cast
  have ht : (4 : ℝ) ≤ k := by exact_mod_cast hk
  have ht0 : (0 : ℝ) < k := by linarith
  have hstep : ((k : ℝ) + 1) ^ r - (k : ℝ) ^ r ≤
      (r : ℝ) * ((k : ℝ) + 1) ^ (r - 1) := by
    have hh := pow_step (k : ℝ) ht0.le (r - 1)
    simpa only [Nat.sub_add_cancel (show 1 ≤ r by omega)] using hh
  have hpower : ((k : ℝ) + 1) ^ (r - 1) ≤
      (2 : ℝ) ^ (r - 1) * (k : ℝ) ^ (r - 1) := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (by linarith) (r - 1)
  have htp : (k : ℝ) ^ (r - 1) = (k : ℝ) ^ r / k := by
    apply (eq_div_iff ht0.ne').mpr
    rw [← pow_succ, Nat.sub_add_cancel (show 1 ≤ r by omega)]
  refine ⟨?_, ?_, ?_⟩
  · rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (by linarith) r
  · calc
      ((k : ℝ) + 1) ^ r - (k : ℝ) ^ r ≤
          (r : ℝ) * ((k : ℝ) + 1) ^ (r - 1) := hstep
      _ ≤ (r : ℝ) * ((2 : ℝ) ^ (r - 1) * (k : ℝ) ^ (r - 1)) :=
        mul_le_mul_of_nonneg_left hpower (Nat.cast_nonneg r)
      _ = (r : ℝ) * (2 : ℝ) ^ (r - 1) * ((k : ℝ) ^ r / k) := by rw [htp]; ring
  · have hbase : (k : ℝ) + 1 ≤ (k : ℝ) ^ 2 := by nlinarith
    have hh := pow_le_pow_left₀ (by positivity : 0 ≤ (k : ℝ) + 1) hbase r
    calc
      ((k : ℝ) + 1) ^ r ≤ ((k : ℝ) ^ 2) ^ r := hh
      _ = ((k : ℝ) ^ r) ^ 2 := by simp only [← pow_mul]; congr 1; omega

lemma mesh_bracket (r : ℕ) (hr : 2 ≤ r) (K : ℕ) {X : ℝ}
    (hX : ((K ^ r : ℕ) : ℝ) ≤ X) :
    ∃ k : ℕ, K ≤ k ∧ ((k ^ r : ℕ) : ℝ) ≤ X ∧
      X < (((k + 1) ^ r : ℕ) : ℝ) := by
  classical
  have hex : ∃ j : ℕ, X < (((j + 1) ^ r : ℕ) : ℝ) := by
    obtain ⟨j, hj⟩ := eventually_atTop.mp ((power_atTop r hr).eventually
      (eventually_gt_atTop X))
    refine ⟨j, (hj j le_rfl).trans_le ?_⟩
    exact_mod_cast Nat.pow_le_pow_left (Nat.le_succ j) r
  let k := Nat.find hex
  have hupper : X < (((k + 1) ^ r : ℕ) : ℝ) := Nat.find_spec hex
  have hK : K ≤ k := by
    by_contra h
    have hle : k + 1 ≤ K := by omega
    have hp : (((k + 1) ^ r : ℕ) : ℝ) ≤ ((K ^ r : ℕ) : ℝ) := by
      exact_mod_cast Nat.pow_le_pow_left hle r
    linarith
  refine ⟨k, hK, ?_, hupper⟩
  by_cases hk : k = 0
  · have hX0 : 0 ≤ X := (Nat.cast_nonneg (K ^ r)).trans hX
    simpa only [hk, zero_pow (by omega : r ≠ 0), Nat.cast_zero] using hX0
  · have hmin : ¬ X < ((((k - 1) + 1) ^ r : ℕ) : ℝ) :=
      Nat.find_min hex (show k - 1 < Nat.find hex by change k - 1 < k; omega)
    simpa only [Nat.sub_add_cancel (show 1 ≤ k by omega)] using le_of_not_gt hmin

lemma mesh_power_balance (r : ℕ) {alpha beta : ℝ}
    (hbalance : (r : ℝ) * (alpha + beta) ≤ (r : ℝ) + 1)
    {k : ℕ} (hk : 1 ≤ k) :
    Real.rpow (((k ^ r : ℕ) : ℝ)) alpha *
        Real.rpow (((k ^ r : ℕ) : ℝ)) beta ≤
      (((k ^ r : ℕ) : ℝ)) * (k : ℝ) := by
  have ht : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have ht0 : (0 : ℝ) < k := by linarith
  have hN0 : 0 < (((k ^ r : ℕ) : ℝ)) := by positivity
  simp only [Real.rpow_eq_pow]
  rw [← Real.rpow_add hN0]
  push_cast
  rw [← Real.rpow_natCast_mul ht0.le]
  calc
    Real.rpow (k : ℝ) ((r : ℝ) * (alpha + beta)) ≤
        Real.rpow (k : ℝ) ((r : ℝ) + 1) :=
      Real.rpow_le_rpow_of_exponent_le ht hbalance
    _ = (k : ℝ) ^ r * (k : ℝ) := by
      rw [Real.rpow_eq_pow, Real.rpow_add ht0, Real.rpow_natCast, Real.rpow_one]


lemma record_weight {alpha P L : ℝ} (halpha : 0 ≤ alpha)
    (halpha1 : alpha ≤ 1) (hP : 1 < P) (hL : 2 ≤ L) (hPL : P ≤ 2 * L) :
    Real.rpow P alpha * Real.log P ≤ 4 * (Real.rpow L alpha * Real.log L) := by
  have hL0 : 0 < L := by linarith
  have hp : Real.rpow P alpha ≤ 2 * Real.rpow L alpha := by
    calc
      Real.rpow P alpha ≤ Real.rpow (2 * L) alpha :=
        Real.rpow_le_rpow (by linarith) hPL halpha
      _ = Real.rpow 2 alpha * Real.rpow L alpha := Real.mul_rpow (by norm_num) hL0.le
      _ ≤ 2 * Real.rpow L alpha :=
        mul_le_mul_of_nonneg_right
          (by simpa only [Real.rpow_one, Real.rpow_eq_pow] using
            Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) halpha1)
          (Real.rpow_nonneg hL0.le _)
  have hPL2 : P ≤ L ^ 2 := by
    nlinarith only [hPL, mul_nonneg hL0.le (show 0 ≤ L - 2 by linarith)]
  have hl : Real.log P ≤ 2 * Real.log L := by
    have hh := Real.log_le_log (by linarith : 0 < P) hPL2
    simpa only [Real.log_pow, Nat.cast_ofNat] using hh
  have hh := mul_le_mul hp hl (Real.log_pos hP).le
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (Real.rpow_nonneg hL0.le _))
  nlinarith only [hh]


lemma W_factor (a b : ℝ) {X : ℝ} (hX : 0 < X) :
    (Real.rpow X a * Real.log X) = Real.rpow X (a - b) * (Real.rpow X b * Real.log X) := by
  simp only [Real.rpow_eq_pow]
  rw [Real.rpow_sub hX]
  field_simp [(Real.rpow_pos_of_pos hX b).ne']
  <;> ring

lemma sample_exponent_lower {a alpha M X v : ℝ}
    (hM : 0 ≤ M) (ha : a ≤ alpha) (hX : 1 < X)
    (hbound : -M ≤ (Real.rpow X alpha * Real.log X) * v) :
    -M ≤ (Real.rpow X a * Real.log X) * v := by
  have ht0 : 0 < Real.rpow X (a - alpha) :=
    Real.rpow_pos_of_pos (by linarith) _
  have ht1 : Real.rpow X (a - alpha) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hX.le (by linarith)
  have hMscale := mul_le_mul_of_nonneg_right ht1 hM
  have hneg : -M ≤ Real.rpow X (a - alpha) * (-M) := by
    nlinarith only [hMscale]
  calc
    -M ≤ Real.rpow X (a - alpha) * (-M) := hneg
    _ ≤ Real.rpow X (a - alpha) * ((Real.rpow X alpha * Real.log X) * v) :=
      mul_le_mul_of_nonneg_left hbound ht0.le
    _ = (Real.rpow X a * Real.log X) * v := by rw [W_factor a alpha (by linarith : 0 < X)]; ring

lemma rescale_lower {A c d e v : ℝ} (hA : 0 ≤ A) (hc : 0 ≤ c)
    (he : 0 ≤ e) (hed : e ≤ c * d) (hv : -A ≤ d * v) :
    -(c * A) ≤ e * v := by
  by_cases h : 0 ≤ v
  · exact (neg_nonpos.mpr (mul_nonneg hc hA)).trans (mul_nonneg he h)
  · have hneg : v ≤ 0 := le_of_not_ge h
    have hscale := mul_le_mul_of_nonpos_right hed hneg
    have hbase := mul_le_mul_of_nonneg_left hv hc
    nlinarith only [hscale, hbase]


private def S (X : ℝ) : ℝ :=
  Real.eulerMascheroniConstant + Real.log (Real.log X) - 1 / Real.log X -
    pressure (price X)
private def W (alpha X : ℝ) : ℝ := Real.rpow X alpha * Real.log X

lemma W_pos (alpha : ℝ) {X : ℝ} (hX : 1 < X) : 0 < Real.rpow X alpha * Real.log X := by
  exact mul_pos (Real.rpow_pos_of_pos (by linarith) _) (Real.log_pos hX)

private lemma w_pos (alpha : ℝ) {X : ℝ} (hX : 1 < X) : 0 < W alpha X :=
  W_pos alpha hX

private lemma pressure_clock_interval_modulus {a b E : ℝ}
    (ha : 1 < a) (hab : a ≤ b)
    (hclock : ∀ u : ℝ, u ∈ Set.Icc a b → |u - clock u| ≤ E) :
    |S b - S a| ≤ E * (price a - price b) := by
  have hb : 1 < b := ha.trans_le hab
  have hdomain (u : ℝ) (hu : u ∈ Set.uIcc a b) : 1 < u :=
    (lt_min ha hb).trans_le hu.1
  have hw : IntervalIntegrable weight volume a b :=
    (show ContinuousOn weight (Set.uIcc a b) from fun u hu =>
      (weight_continuousAt (hdomain u hu)).continuousWithinAt).intervalIntegrable
  have hi : IntervalIntegrable (fun u : ℝ => u * weight u) volume a b :=
    hw.continuousOn_mul continuousOn_id
  have hc : IntervalIntegrable (fun u : ℝ => clock u * weight u) volume a b :=
    clock_weight_integrable ha hb
  have hderiv : ∀ u ∈ Set.uIcc a b,
      HasDerivAt (fun t : ℝ => Real.log (Real.log t) - 1 / Real.log t)
        (u * weight u) u := by
    intro u hu
    have hu1 := hdomain u hu
    have hu0 : 0 < u := by linarith
    have hL : Real.log u ≠ 0 := (Real.log_pos hu1).ne'
    have hlog := Real.hasDerivAt_log hu0.ne'
    have hd := ((Real.hasDerivAt_log hL).comp u hlog).sub (hlog.inv hL)
    convert hd using 1
    · funext t
      simp only [Pi.sub_apply, Function.comp_apply, Pi.inv_apply, one_div]
    · dsimp only [weight]
      field_simp [hu0.ne', hL] <;> ring
  have hprimitive := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hi
  have hid : S b - S a =
      ∫ u in a..b, (u - clock u) * weight u := by
    calc
      S b - S a = (∫ u in a..b, u * weight u) -
          (∫ u in a..b, clock u * weight u) := by
        rw [hprimitive, pressure_integral ha hb]
        dsimp only [S]
        ring
      _ = ∫ u in a..b, (u - clock u) * weight u := by
        rw [← intervalIntegral.integral_sub hi hc]
        apply intervalIntegral.integral_congr
        intro u _
        ring
  have hd : IntervalIntegrable (fun u : ℝ => (u - clock u) * weight u)
      volume a b := by
    convert hi.sub hc using 1
    funext u
    ring
  rw [hid]
  calc
    |∫ u in a..b, (u - clock u) * weight u| ≤
        ∫ u in a..b, |(u - clock u) * weight u| :=
      intervalIntegral.abs_integral_le_integral_abs hab
    _ ≤ ∫ u in a..b, E * weight u := by
      apply intervalIntegral.integral_mono_on hab hd.abs (hw.const_mul E)
      intro u hu
      have hw0 : 0 ≤ weight u := by
        dsimp only [weight]
        positivity [Real.log_pos (ha.trans_le hu.1)]
      rw [abs_mul, abs_of_nonneg hw0]
      exact mul_le_mul_of_nonneg_right (hclock u hu) hw0
    _ = E * (price a - price b) := by
      rw [intervalIntegral.integral_const_mul, weight_integral ha hb]

lemma pressure_samples_to_all (r : ℕ) (hr : 2 ≤ r)
    (beta sigma C A : ℝ) (hC : 0 ≤ C) (hA : 0 ≤ A)
    (hsigma0 : 1 / 2 < sigma) (hsigma1 : sigma < 1)
    (hbeta : 0 ≤ beta) (hgap : beta - 1 / (r : ℝ) < sigma)
    (hclock : ∀ X : ℝ, 2 ≤ X → |X - clock X| ≤ C * Real.rpow X beta)
    (hsample : ∀ᶠ k : ℕ in atTop,
      -A ≤ (Real.rpow ((k ^ r : ℕ) : ℝ) (1 - sigma) *
        Real.log ((k ^ r : ℕ) : ℝ)) *
        (Real.eulerMascheroniConstant + Real.log (Real.log ((k ^ r : ℕ) : ℝ)) -
        1 / Real.log ((k ^ r : ℕ) : ℝ) - pressure (price ((k ^ r : ℕ) : ℝ)))) :
    ∃ B : ℝ, 0 ≤ B ∧ ∃ T : ℝ, ∀ X : ℝ, T ≤ X →
      -B ≤ (Real.rpow X (1 - sigma) * Real.log X) *
        (Real.eulerMascheroniConstant + Real.log (Real.log X) -
        1 / Real.log X - pressure (price X)) := by
  let alpha : ℝ := 1 - sigma
  let H : ℝ := (2 : ℝ) ^ r
  let G : ℝ := (r : ℝ) * (2 : ℝ) ^ (r - 1)
  let E0 : ℝ := 2 * C * Real.rpow H beta
  let B0 : ℝ := E0 * G
  have halpha : 0 < alpha := by dsimp [alpha]; linarith
  have halpha1 : alpha ≤ 1 := by linarith
  have hr0 : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have hH : 1 ≤ H := one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
  have hG : 0 ≤ G := by dsimp [G]; positivity
  have hE0 : 0 ≤ E0 := by dsimp [E0]; positivity
  have hB0 : 0 ≤ B0 := mul_nonneg hE0 hG
  have hbalance : (r : ℝ) * (alpha + beta) ≤ (r : ℝ) + 1 := by
    have hh : (r : ℝ) * (beta - sigma) < 1 := by
      have ht : beta - sigma < 1 / (r : ℝ) := by linarith only [hgap]
      have hm := (lt_div_iff₀ hr0).mp ht
      nlinarith only [hm]
    dsimp only [alpha]
    nlinarith only [hh]
  obtain ⟨K0, hK0⟩ := eventually_atTop.mp hsample
  let K := max K0 4
  refine ⟨(2 * H) * (A + B0), by positivity, ((K ^ r : ℕ) : ℝ), ?_⟩
  intro X hX
  obtain ⟨k, hkK, hNX, hXNplus⟩ := mesh_bracket r hr K hX
  have hk : 4 ≤ k := (le_max_right K0 4).trans hkK
  have hk0 : K0 ≤ k := (le_max_left K0 4).trans hkK
  let N : ℝ := ((k ^ r : ℕ) : ℝ)
  have hN16 : 16 ≤ N := by
    change (16 : ℝ) ≤ ((k ^ r : ℕ) : ℝ)
    exact_mod_cast power_large r hr hk
  have hN1 : 1 < N := by linarith
  have hN0 : 0 < N := by linarith
  have ht : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hlogN : 1 ≤ Real.log N :=
    (ActualRobinInterval.log_gt_one (show 3 ≤ k ^ r by
      have := power_large r hr hk; omega)).le
  have hgeom := mesh_geometry r hr hk
  change (((k + 1) ^ r : ℕ) : ℝ) ≤ H * N ∧
    (((k + 1) ^ r : ℕ) : ℝ) - N ≤ G * (N / (k : ℝ)) ∧
    (((k + 1) ^ r : ℕ) : ℝ) ≤ N ^ 2 at hgeom
  have hNX' : N ≤ X := hNX
  have hXH : X ≤ H * N := hXNplus.le.trans hgeom.1
  have hXsq : X ≤ N ^ 2 := hXNplus.le.trans hgeom.2.2
  have hwidth : X - N ≤ G * (N / (k : ℝ)) := by
    linarith only [hXNplus, hgeom.2.1]
  have hX1 : 1 < X := hN1.trans_le hNX'
  have hWX : W alpha X ≤ (2 * H) * W alpha N := by
    have hp : Real.rpow X alpha ≤ H * Real.rpow N alpha := by
      calc
        Real.rpow X alpha ≤ Real.rpow (H * N) alpha :=
          Real.rpow_le_rpow (by linarith) hXH halpha.le
        _ = Real.rpow H alpha * Real.rpow N alpha := Real.mul_rpow (by linarith) hN0.le
        _ ≤ H * Real.rpow N alpha := by
          apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hN0.le _)
          simpa only [Real.rpow_one, Real.rpow_eq_pow] using
            Real.rpow_le_rpow_of_exponent_le hH halpha1
    have hl : Real.log X ≤ 2 * Real.log N := by
      have hh := Real.log_le_log (by linarith : 0 < X) hXsq
      simpa only [Real.log_pow, Nat.cast_ofNat] using hh
    have hh := mul_le_mul hp hl (Real.log_pos hX1).le
      (mul_nonneg (by linarith : 0 ≤ H) (Real.rpow_nonneg hN0.le _))
    dsimp only [W]
    nlinarith only [hh]
  have hsampleN : -A ≤ W alpha N * S N := hK0 k hk0
  have hmod := pressure_clock_interval_modulus hN1 hNX' (E := C * Real.rpow (H * N) beta)
    (by
      intro u hu
      have hu2 : 2 ≤ u := by linarith [hu.1]
      exact (hclock u hu2).trans
        (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (by linarith) (hu.2.trans hXH) hbeta) hC))
  change |S X - S N| ≤ C * Real.rpow (H * N) beta * (price N - price X) at hmod
  have hprice := price_gap hN1 hNX' hlogN
  have hraw : |S X - S N| ≤
      C * Real.rpow (H * N) beta * (2 * (X - N) / (N ^ 2 * Real.log N)) :=
    hmod.trans (mul_le_mul_of_nonneg_left hprice
      (mul_nonneg hC (Real.rpow_nonneg (mul_nonneg (by linarith) hN0.le) _)))
  have hprod : Real.rpow N alpha * Real.rpow N beta ≤ N * (k : ℝ) :=
    mesh_power_balance r hbalance (show 1 ≤ k by omega)
  have hwidth' : (X - N) * (k : ℝ) ≤ G * N := by
    have hh := (le_div_iff₀ ht).mp (show X - N ≤ G * N / (k : ℝ) by
      simpa only [mul_div_assoc] using hwidth)
    exact hh
  have hnum : (Real.rpow N alpha * Real.rpow N beta) * (X - N) ≤ G * N ^ 2 := by
    have h1 := mul_le_mul_of_nonneg_right hprod (sub_nonneg.mpr hNX')
    have h2 := mul_le_mul_of_nonneg_left hwidth' hN0.le
    nlinarith only [h1, h2]
  have hquot : ((Real.rpow N alpha * Real.rpow N beta) * (X - N)) / N ^ 2 ≤ G :=
    (div_le_iff₀ (pow_pos hN0 2)).mpr hnum
  have hid : W alpha N *
      (C * Real.rpow (H * N) beta * (2 * (X - N) / (N ^ 2 * Real.log N))) =
      E0 * (((Real.rpow N alpha * Real.rpow N beta) * (X - N)) / N ^ 2) := by
    simp only [Real.rpow_eq_pow]
    rw [Real.mul_rpow (by linarith : 0 ≤ H) hN0.le]
    dsimp only [W, E0]
    simp only [Real.rpow_eq_pow]
    field_simp [hN0.ne', (Real.log_pos hN1).ne'] <;> ring
  have herr : W alpha N * |S X - S N| ≤ B0 := by
    calc
      W alpha N * |S X - S N| ≤ W alpha N *
          (C * Real.rpow (H * N) beta * (2 * (X - N) / (N ^ 2 * Real.log N))) :=
        mul_le_mul_of_nonneg_left hraw (w_pos alpha hN1).le
      _ = E0 * (((Real.rpow N alpha * Real.rpow N beta) * (X - N)) / N ^ 2) := hid
      _ ≤ E0 * G := mul_le_mul_of_nonneg_left hquot hE0
  have hlower : -(A + B0) ≤ W alpha N * S X := by
    have hsign := mul_le_mul_of_nonneg_left (neg_le_abs (S X - S N))
      (w_pos alpha hN1).le
    nlinarith only [hsampleN, herr, hsign]
  exact rescale_lower (add_nonneg hA hB0) (by positivity : 0 ≤ 2 * H)
    (w_pos alpha hX1).le hWX hlower


end D5.S3.Arith.Robin.PriceRecord.PolynomialMeshBounds
