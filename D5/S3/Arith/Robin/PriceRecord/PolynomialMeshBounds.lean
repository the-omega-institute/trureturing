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

/-! Pressure interpolation for increasing real meshes, with polynomial specializations. -/

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

lemma power_strictMono (r : ℕ) (hr : 2 ≤ r) : StrictMono (fun k : ℕ => k ^ r) := by
  intro i j hij
  exact pow_lt_pow_left₀ hij (Nat.zero_le i) (by omega : r ≠ 0)

private lemma power_cast_strictMono (r : ℕ) (hr : 2 ≤ r) :
    StrictMono (fun k : ℕ => ((k ^ r : ℕ) : ℝ)) := by
  intro i j hij
  change ((i ^ r : ℕ) : ℝ) < ((j ^ r : ℕ) : ℝ)
  exact_mod_cast (power_strictMono r hr hij : i ^ r < j ^ r)

lemma mesh_atTop {N : ℕ → ℕ} (hN : StrictMono N) :
    Tendsto (fun k : ℕ => (N k : ℝ)) atTop atTop :=
  (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).comp
    hN.tendsto_atTop

lemma power_atTop (r : ℕ) (hr : 2 ≤ r) :
    Tendsto (fun k : ℕ => ((k ^ r : ℕ) : ℝ)) atTop atTop :=
  mesh_atTop (power_strictMono r hr)

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

private lemma mesh_bracket_of_strictMono {mesh : ℕ → ℝ} (hmesh : StrictMono mesh)
    (hmeshTop : Tendsto mesh atTop atTop) (K : ℕ) {X : ℝ} (hX : mesh K ≤ X) :
    ∃ k : ℕ, K ≤ k ∧ mesh k ≤ X ∧ X < mesh (k + 1) := by
  classical
  have hex : ∃ j : ℕ, X < mesh (j + 1) := by
    obtain ⟨j, hj⟩ := eventually_atTop.mp (hmeshTop.eventually (eventually_gt_atTop X))
    exact ⟨j, hj (j + 1) (Nat.le_succ j)⟩
  let k := Nat.find hex
  have hupper : X < mesh (k + 1) := Nat.find_spec hex
  have hK : K ≤ k := by
    by_contra h
    have hle : k + 1 ≤ K := by omega
    exact (not_lt_of_ge ((hmesh.monotone hle).trans hX)) hupper
  refine ⟨k, hK, ?_, hupper⟩
  by_cases hk : k = 0
  · rw [hk]
    exact (hmesh.monotone (Nat.zero_le K)).trans hX
  · have hprev : k - 1 < Nat.find hex := by
      change k - 1 < k
      omega
    have hmin : ¬ X < mesh ((k - 1) + 1) := Nat.find_min hex hprev
    simpa only [Nat.sub_add_cancel (show 1 ≤ k by omega)] using le_of_not_gt hmin

lemma mesh_bracket (r : ℕ) (hr : 2 ≤ r) (K : ℕ) {X : ℝ}
    (hX : ((K ^ r : ℕ) : ℝ) ≤ X) :
    ∃ k : ℕ, K ≤ k ∧ ((k ^ r : ℕ) : ℝ) ≤ X ∧
      X < (((k + 1) ^ r : ℕ) : ℝ) :=
  mesh_bracket_of_strictMono (power_cast_strictMono r hr) (power_atTop r hr) K hX

lemma polynomial_gap (r : ℕ) (hr : 2 ≤ r) :
    ∀ᶠ k : ℕ in atTop, (((k + 1) ^ r : ℕ) : ℝ) - ((k ^ r : ℕ) : ℝ) ≤
      ((r : ℝ) * (2 : ℝ) ^ (r - 1)) *
        Real.rpow ((k ^ r : ℕ) : ℝ) (1 - 1 / (r : ℝ)) := by
  filter_upwards [eventually_ge_atTop (4 : ℕ)] with k hk
  have hr0 : r ≠ 0 := by omega
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hN0 : 0 < ((k ^ r : ℕ) : ℝ) := by
    have hlarge := power_large r hr hk
    exact_mod_cast (show 0 < k ^ r by omega)
  have hroot : Real.rpow ((k ^ r : ℕ) : ℝ) (1 / (r : ℝ)) = (k : ℝ) := by
    simpa only [Nat.cast_pow, Real.rpow_eq_pow, one_div] using
      (Real.pow_rpow_inv_natCast hk0 hr0)
  have hwidth : Real.rpow ((k ^ r : ℕ) : ℝ) (1 - 1 / (r : ℝ)) =
      ((k ^ r : ℕ) : ℝ) / (k : ℝ) := by
    simp only [Real.rpow_eq_pow] at hroot ⊢
    rw [Real.rpow_sub hN0, Real.rpow_one, hroot]
  rw [hwidth]
  exact (mesh_geometry r hr hk).2.1

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

/-- A power-saving gap interpolates a pressure lower bound when the
weight and clock exponents satisfy `alpha + beta - eta ≤ 1`. -/
lemma pressure_mesh_samples_to_all {mesh : ℕ → ℝ} (hmesh : StrictMono mesh)
    (hmeshTop : Tendsto mesh atTop atTop)
    {G eta alpha beta C A : ℝ} (hG : 0 ≤ G) (heta : 0 < eta)
    (halpha : 0 ≤ alpha) (halpha1 : alpha ≤ 1) (hbeta : 0 ≤ beta)
    (hC : 0 ≤ C) (hA : 0 ≤ A) (hbalance : alpha + beta - eta ≤ 1)
    (hgap : ∀ᶠ k : ℕ in atTop,
      mesh (k + 1) - mesh k ≤ G * Real.rpow (mesh k) (1 - eta))
    (hclock : ∀ X : ℝ, 2 ≤ X → |X - clock X| ≤ C * Real.rpow X beta)
    (hsample : ∀ᶠ k : ℕ in atTop,
      -A ≤ (Real.rpow (mesh k) alpha * Real.log (mesh k)) *
        (Real.eulerMascheroniConstant + Real.log (Real.log (mesh k)) -
          1 / Real.log (mesh k) - pressure (price (mesh k)))) :
    ∃ B : ℝ, 0 ≤ B ∧ ∃ T : ℝ, ∀ X : ℝ, T ≤ X →
      -B ≤ (Real.rpow X alpha * Real.log X) *
        (Real.eulerMascheroniConstant + Real.log (Real.log X) -
          1 / Real.log X - pressure (price X)) := by
  let H : ℝ := 1 + G
  let E0 : ℝ := 2 * C * Real.rpow H beta
  let B0 : ℝ := E0 * G
  have hH : 1 ≤ H := by
    dsimp only [H]
    linarith only [hG]
  have hH0 : 0 ≤ H := zero_le_one.trans hH
  have hE0 : 0 ≤ E0 :=
    mul_nonneg (mul_nonneg (by norm_num) hC) (Real.rpow_nonneg hH0 _)
  have hB0 : 0 ≤ B0 := mul_nonneg hE0 hG
  have hlarge : ∀ᶠ k : ℕ in atTop, 3 ≤ mesh k ∧ H ≤ mesh k :=
    (hmeshTop.eventually (eventually_ge_atTop (3 : ℝ))).and
      (hmeshTop.eventually (eventually_ge_atTop H))
  obtain ⟨K, hK⟩ := eventually_atTop.mp (hlarge.and (hgap.and hsample))
  have hScale : 0 ≤ 2 * H := mul_nonneg (by norm_num) hH0
  refine ⟨(2 * H) * (A + B0), mul_nonneg hScale (add_nonneg hA hB0), mesh K, ?_⟩
  intro X hX
  obtain ⟨k, hkK, hNX, hXNplus⟩ := mesh_bracket_of_strictMono hmesh hmeshTop K hX
  obtain ⟨⟨hk3, hkH⟩, hkGap, hkSample⟩ := hK k hkK
  let N : ℝ := mesh k
  have hN3 : 3 ≤ N := hk3
  have hN1 : 1 < N := by linarith
  have hN0 : 0 < N := by linarith
  have hlog3 : 1 < Real.log (3 : ℝ) := by
    simpa only [Nat.cast_ofNat] using (ActualRobinInterval.log_gt_one (n := 3) le_rfl)
  have hlogN : 1 ≤ Real.log N := hlog3.le.trans (Real.log_le_log (by norm_num) hN3)
  have hNX' : N ≤ X := hNX
  have hwidth : X - N ≤ G * Real.rpow N (1 - eta) :=
    (sub_le_sub_right hXNplus.le N).trans hkGap
  have hwidthN : X - N ≤ G * N := by
    apply hwidth.trans
    apply mul_le_mul_of_nonneg_left _ hG
    simpa only [Real.rpow_eq_pow, Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hN1.le (show 1 - eta ≤ 1 by linarith)
  have hXH : X ≤ H * N := by
    dsimp only [H]
    nlinarith only [hwidthN]
  have hXsq : X ≤ N ^ 2 := hXH.trans (by
    simpa only [pow_two] using mul_le_mul_of_nonneg_right hkH hN0.le)
  have hX1 : 1 < X := hN1.trans_le hNX'
  have hWX : W alpha X ≤ (2 * H) * W alpha N := by
    have hp : Real.rpow X alpha ≤ H * Real.rpow N alpha := by
      calc
        Real.rpow X alpha ≤ Real.rpow (H * N) alpha :=
          Real.rpow_le_rpow (hN0.le.trans hNX') hXH halpha
        _ = Real.rpow H alpha * Real.rpow N alpha := Real.mul_rpow hH0 hN0.le
        _ ≤ H * Real.rpow N alpha := by
          apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hN0.le _)
          simpa only [Real.rpow_one, Real.rpow_eq_pow] using
            Real.rpow_le_rpow_of_exponent_le hH halpha1
    have hl : Real.log X ≤ 2 * Real.log N := by
      have hh := Real.log_le_log (by linarith : 0 < X) hXsq
      simpa only [Real.log_pow, Nat.cast_ofNat] using hh
    have hh := mul_le_mul hp hl (Real.log_pos hX1).le
      (mul_nonneg hH0 (Real.rpow_nonneg hN0.le _))
    dsimp only [W]
    nlinarith only [hh]
  have hsampleN : -A ≤ W alpha N * S N := hkSample
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
      (mul_nonneg hC (Real.rpow_nonneg (mul_nonneg hH0 hN0.le) _)))
  have hnum : (Real.rpow N alpha * Real.rpow N beta) * (X - N) ≤ G * N ^ 2 := by
    calc
      _ ≤ (Real.rpow N alpha * Real.rpow N beta) * (G * Real.rpow N (1 - eta)) :=
        mul_le_mul_of_nonneg_left hwidth
          (mul_nonneg (Real.rpow_nonneg hN0.le _) (Real.rpow_nonneg hN0.le _))
      _ = G * Real.rpow N (alpha + beta + (1 - eta)) := by
        simp only [Real.rpow_eq_pow, Real.rpow_add hN0]
        ring
      _ ≤ G * N ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ hG
        have hb := Real.rpow_le_rpow_of_exponent_le hN1.le
          (show alpha + beta + (1 - eta) ≤ (2 : ℝ) by linarith only [hbalance])
        simpa only [Real.rpow_eq_pow, Real.rpow_two] using hb
  have hquot : ((Real.rpow N alpha * Real.rpow N beta) * (X - N)) / N ^ 2 ≤ G :=
    (div_le_iff₀ (pow_pos hN0 2)).mpr hnum
  have hid : W alpha N *
      (C * Real.rpow (H * N) beta * (2 * (X - N) / (N ^ 2 * Real.log N))) =
      E0 * (((Real.rpow N alpha * Real.rpow N beta) * (X - N)) / N ^ 2) := by
    simp only [Real.rpow_eq_pow]
    rw [Real.mul_rpow hH0 hN0.le]
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
  exact rescale_lower (add_nonneg hA hB0) hScale
    (w_pos alpha hX1).le hWX hlower

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
  have hr0 : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  exact pressure_mesh_samples_to_all (power_cast_strictMono r hr) (power_atTop r hr)
    (G := (r : ℝ) * (2 : ℝ) ^ (r - 1)) (eta := 1 / (r : ℝ)) (alpha := 1 - sigma)
    (by positivity) (one_div_pos.mpr hr0) (by linarith) (by linarith) hbeta hC hA
    (by linarith only [hgap]) (polynomial_gap r hr) hclock hsample

end D5.S3.Arith.Robin.PriceRecord.PolynomialMeshBounds
