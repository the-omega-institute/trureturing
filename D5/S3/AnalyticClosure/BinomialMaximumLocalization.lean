/- GID: D5/S3/AnalyticClosure/BinomialMaximumLocalization
   generality: G
   mirror-B: D5/B/S3/AnalyticClosure/BinomialMaximumLocalization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Global localization and floor comparison for weighted binomial prefix maxima. -/

import D5.S3.AnalyticClosure.BinomialMovingEndpoint
import D5.S3.AnalyticClosure.BinomialLocalGaussian
import Mathlib.Algebra.Order.Floor.Semiring

open Filter Real Finset
open scoped Topology
open D5.S3.AnalyticClosure.BinomialLocalGaussian

namespace D5.S3.AnalyticClosure.BinomialMaximumLocalization

/-- The weighted prefix whose maximum is taken over `0 ≤ r ≤ m`. -/
noncomputable def prefixValue (a : ℝ) (l m r : ℕ) : ℝ :=
  (∑ i ∈ range (r + 1), ((m.choose i : ℝ) * a ^ i) ^ l) / (1 + a) ^ (r * l)

/-- The floor endpoint has the full positive asymptotic constant. This supplies
a lower comparison for every maximizing index, for all fixed `a > 0` and `l > 0`.
No assertion about the exact maximizing index is used. -/
theorem floor_comparison (a : ℝ) (ha : 0 < a) (l : ℕ) (hl : 0 < l) :
    let q := a / (1 + 2 * a)
    Tendsto (fun m : ℕ =>
      prefixValue a l m ⌊(m : ℝ) * q⌋₊ / ((1 + 2 * a) / (1 + a)) ^ (m * l) *
        (sqrt (2 * π * m * q * (1 - q))) ^ l)
      atTop (𝓝 ((1 - ((1 + a)⁻¹) ^ l)⁻¹)) := by
  dsimp only
  let q := a / (1 + 2 * a)
  let r (m : ℕ) := ⌊(m : ℝ) * q⌋₊
  have hq : 0 < q := by dsimp [q]; positivity
  have hq1 : q < 1 := by dsimp [q]; apply (div_lt_one (by positivity)).2; linarith
  have hqa : q < a / (1 + a) := by
    dsimp [q]
    exact div_lt_div_of_pos_left ha (by positivity) (by linarith)
  have hm : Tendsto (fun m : ℕ => (m : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have herr (m : ℕ) : |(r m : ℝ) - m * q| ≤ 1 :=
    Nat.abs_floor_sub_le (by positivity)
  have hrle (m : ℕ) : r m ≤ m :=
    Nat.floor_le_of_le (by nlinarith [Nat.cast_nonneg (α := ℝ) m])
  have hd : Tendsto (fun m : ℕ => ((r m : ℝ) - m * q) / m) atTop (𝓝 0) := by
    apply squeeze_zero_norm' (Eventually.of_forall fun m => ?_)
      (tendsto_const_nhds.div_atTop hm : Tendsto (fun m : ℕ => (1 : ℝ) / m) atTop (𝓝 0))
    rw [Real.norm_eq_abs, abs_div, Nat.abs_cast]
    exact div_le_div_of_nonneg_right (herr m) (Nat.cast_nonneg m)
  have hr : Tendsto (fun m : ℕ => (r m : ℝ) / m) atTop (𝓝 q) := by
    have ht : Tendsto (fun m : ℕ => ((r m : ℝ) - m * q) / m + q) atTop (𝓝 q) :=
      by simpa only [zero_add] using hd.add_const q
    apply ht.congr'
    filter_upwards [eventually_gt_atTop 0] with m hm0
    have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm0.ne'
    field_simp
    ring
  have hwindow : ∀ᶠ m : ℕ in atTop,
      |(r m : ℝ) - m * q| ≤ (m : ℝ) ^ (7 / 12 : ℝ) := by
    filter_upwards [eventually_ge_atTop 1] with m hm1
    exact (herr m).trans (one_le_rpow (by exact_mod_cast hm1) (by norm_num))
  have hgauss : Tendsto (fun m : ℕ => binomialMass q m (r m) *
      sqrt (2 * π * m * q * (1 - q)) *
      exp (((r m : ℝ) - m * q) ^ 2 / (2 * m * q * (1 - q)))) atTop (𝓝 1) := by
    apply Metric.tendsto_atTop.mpr
    intro ε hε
    obtain ⟨N, hN⟩ := local_gaussian_window q hq hq1 ε hε
    obtain ⟨K, hK⟩ := eventually_atTop.mp hwindow
    exact ⟨max N K, fun m hm => by
      simpa only [Real.dist_eq] using hN m ((le_max_left _ _).trans hm) (r m)
        (hK m ((le_max_right _ _).trans hm))⟩
  have hcorr : Tendsto (fun m : ℕ =>
      ((r m : ℝ) - m * q) ^ 2 / (2 * m * q * (1 - q))) atTop (𝓝 0) := by
    have hzero : Tendsto (fun m : ℕ => (1 / (2 * q * (1 - q))) / m) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hm
    apply squeeze_zero (fun m => by positivity) (fun m => ?_) hzero
    calc
      _ ≤ 1 / (2 * m * q * (1 - q)) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        have hs := (sq_le_sq₀ (abs_nonneg ((r m : ℝ) - m * q)) zero_le_one).2 (herr m)
        simpa only [sq_abs, one_pow] using hs
      _ = _ := by rw [div_div]; congr 1; ring
  have hmass : Tendsto (fun m : ℕ => binomialMass q m (r m) *
      sqrt (2 * π * m * q * (1 - q))) atTop (𝓝 1) := by
    have he : Tendsto (fun m : ℕ => exp
        (((r m : ℝ) - m * q) ^ 2 / (2 * m * q * (1 - q)))) atTop (𝓝 1) :=
      by
        have hexp : Tendsto Real.exp (𝓝 (0 : ℝ)) (𝓝 1) :=
          by simpa only [exp_zero] using Real.continuous_exp.tendsto 0
        exact hexp.comp hcorr
    convert hgauss.div he one_ne_zero using 1
    · ext m
      exact (mul_div_cancel_right₀ _ (exp_ne_zero _)).symm
    · simp
  have he := BinomialMovingEndpoint.moving_endpoint_sum a q ha hq hqa l hl r hr
  have hratio : q / (a * (1 - q)) = (1 + a)⁻¹ := by
    have hcomp : 1 - q = (1 + a) / (1 + 2 * a) := by
      dsimp [q]; field_simp; ring
    rw [hcomp, inv_eq_one_div]
    dsimp [q]
    field_simp
  rw [hratio] at he
  have ht := he.mul (hmass.pow l)
  simp only [one_pow, mul_one] at ht
  apply ht.congr'
  filter_upwards with m
  have htilt : binomialMass q m (r m) =
      ((m.choose (r m) : ℝ) * a ^ r m) /
        ((1 + a) ^ r m * ((1 + 2 * a) / (1 + a)) ^ m) := by
    have hcomp : 1 - q = (1 + a) / (1 + 2 * a) := by
      dsimp [q]; field_simp; ring
    have hmadd : r m + (m - r m) = m := Nat.add_sub_of_le (hrle m)
    rw [binomialMass, hcomp]
    dsimp only [q]
    rw [div_pow, div_pow, div_pow]
    have hb : (1 + a) ≠ 0 := by positivity
    have hc : (1 + 2 * a) ≠ 0 := by positivity
    have hbp := pow_add (1 + a) (r m) (m - r m)
    have hcp := pow_add (1 + 2 * a) (r m) (m - r m)
    rw [hmadd] at hbp hcp
    field_simp
    rw [hbp, hcp]
    ring
  have hw : (m.choose (r m) : ℝ) * a ^ r m ≠ 0 :=
    (mul_pos (by exact_mod_cast Nat.choose_pos (hrle m)) (pow_pos ha _)).ne'
  rw [htilt]
  change (∑ i ∈ range (r m + 1), ((m.choose i : ℝ) * a ^ i) ^ l) /
      ((m.choose (r m) : ℝ) * a ^ r m) ^ l *
      ((((m.choose (r m) : ℝ) * a ^ r m) /
        ((1 + a) ^ r m * ((1 + 2 * a) / (1 + a)) ^ m)) *
        sqrt (2 * π * m * q * (1 - q))) ^ l = _
  simp only [prefixValue, mul_pow, div_pow, ← pow_mul]
  change _ = (∑ i ∈ range (r m + 1), (m.choose i : ℝ) ^ l * a ^ (i * l)) /
    (1 + a) ^ (r m * l) / ((1 + 2 * a) ^ (m * l) / (1 + a) ^ (m * l)) *
      sqrt (2 * π * m * q * (1 - q)) ^ l
  have hc : (m.choose (r m) : ℝ) ≠ 0 :=
    (by exact_mod_cast Nat.choose_pos (hrle m) : (0 : ℝ) < m.choose (r m)).ne'
  field_simp

/-- Uniform exponential separation from the maximizing slope. The estimate
includes both boundary indices and does not require monotonicity of the prefix.
The two costs are Bernoulli Pinsker deviation and the distance paid by the tilt. -/
theorem separated_prefix_bound (a : ℝ) (ha : 0 < a) (l : ℕ)
    (ε : ℝ) (hε : 0 < ε) (m r : ℕ) (hm : 0 < m) (hr : r ≤ m)
    (hfar : ε ≤ |(r : ℝ) / m - a / (1 + 2 * a)|) :
    prefixValue a l m r / ((1 + 2 * a) / (1 + a)) ^ (m * l) ≤
      (m + 1 : ℝ) * exp (-(l : ℝ) * m *
        min (ε ^ 2 / 2) (ε * log (1 + a) / 2)) := by
  let q := a / (1 + 2 * a)
  have hq : 0 < q := by dsimp [q]; positivity
  have hq1 : q < 1 := by dsimp [q]; apply (div_lt_one (by positivity)).2; linarith
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hb : 0 < 1 + a := by positivity
  have hd : 0 < 1 + 2 * a := by positivity
  have hlog : 0 < log (1 + a) := log_pos (by linarith)
  have hcomp : 1 - q = (1 + a) / (1 + 2 * a) := by
    dsimp [q]; field_simp; ring
  -- The pointwise entropy estimate is needed here at all indices, including
  -- the endpoints. The existing power-tail theorem only exports a summed tail.
  have hmass_bound (i : ℕ) (hi : i ≤ m) :
      binomialMass q m i ≤ exp (-2 * m * ((i : ℝ) / m - q) ^ 2) := by
    let x : ℝ := (i : ℝ) / m
    have hx0 : 0 ≤ x := div_nonneg (Nat.cast_nonneg _) hmR.le
    have hx1 : x ≤ 1 := (div_le_one hmR).2 (by exact_mod_cast hi)
    have hmass : 0 < binomialMass q m i := by
      unfold binomialMass
      exact mul_pos (mul_pos (by exact_mod_cast Nat.choose_pos hi) (pow_pos hq _))
        (pow_pos (sub_pos.mpr hq1) _)
    have hsum : ∑ j ∈ range (m + 1), binomialMass x m j = 1 := by
      have hs := (add_pow x (1 - x) m).symm
      simpa [binomialMass, mul_comm, mul_left_comm, mul_assoc] using hs
    have hle : binomialMass x m i ≤ 1 := by
      rw [← hsum]
      unfold binomialMass
      refine single_le_sum (s := range (m + 1))
        (f := fun j : ℕ => (m.choose j : ℝ) * x ^ j * (1 - x) ^ (m - j)) ?_ ?_
      · intro j _
        exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hx0 _))
          (pow_nonneg (sub_nonneg.mpr hx1) _)
      · exact mem_range.mpr (Nat.lt_succ_of_le hi)
    have hid : log (binomialMass q m i) = log (binomialMass x m i) - m * binaryKL x q := by
      by_cases hi0 : i = 0
      · subst i
        simp [x, binomialMass, binaryKL, log_pow]
      by_cases him : i = m
      · subst i
        simp [x, hm.ne', binomialMass, binaryKL, log_pow]
      have hiR : (0 : ℝ) < i := by exact_mod_cast Nat.pos_of_ne_zero hi0
      have hxp : 0 < x := div_pos hiR hmR
      have hxn : 0 < 1 - x :=
        sub_pos.mpr ((div_lt_one hmR).2 (by exact_mod_cast lt_of_le_of_ne hi him))
      have hc : (0 : ℝ) < m.choose i := by exact_mod_cast Nat.choose_pos hi
      have hnp : 0 < 1 - q := sub_pos.mpr hq1
      simp only [binomialMass,
        log_mul (mul_pos hc (pow_pos hq _)).ne' (pow_pos hnp _).ne',
        log_mul hc.ne' (pow_pos hq _).ne',
        log_mul (mul_pos hc (pow_pos hxp _)).ne' (pow_pos hxn _).ne',
        log_mul hc.ne' (pow_pos hxp _).ne', log_pow,
        binaryKL, log_div hxp.ne' hq.ne', log_div hxn.ne' hnp.ne']
      rw [Nat.cast_sub hi]
      dsimp [x]
      field_simp
      ring
    have hxmass : 0 < binomialMass x m i := by
      by_cases hi0 : i = 0
      · simp [x, hi0, binomialMass]
      by_cases him : i = m
      · simp [x, him, hm.ne', binomialMass]
      have hxp : 0 < x := div_pos (by exact_mod_cast Nat.pos_of_ne_zero hi0) hmR
      have hxn : 0 < 1 - x :=
        sub_pos.mpr ((div_lt_one hmR).2 (by exact_mod_cast lt_of_le_of_ne hi him))
      exact mul_pos (mul_pos (by exact_mod_cast Nat.choose_pos hi) (pow_pos hxp _))
        (pow_pos hxn _)
    have hlogle : log (binomialMass q m i) ≤ -m * binaryKL x q := by
      rw [hid]
      have := log_nonpos hxmass.le hle
      linarith
    have hpin := D5.S3.TotalVariation.Pinsker.binary_pinsker x q ⟨hx0, hx1⟩ ⟨hq.le, hq1.le⟩
      (fun h => (hq.ne' h).elim) (fun h => ((sub_pos.mpr hq1).ne' h).elim)
    apply (log_le_iff_le_exp hmass).mp
    have := mul_le_mul_of_nonneg_left hpin hmR.le
    dsimp [binaryKL] at hlogle
    nlinarith
  let c := min (ε ^ 2 / 2) (ε * log (1 + a) / 2)
  have hterm (i : ℕ) (hi : i ≤ r) :
      ((m.choose i : ℝ) * a ^ i / ((1 + a) ^ r * ((1 + 2 * a) / (1 + a)) ^ m)) ^ l ≤
        exp (-(l : ℝ) * m * c) := by
    have him := hi.trans hr
    have htilt : (m.choose i : ℝ) * a ^ i /
        ((1 + a) ^ r * ((1 + 2 * a) / (1 + a)) ^ m) =
        binomialMass q m i / (1 + a) ^ (r - i) := by
      rw [binomialMass, hcomp]
      dsimp only [q]
      rw [div_pow, div_pow, div_pow]
      have hbp : (1 + a) ^ m = (1 + a) ^ i * (1 + a) ^ (m - i) :=
        by rw [← pow_add, Nat.add_sub_of_le him]
      have hcp : (1 + 2 * a) ^ m = (1 + 2 * a) ^ i * (1 + 2 * a) ^ (m - i) :=
        by rw [← pow_add, Nat.add_sub_of_le him]
      have hbr : (1 + a) ^ r = (1 + a) ^ i * (1 + a) ^ (r - i) :=
        by rw [← pow_add, Nat.add_sub_of_le hi]
      field_simp
      simp only [mul_comm (2 : ℝ) a] at hcp
      rw [hbp, hcp, hbr]
      ring
    let x := (i : ℝ) / m
    let t := (r : ℝ) / m - x
    have ht0 : 0 ≤ t := sub_nonneg.mpr (div_le_div_of_nonneg_right
      (by exact_mod_cast hi) hmR.le)
    have habs : ε ≤ |x - q| + t := by
      calc
        ε ≤ |(r : ℝ) / m - q| := hfar
        _ = |(x - q) + t| := by congr 1; dsimp [t]; ring
        _ ≤ |x - q| + |t| := abs_add_le _ _
        _ = _ := by rw [abs_of_nonneg ht0]
    have hcost : c ≤ 2 * (x - q) ^ 2 + t * log (1 + a) := by
      by_cases hx : ε / 2 ≤ |x - q|
      · have hs := mul_self_le_mul_self (by positivity : 0 ≤ ε / 2) hx
        have hc := min_le_left (ε ^ 2 / 2) (ε * log (1 + a) / 2)
        have htlog := mul_nonneg ht0 hlog.le
        dsimp [c]
        nlinarith [sq_abs (x - q)]
      · have ht : ε / 2 ≤ t := by linarith
        have hc := min_le_right (ε ^ 2 / 2) (ε * log (1 + a) / 2)
        have htlog := mul_le_mul_of_nonneg_right ht hlog.le
        dsimp [c]
        nlinarith [sq_nonneg (x - q)]
    have hdist : ((r - i : ℕ) : ℝ) = m * t := by
      rw [Nat.cast_sub hi]
      dsimp [t, x]
      field_simp
    have hexponent : -2 * m * (x - q) ^ 2 - (r - i : ℕ) * log (1 + a) ≤ -m * c := by
      rw [hdist]
      nlinarith [mul_le_mul_of_nonneg_left hcost hmR.le]
    rw [htilt]
    calc
      _ ≤ (exp (-2 * m * (x - q) ^ 2) / (1 + a) ^ (r - i)) ^ l :=
        pow_le_pow_left₀ (by unfold binomialMass; positivity)
          (div_le_div_of_nonneg_right (hmass_bound i him) (by positivity)) _
      _ = exp ((l : ℝ) * (-2 * m * (x - q) ^ 2 - (r - i : ℕ) * log (1 + a))) := by
        rw [exp_nat_mul, exp_sub, exp_nat_mul, exp_log hb]
      _ ≤ _ := exp_le_exp.mpr (by
        nlinarith [mul_le_mul_of_nonneg_left hexponent (Nat.cast_nonneg (α := ℝ) l)])
  have hsum : prefixValue a l m r / ((1 + 2 * a) / (1 + a)) ^ (m * l) =
      ∑ i ∈ range (r + 1),
        ((m.choose i : ℝ) * a ^ i / ((1 + a) ^ r * ((1 + 2 * a) / (1 + a)) ^ m)) ^ l := by
    simp only [prefixValue, div_pow, mul_pow, ← pow_mul, ← sum_div, div_div]
  rw [hsum]
  calc
    _ ≤ ∑ _i ∈ range (r + 1), exp (-(l : ℝ) * m * c) :=
      sum_le_sum fun i hi => hterm i (Nat.le_of_lt_succ (mem_range.mp hi))
    _ = (r + 1 : ℝ) * exp (-(l : ℝ) * m * c) := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.add_le_add_right hr 1)
      (exp_pos _).le

/-- Every choice of global maximizing indices has slope `a / (1 + 2*a)`.
Along any such choice, the accepted moving-endpoint theorem therefore gives
the same geometric factor as at the floor comparison. This does not assert
the Gaussian prefactor at the maximizing index or the exact maximum asymptotic. -/
theorem maximizer_slope_and_endpoint (a : ℝ) (ha : 0 < a) (l : ℕ) (hl : 0 < l)
    (r : ℕ → ℕ) (hr : ∀ m, r m ≤ m)
    (hmax : ∀ m j, j ≤ m → prefixValue a l m j ≤ prefixValue a l m (r m)) :
    Tendsto (fun m : ℕ => (r m : ℝ) / m) atTop (𝓝 (a / (1 + 2 * a))) ∧
    Tendsto (fun m : ℕ =>
      (∑ i ∈ range (r m + 1), ((m.choose i : ℝ) * a ^ i) ^ l) /
        ((m.choose (r m) : ℝ) * a ^ r m) ^ l)
      atTop (𝓝 ((1 - ((1 + a)⁻¹) ^ l)⁻¹)) := by
  let q := a / (1 + 2 * a)
  let L := (1 - ((1 + a)⁻¹) ^ l)⁻¹
  have hq : 0 < q := by dsimp [q]; positivity
  have hq1 : q < 1 := by dsimp [q]; apply (div_lt_one (by positivity)).2; linarith
  have hb : 0 < 1 + a := by positivity
  have hinv : (1 + a)⁻¹ < 1 := by
    rw [inv_eq_one_div]
    exact (div_lt_one hb).2 (by linarith)
  have hL : 0 < L := by
    exact inv_pos.mpr (sub_pos.mpr (pow_lt_one₀ (by positivity) hinv (by omega)))
  have hfloor := floor_comparison a ha l hl
  change Tendsto (fun m : ℕ =>
    prefixValue a l m ⌊(m : ℝ) * q⌋₊ / ((1 + 2 * a) / (1 + a)) ^ (m * l) *
      sqrt (2 * π * m * q * (1 - q)) ^ l) atTop (𝓝 L) at hfloor
  have hlow := hfloor.eventually (lt_mem_nhds (show L / 2 < L by linarith))
  have hslope : Tendsto (fun m : ℕ => (r m : ℝ) / m) atTop (𝓝 q) := by
    apply Metric.tendsto_atTop.mpr
    intro ε hε
    let c := min (ε ^ 2 / 2) (ε * log (1 + a) / 2)
    have hc : 0 < c := lt_min (by positivity)
      (div_pos (mul_pos hε (log_pos (by linarith))) (by norm_num))
    have hlc : 0 < (l : ℝ) * c := mul_pos (by exact_mod_cast hl) hc
    have hm : Tendsto (fun m : ℕ => (m : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
    have hupper : Tendsto (fun m : ℕ =>
        (m + 1 : ℝ) * exp (-(l : ℝ) * m * c) *
          sqrt (2 * π * m * q * (1 - q)) ^ l) atTop (𝓝 0) := by
      let C := 2 * π * q * (1 - q)
      have hC : 0 < C := by dsimp [C]; positivity
      have h0 := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
        ((l : ℝ) / 2) ((l : ℝ) * c) hlc).comp hm
      have h1 := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
        ((l : ℝ) / 2 + 1) ((l : ℝ) * c) hlc).comp hm
      have ht := (h1.add h0).const_mul (sqrt C ^ l)
      simp only [add_zero, mul_zero] at ht
      apply ht.congr'
      filter_upwards [eventually_gt_atTop 0] with m hm0
      have hmR : (0 : ℝ) < m := by exact_mod_cast hm0
      have hprod : 2 * π * (m : ℝ) * q * (1 - q) = C * m := by dsimp [C]; ring
      dsimp only [Function.comp_apply]
      rw [hprod, sqrt_mul hC.le, mul_pow, sqrt_eq_rpow (m : ℝ),
        ← rpow_mul_natCast hmR.le]
      rw [show (1 / 2 : ℝ) * l = (l : ℝ) / 2 by ring, rpow_add hmR, rpow_one]
      rw [show -(l : ℝ) * m * c = -((l : ℝ) * c) * m by ring]
      ring
    have hup := hupper.eventually (gt_mem_nhds (show (0 : ℝ) < L / 2 by positivity))
    obtain ⟨N, hN⟩ := eventually_atTop.mp (hlow.and (hup.and (eventually_gt_atTop 0)))
    refine ⟨N, fun m hmN => ?_⟩
    rw [Real.dist_eq]
    by_contra hnot
    have hfar : ε ≤ |(r m : ℝ) / m - q| := le_of_not_gt hnot
    have hbound := separated_prefix_bound a ha l ε hε m (r m) (hN m hmN).2.2 (hr m) hfar
    have hfloorm : ⌊(m : ℝ) * q⌋₊ ≤ m :=
      Nat.floor_le_of_le (by nlinarith [Nat.cast_nonneg (α := ℝ) m])
    have hcompare := mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right (hmax m _ hfloorm)
        (show 0 ≤ ((1 + 2 * a) / (1 + a)) ^ (m * l) by positivity))
      (show 0 ≤ sqrt (2 * π * m * q * (1 - q)) ^ l by positivity)
    have hbound' := mul_le_mul_of_nonneg_right hbound
      (show 0 ≤ sqrt (2 * π * m * q * (1 - q)) ^ l by positivity)
    have hlo := (hN m hmN).1
    have hhi := (hN m hmN).2.1
    change _ < L / 2 at hhi
    change _ ≤ (m + 1 : ℝ) * exp (-(l : ℝ) * m * c) *
      sqrt (2 * π * m * q * (1 - q)) ^ l at hbound'
    linarith
  refine ⟨hslope, ?_⟩
  have hqa : q < a / (1 + a) := by
    dsimp [q]
    exact div_lt_div_of_pos_left ha (by positivity) (by linarith)
  have ht := BinomialMovingEndpoint.moving_endpoint_sum a q ha hq hqa l hl r hslope
  have hratio : q / (a * (1 - q)) = (1 + a)⁻¹ := by
    have hcomp : 1 - q = (1 + a) / (1 + 2 * a) := by
      dsimp [q]; field_simp; ring
    rw [hcomp, inv_eq_one_div]
    dsimp [q]
    field_simp
  rwa [hratio] at ht

end D5.S3.AnalyticClosure.BinomialMaximumLocalization
