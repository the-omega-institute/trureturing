/- GID: D5/S3/CharacterSums/ClippedWindowBadSet
   generality: G
   mirror-B: D5/B/S3/CharacterSums/ClippedWindowBadSet
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Uniform second moments for clipped sums control exceptional sets on full windows. -/

import D5.S3.Arith.Robin.ForwardKernel.VarianceTransfer
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic

/-! Finite real knots and arbitrary complex coefficient arrays suffice. No arithmetic
property or size bound of the coefficient array is needed beyond the uniform moment hypothesis. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Finset Filter MeasureTheory Real
open scoped Topology
namespace D5.S3.CharacterSums.ClippedWindowBadSet

/-- A finite clipped sum with real knots and an index multiplier. -/
def clippedSum {α : Type*} {ι : Type*} (T : Finset ι) (h : ι → ℝ) (a : ι → α → ℂ)
    (y : ℝ) (q : α) (κ : ι → ℂ) : ℂ :=
  ∑ n ∈ T, ((min 1 (y / h n) : ℝ) : ℂ) * κ n * a n q

private def slope {α : Type*} {ι : Type*} (T : Finset ι) (h : ι → ℝ) (a : ι → α → ℂ)
    (y : ℝ) (q : α) (κ : ι → ℂ) : ℂ :=
  ∑ n ∈ T, if y < h n then κ n * a n q / h n else 0

variable {α : Type*} {ι : Type*} {T : Finset ι} {h : ι → ℝ} {a : ι → α → ℂ}

private lemma slope_integrable (q : α) (κ : ι → ℂ) (u v : ℝ) :
    IntervalIntegrable (fun y => slope T h a y q κ) volume u v ∧
    IntervalIntegrable (fun y => ‖slope T h a y q κ‖ ^ 2) volume u v := by
  let M := ∑ n ∈ T, ‖κ n * a n q / h n‖
  have hb (y : ℝ) : ‖slope T h a y q κ‖ ≤ M := by
    apply (norm_sum_le _ _).trans
    apply sum_le_sum
    intro n hn
    split_ifs
    · exact le_rfl
    · simpa only [norm_zero] using norm_nonneg (κ n * a n q / h n)
  have hm : Measurable (fun y => slope T h a y q κ) := by
    unfold slope
    exact Finset.measurable_sum T fun n _ =>
      Measurable.ite measurableSet_Iio measurable_const measurable_const
  constructor
  · exact IntervalIntegrable.mono_fun' (g := fun _ => M) intervalIntegrable_const
      hm.aestronglyMeasurable (Eventually.of_forall hb)
  · apply IntervalIntegrable.mono_fun' (g := fun _ => M ^ 2) intervalIntegrable_const
      (hm.norm.pow_const 2).aestronglyMeasurable
    exact Eventually.of_forall fun y => by
      simpa only [norm_pow, norm_norm] using pow_le_pow_left₀ (norm_nonneg _) (hb y) 2

private lemma clippedSum_increment (hp : ∀ n ∈ T, 0 < h n) (q : α)
    (κ : ι → ℂ) (u v : ℝ) :
    clippedSum T h a v q κ = clippedSum T h a u q κ +
      ∫ y in u..v, slope T h a y q κ := by
  have hc : Continuous (fun y => clippedSum T h a y q κ) := by
    unfold clippedSum
    fun_prop
  have hd (x : ℝ) : HasDerivWithinAt (fun y => clippedSum T h a y q κ)
      (slope T h a x q κ) (Set.Ioi x) x := by
    unfold clippedSum slope
    apply HasDerivWithinAt.fun_sum
    intro n hn
    have hp' := hp n hn
    by_cases hx : x < h n
    · have he : (fun y : ℝ => min 1 (y / h n)) =ᶠ[𝓝 x] fun y => y / h n := by
        filter_upwards [Iio_mem_nhds hx] with y hy
        exact min_eq_right ((div_le_one hp').2 hy.le)
      have H := ((hasDerivAt_id x).div_const (h n)).congr_of_eventuallyEq he
      convert ((H.hasDerivWithinAt.ofReal_comp.mul_const (κ n)).mul_const (a n q)) using 1
      simp only [hx, ite_true, one_div, Complex.ofReal_inv]
      ring
    · have hx' : h n ≤ x := le_of_not_gt hx
      have H : HasDerivWithinAt (fun y : ℝ => min 1 (y / h n)) 0 (Set.Ioi x) x := by
        apply (hasDerivAt_const x (1 : ℝ)).hasDerivWithinAt.congr
        · intro y hy
          exact min_eq_left ((one_le_div hp').2 (hx'.trans hy.le))
        · exact min_eq_left ((one_le_div hp').2 hx')
      convert ((H.ofReal_comp.mul_const (κ n)).mul_const (a n q)) using 1 <;> simp [hx]
  have H := intervalIntegral.integral_eq_sub_of_hasDeriv_right
    hc.continuousOn (fun x _ => hd x) (slope_integrable (T := T) (h := h) (a := a) q κ u v).1
  linear_combination -H

private lemma integral_square_bound {f : ℝ → ℝ} {u v : ℝ} (huv : u ≤ v)
    (hi : IntervalIntegrable f volume u v)
    (hi2 : IntervalIntegrable (fun x => f x ^ 2) volume u v) :
    (∫ x in u..v, f x) ^ 2 ≤ (v-u) * ∫ x in u..v, f x ^ 2 := by
  rcases huv.eq_or_lt with rfl | huv
  · simp
  have H := D5.S3.Arith.Robin.ForwardKernel.VarianceTransfer.interval_cauchy_schwarz
    (sub_pos.mpr huv) (by simpa using hi.comp_add_right u)
    (by simpa using hi2.comp_add_right u)
  have htrans : (∫ x in (0 : ℝ)..v-u, f (x+u)^2) = ∫ x in u..v, f x^2 := by
    simpa only [zero_add, sub_add_cancel] using
      intervalIntegral.integral_comp_add_right (a := 0) (b := v-u) (fun x => f x^2) u
  rw [htrans] at H
  simpa only [intervalIntegral.integral_comp_add_right, zero_add, sub_add_cancel] using H

private lemma selected_block_bound (hp : ∀ n ∈ T, 0 < h n)
    {C u v : ℝ} {P : Finset α} (hC : 0 ≤ C) (hu : 1 ≤ u) (huv : u ≤ v)
    (hv : v ≤ 2*u)
    (hm : ∀ y ∈ Set.Icc u v, ∀ κ : ι → ℂ, (∀ n ∈ T, ‖κ n‖ ≤ 1) →
      ∑ q ∈ P, ‖clippedSum T h a y q κ‖ ^ 2 ≤ C*y*log y*P.card)
    {κ : ι → ℂ} (hκ : ∀ n ∈ T, ‖κ n‖ ≤ 1) (w : α → ℝ)
    (hw : ∀ q, w q ∈ Set.Icc u v) :
    ∑ q ∈ P, ‖clippedSum T h a (w q) q κ‖ ^ 2 ≤
      4*C*u*log (2*u)*P.card := by
  have hu0 : 0 < u := by linarith
  have hlog0 : 0 ≤ log (2*u) := log_nonneg (by linarith)
  have hb (q : α) : ‖clippedSum T h a (w q) q κ‖ ^ 2 ≤
      2*‖clippedSum T h a u q κ‖ ^ 2 +
        2*u*(∫ y in u..v, ‖slope T h a y q κ‖ ^ 2) := by
    have hwu := (hw q).1
    have hwv := (hw q).2
    have H := integral_square_bound hwu
      (slope_integrable (T := T) (h := h) (a := a) q κ u (w q)).1.norm
      (slope_integrable (T := T) (h := h) (a := a) q κ u (w q)).2
    have Hn := intervalIntegral.norm_integral_le_integral_norm (μ := volume)
      (f := fun y => slope T h a y q κ) hwu
    have Ht : ‖clippedSum T h a (w q) q κ‖ ≤ ‖clippedSum T h a u q κ‖ +
        ∫ y in u..w q, ‖slope T h a y q κ‖ := by
      rw [clippedSum_increment hp q κ u (w q)]
      exact (norm_add_le _ _).trans (add_le_add le_rfl Hn)
    have Hsq := pow_le_pow_left₀ (norm_nonneg _) Ht 2
    have HI := intervalIntegral.integral_add_adjacent_intervals
      (slope_integrable (T := T) (h := h) (a := a) q κ u (w q)).2
      (slope_integrable (T := T) (h := h) (a := a) q κ (w q) v).2
    have Hpos := intervalIntegral.integral_nonneg_of_forall (μ := volume) hwu
      (fun y => sq_nonneg ‖slope T h a y q κ‖)
    have Htail := intervalIntegral.integral_nonneg_of_forall (μ := volume) hwv
      (fun y => sq_nonneg ‖slope T h a y q κ‖)
    have Hlength : (w q-u)*(∫ y in u..w q, ‖slope T h a y q κ‖ ^ 2) ≤
        u*(∫ y in u..w q, ‖slope T h a y q κ‖ ^ 2) :=
      mul_le_mul_of_nonneg_right (by linarith) Hpos
    nlinarith [sq_nonneg (‖clippedSum T h a u q κ‖ -
      ∫ y in u..w q, ‖slope T h a y q κ‖)]
  have hD (y : ℝ) (hy : y ∈ Set.Icc u v) :
      ∑ q ∈ P, ‖slope T h a y q κ‖ ^ 2 ≤ C*log (2*u)*P.card/u := by
    have hy0 : 0 < y := hu0.trans_le hy.1
    let k : ι → ℂ := fun n => if y < h n then κ n else 0
    have hk : ∀ n ∈ T, ‖k n‖ ≤ 1 := by
      intro n hn
      dsimp [k]
      split_ifs <;> simp [hκ n hn]
    have He (q : α) : clippedSum T h a y q k = (y : ℂ)*slope T h a y q κ := by
      unfold clippedSum slope
      rw [mul_sum]
      apply sum_congr rfl
      intro n hn
      dsimp [k]
      split_ifs with hn'
      · rw [min_eq_right ((div_le_one (hp n hn)).2 hn'.le)]
        push_cast
        ring
      · simp
    have Hm := hm y hy k hk
    simp_rw [He, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs] at Hm
    rw [← mul_sum] at Hm
    have Hdiv : ∑ q ∈ P, ‖slope T h a y q κ‖ ^ 2 ≤ C*log y*P.card/y := by
      apply (le_div_iff₀ hy0).2
      nlinarith [Hm]
    apply Hdiv.trans
    apply div_le_div₀ (by positivity) _ hu0 hy.1
    have Hl : log y ≤ log (2*u) := log_le_log hy0 (hy.2.trans hv)
    gcongr
  have hi : IntervalIntegrable (fun y => ∑ q ∈ P, ‖slope T h a y q κ‖^2)
      volume u v := by
    have he : (fun y => ∑ q ∈ P, ‖slope T h a y q κ‖^2) =
        ∑ q ∈ P, fun y => ‖slope T h a y q κ‖^2 := by
      funext y
      simp only [Finset.sum_apply]
    rw [he]
    exact IntervalIntegrable.sum P
      (fun q _ => (slope_integrable (T := T) (h := h) (a := a) q κ u v).2)
  have hInt : (∫ y in u..v, ∑ q ∈ P, ‖slope T h a y q κ‖ ^ 2) ≤
      C*log (2*u)*P.card := by
    have HI := intervalIntegral.integral_mono_on huv hi intervalIntegrable_const hD
    rw [intervalIntegral.integral_const, smul_eq_mul] at HI
    apply HI.trans
    calc (v-u)*(C*log (2*u)*P.card/u) ≤ u*(C*log (2*u)*P.card/u) := by
          apply mul_le_mul_of_nonneg_right (by linarith)
          positivity
      _ = _ := by field_simp
  have H := sum_le_sum fun q (_hq : q ∈ P) => hb q
  rw [sum_add_distrib, ← mul_sum, ← mul_sum,
    ← intervalIntegral.integral_finsetSum
      (fun q _ => (slope_integrable (T := T) (h := h) (a := a) q κ u v).2)] at H
  have Hbase := hm u ⟨le_rfl, huv⟩ κ hκ
  have Hlog : C*u*log u*P.card ≤ C*u*log (2*u)*P.card := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (log_le_log hu0 (by linarith)) (mul_nonneg hC hu0.le))
      (Nat.cast_nonneg _)
  nlinarith [mul_le_mul_of_nonneg_left hInt (show 0 ≤ 2*u by positivity)]

private lemma block_count (hp : ∀ n ∈ T, 0 < h n)
    {C τ d u v : ℝ} {P B : Finset α} (hC : 0 ≤ C) (hτ : 0 < τ)
    (hd : 0 < d) (hu : 2 ≤ u) (huv : u ≤ v) (hv : v ≤ 2*u)
    (hm : ∀ y ∈ Set.Icc u v, ∀ κ : ι → ℂ, (∀ n ∈ T, ‖κ n‖ ≤ 1) →
      ∑ q ∈ P, ‖clippedSum T h a y q κ‖ ^ 2 ≤ C*y*log y*P.card)
    {κ : ι → ℂ} (hκ : ∀ n ∈ T, ‖κ n‖ ≤ 1) (hBP : B ⊆ P)
    (hb : ∀ q ∈ B, ∃ y ∈ Set.Icc u v,
      d*y^(1/2+τ) ≤ ‖clippedSum T h a y q κ‖) :
    (B.card : ℝ) ≤ 8*C/(d^2*τ)*u^(-τ)*P.card := by
  classical
  have hu0 : 0 < u := by linarith
  have hsel : ∀ q, ∃ y ∈ Set.Icc u v,
      q ∈ B → d*y^(1/2+τ) ≤ ‖clippedSum T h a y q κ‖ := by
    intro q
    by_cases hq : q ∈ B
    · obtain ⟨y,hy,hv⟩ := hb q hq
      exact ⟨y,hy,fun _ => hv⟩
    · exact ⟨u,⟨le_rfl,huv⟩,fun H => (hq H).elim⟩
  choose w hw hwB using hsel
  have upper := selected_block_bound hp hC (by linarith) huv hv hm hκ w hw
  have restrict : ∑ q ∈ B, ‖clippedSum T h a (w q) q κ‖^2 ≤
      ∑ q ∈ P, ‖clippedSum T h a (w q) q κ‖^2 :=
    sum_le_sum_of_subset_of_nonneg hBP (fun q _ _ => sq_nonneg _)
  have lower : (B.card : ℝ)*(d*u^(1/2+τ))^2 ≤
      ∑ q ∈ B, ‖clippedSum T h a (w q) q κ‖^2 := by
    rw [← nsmul_eq_mul]
    apply card_nsmul_le_sum
    intro q hq
    apply pow_le_pow_left₀ (by positivity)
    apply le_trans _ (hwB q hq)
    apply mul_le_mul_of_nonneg_left _ hd.le
    exact rpow_le_rpow hu0.le (hw q).1 (by linarith)
  have hlog : log (2*u) ≤ 2*u^τ/τ := by
    rw [log_mul (by norm_num) hu0.ne']
    have H := log_le_rpow_div hu0.le hτ
    have H2 := log_le_log (by norm_num : (0:ℝ)<2) hu
    calc log 2 + log u ≤ u^τ/τ + u^τ/τ := add_le_add (H2.trans H) H
      _ = _ := by ring
  have hpow : (d*u^(1/2+τ))^2 = d^2*u*(u^τ)^2 := by
    rw [mul_pow, sq (u^_), ← rpow_add hu0,
      show 1/2+τ+(1/2+τ) = 1+τ+τ by ring, rpow_add hu0,
      rpow_add hu0, rpow_one]
    ring
  have hupper : 4*C*u*log (2*u)*P.card ≤ 4*C*u*(2*u^τ/τ)*P.card := by
    gcongr
  have he : 4*C*u*(2*u^τ/τ)*P.card =
      (8*C/(d^2*τ)*u^(-τ)*P.card)*(d*u^(1/2+τ))^2 := by
    rw [hpow, rpow_neg hu0.le]
    field_simp
    <;> ring
  apply le_of_mul_le_mul_right (lower.trans (restrict.trans (upper.trans
    (hupper.trans he.le))))
  positivity

private theorem positive_clipped_window_bad_set {α : Type*} {ι : Type*}
    (T : Finset ι) (h : ι → ℝ)
    (a : ι → α → ℂ) (hp : ∀ n ∈ T, 0 < h n)
    {C τ d Y X : ℝ} {P B : Finset α} (hC : 0 ≤ C) (hτ : 0 < τ)
    (hd : 0 < d) (hY : 2 ≤ Y)
    (hm : ∀ y ∈ Set.Icc Y X, ∀ κ : ι → ℂ, (∀ n ∈ T, ‖κ n‖ ≤ 1) →
      ∑ q ∈ P, ‖clippedSum T h a y q κ‖^2 ≤ C*y*log y*P.card)
    {κ : ι → ℂ} (hκ : ∀ n ∈ T, ‖κ n‖ ≤ 1) (hBP : B ⊆ P)
    (hb : ∀ q ∈ B, ∃ y ∈ Set.Icc Y X,
      d*y^(1/2+τ) ≤ ‖clippedSum T h a y q κ‖) :
    (B.card : ℝ) ≤ (8*C/(d^2*τ)*Y^(-τ)/(1-(2:ℝ)^(-τ)))*P.card := by
  classical
  have hY0 : 0 < Y := by linarith
  let r : ℝ := (2:ℝ)^(-τ)
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r < 1 := rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hselect : ∀ q, ∃ k : ℕ, q ∈ B →
      2^k*Y ≤ X ∧ ∃ y ∈ Set.Icc (2^k*Y) (min (2*(2^k*Y)) X),
        d*y^(1/2+τ) ≤ ‖clippedSum T h a y q κ‖ := by
    intro q
    by_cases hq : q ∈ B
    · obtain ⟨y,hy,hyb⟩ := hb q hq
      have hyr : 1 ≤ y/Y := (le_div_iff₀ hY0).2 (by simpa using hy.1)
      obtain ⟨k,hk,hk'⟩ := exists_nat_pow_near hyr (by norm_num : (1:ℝ)<2)
      rw [le_div_iff₀ hY0] at hk
      rw [div_lt_iff₀ hY0, pow_succ] at hk'
      exact ⟨k,fun _ => ⟨hk.trans hy.2,y,⟨hk,le_min (by nlinarith) hy.2⟩,hyb⟩⟩
    · exact ⟨0,fun H => (hq H).elim⟩
  choose index hindex using hselect
  have group : (B.card : ℝ) =
      ∑ k ∈ B.image index, ((B.filter (fun q => index q = k)).card : ℝ) := by
    rw [card_eq_sum_card_image index B]
    push_cast
    rfl
  have Hk (k : ℕ) (hk : k ∈ B.image index) :
      ((B.filter (fun q => index q = k)).card : ℝ) ≤
        (8*C/(d^2*τ)*Y^(-τ)*P.card)*r^k := by
    obtain ⟨q,hq,rfl⟩ := mem_image.1 hk
    have hx := (hindex q hq).1
    have hpow : (1:ℝ) ≤ 2^index q := one_le_pow₀ (by norm_num)
    have hy : Y ≤ 2^index q*Y := by nlinarith
    have H := block_count hp hC hτ hd (by linarith : 2 ≤ 2^index q*Y)
      (le_min (by linarith) hx) (min_le_left _ _) (P := P)
      (B := B.filter (fun q' => index q' = index q))
      (fun y hy' => hm y ⟨hy.trans hy'.1,hy'.2.trans (min_le_right _ _)⟩)
      hκ ((filter_subset _ _).trans hBP) (fun q' hq' => by
        obtain ⟨hqB,hqi⟩ := mem_filter.1 hq'
        rw [← hqi]
        exact (hindex q' hqB).2)
    apply H.trans_eq
    have He : ((2:ℝ)^index q*Y)^(-τ) = Y^(-τ)*r^index q := by
      rw [mul_rpow (by positivity) hY0.le]
      dsimp [r]
      rw [← rpow_natCast, ← rpow_natCast, ← rpow_mul (by norm_num),
        ← rpow_mul (by norm_num)]
      ring_nf
    rw [He]
    ring
  have Hgeo : ∑ k ∈ B.image index, r^k ≤ (1-r)⁻¹ := by
    rw [← tsum_geometric_of_lt_one hr0 hr1]
    exact (summable_geometric_of_lt_one hr0 hr1).sum_le_tsum _ (fun _ _ => by positivity)
  calc
    (B.card : ℝ) ≤ ∑ k ∈ B.image index,
        (8*C/(d^2*τ)*Y^(-τ)*P.card)*r^k := by rw [group]; exact sum_le_sum Hk
    _ = (8*C/(d^2*τ)*Y^(-τ)*P.card)*(∑ k ∈ B.image index, r^k) :=
      (mul_sum _ _ _).symm
    _ ≤ (8*C/(d^2*τ)*Y^(-τ)*P.card)*(1-r)⁻¹ :=
      mul_le_mul_of_nonneg_left Hgeo (by positivity)
    _ = _ := by dsimp [r]; ring

/-- Every full window above two obeys a quantitative exceptional-set bound, uniformly
in the endpoint, the finite real knots, and the complex coefficient array. -/
theorem clipped_window_bad_set {α : Type*} {ι : Type*} (T : Finset ι) (h : ι → ℝ)
    (a : ι → α → ℂ)
    {C τ d Y X : ℝ} {P B : Finset α} (hC : 0 ≤ C) (hτ : 0 < τ)
    (hd : 0 < d) (hY : 2 ≤ Y)
    (hm : ∀ y ∈ Set.Icc Y X, ∀ κ : ι → ℂ, (∀ n ∈ T, ‖κ n‖ ≤ 1) →
      ∑ q ∈ P, ‖clippedSum T h a y q κ‖^2 ≤ C*y*log y*P.card)
    {κ : ι → ℂ} (hκ : ∀ n ∈ T, ‖κ n‖ ≤ 1) (hBP : B ⊆ P)
    (hb : ∀ q ∈ B, ∃ y ∈ Set.Icc Y X,
      d*y^(1/2+τ) ≤ ‖clippedSum T h a y q κ‖) :
    (B.card : ℝ) ≤ min 1 (8*C/(d^2*τ)*Y^(-τ)/(1-(2:ℝ)^(-τ)))*P.card := by
  classical
  let H : ℝ := max X 1 + 1
  have hH : 0 < H := by dsimp [H]; linarith [le_max_right X (1:ℝ)]
  let h' : ι → ℝ := fun n => if 0 < h n then h n else H
  let a' : ι → α → ℂ := fun n q =>
    if 0 < h n then a n q else ((H / h n : ℝ) : ℂ) * a n q
  have hp' : ∀ n ∈ T, 0 < h' n := by
    intro n _
    dsimp [h']
    split_ifs with hn
    · exact hn
    · exact hH
  have he (y : ℝ) (hy : y ∈ Set.Icc Y X) (q : α) (k : ι → ℂ) :
      clippedSum T h' a' y q k = clippedSum T h a y q k := by
    have hy0 : 0 ≤ y := by linarith [hy.1]
    have hyH : y ≤ H := by dsimp [H]; linarith [hy.2, le_max_left X (1:ℝ)]
    unfold clippedSum
    apply sum_congr rfl
    intro n _
    dsimp [h', a']
    split_ifs with hn
    · rfl
    · have hn0 : h n ≤ 0 := le_of_not_gt hn
      rw [min_eq_right ((div_le_one hH).2 hyH),
        min_eq_right (le_trans (div_nonpos_of_nonneg_of_nonpos hy0 hn0) zero_le_one)]
      have hw : y / H * (H / h n) = y / h n := div_mul_div_cancel₀ hH.ne'
      calc
        ((y / H : ℝ) : ℂ) * k n * (((H / h n : ℝ) : ℂ) * a n q) =
            (((y / H * (H / h n) : ℝ) : ℂ)) * k n * a n q := by push_cast; ring
        _ = _ := by rw [hw]
  have bound := positive_clipped_window_bad_set T h' a' hp'
    (X := X) (κ := κ) hC hτ hd hY
    (fun y hy k hk => by simpa only [he y hy] using hm y hy k hk) hκ hBP
    (by
      intro q hq
      obtain ⟨y, hy, hyb⟩ := hb q hq
      exact ⟨y, hy, by simpa only [he y hy] using hyb⟩)
  rw [min_mul_of_nonneg _ _ (Nat.cast_nonneg P.card), one_mul]
  exact le_min (by exact_mod_cast card_le_card hBP) bound

end D5.S3.CharacterSums.ClippedWindowBadSet
