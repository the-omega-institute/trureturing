/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/MangoldtFejerGap
   generality: I
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/MangoldtFejerGap
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite Fejér averages yield critical logarithm-squared savings up to every c below 1/48. -/

import D5.S3.Weil.Mertens.IntegratedExplicit.MangoldtLogSquareGap
import D5.S3.Zeros.Repulsion.FejerNearCollisionBound
import Mathlib.Algebra.BigOperators.Intervals
import Batteries.Tactic.OpenPrivate

/-! A positive trigonometric polynomial combines the midpoint bounds at all
pairwise distances in a finite equally spaced array. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Filter Set Real Finset
open scoped BigOperators Topology
open D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds
open D5.S3.Weil.Mertens.IntegratedExplicit
open RHSharpActualEnvelope (G actual_G_control coeff_real coeff_norm_hasSum)
open ActualKernelGlobalStrictPositivity (actual_cosine_hasSum)
open ActualKernelLocalPositivity (K K_zero)
open D5.S3.Arith.Robin.CompleteMertensPeak (U)
open private pair_cosine_sum_eq_normSq from D5.S3.Zeros.Repulsion.FejerNearCollisionBound
open private phaseDeficit positiveExp negativeExp negativeExp_pos negativeExp_add negativeExp_sub
  negativeExp_mul_positiveExp G_second_difference_le residualConstant residualConstant_nonneg
  abs_G_sub_K_le eventually_abs_exp_sub_one_le from
  D5.S3.Weil.Mertens.IntegratedExplicit.MangoldtCriticalGap
open private step step_small log_step_scale sinh_slope deficit_log_limit from
  D5.S3.Weil.Mertens.IntegratedExplicit.MangoldtLogSquareGap

namespace D5.S3.Weil.Mertens.IntegratedExplicit.MangoldtFejerGap

private def pairDistance (j k : ℕ) : ℝ := |(j : ℝ) - k|

private theorem cos_sum_nonneg (N : ℕ) (θ : ℝ) :
    0 ≤ ∑ j ∈ range N, ∑ k ∈ range N, cos (pairDistance j k * θ) := by
  have h (j k : ℕ) : cos (pairDistance j k * θ) = cos ((j : ℝ)*θ - k*θ) := by
    rw [← sub_mul]
    unfold pairDistance
    rcases le_total (k : ℝ) j with h | h
    · rw [abs_of_nonneg (sub_nonneg.mpr h)]
    · rw [abs_of_nonpos (sub_nonpos.mpr h), neg_mul, cos_neg]
  simp only [h]
  simp_rw [← Fin.sum_univ_eq_sum_range]
  rw [pair_cosine_sum_eq_normSq (fun i : Fin N => (i : ℝ)*θ)]
  exact Complex.normSq_nonneg _

private theorem double_sum_succ (N : ℕ) (f : ℝ → ℝ) (hf : f 0 = 0) :
    (∑ j ∈ range (N + 1), ∑ k ∈ range (N + 1), f (pairDistance j k)) =
      (∑ j ∈ range N, ∑ k ∈ range N, f (pairDistance j k)) +
      2 * ∑ k ∈ range N, f ((k : ℝ) + 1) := by
  have hor (k : ℕ) (hk : k ∈ range N) :
      pairDistance N k = (↑(N - 1 - k) : ℝ) + 1 := by
    have hlt := mem_range.mp hk
    have hk' : (k : ℝ) ≤ N := by exact_mod_cast hlt.le
    unfold pairDistance
    rw [abs_of_nonneg (sub_nonneg.mpr hk')]
    apply sub_eq_iff_eq_add.mpr
    exact_mod_cast (by omega : N = ((N - 1 - k) + 1) + k)
  have hedge : (∑ k ∈ range N, f (pairDistance N k)) =
      ∑ k ∈ range N, f ((k : ℝ) + 1) := by
    rw [← sum_range_reflect (fun k => f ((k : ℝ) + 1)) N]
    exact sum_congr rfl (fun k hk => congrArg f (hor k hk))
  have hsym (k : ℕ) : pairDistance k N = pairDistance N k := abs_sub_comm _ _
  simp only [sum_range_succ, sum_add_distrib, hsym]
  have hd : pairDistance N N = 0 := by simp [pairDistance]
  rw [hd, hf, hedge]
  ring

private theorem sum_successors (N : ℕ) :
    (∑ i ∈ range N, ((i : ℝ) + 1)) = N * ((N : ℝ) + 1) / 2 := by
  induction N with
  | zero => simp
  | succ N ih => rw [sum_range_succ, ih, Nat.cast_succ]; ring

private theorem sum_successor_squares (N : ℕ) :
    (∑ i ∈ range N, ((i : ℝ) + 1)^2) = N * ((N : ℝ) + 1) * (2*N+1) / 6 := by
  induction N with
  | zero => simp
  | succ N ih => rw [sum_range_succ, ih, Nat.cast_succ]; ring

private theorem sum_pairDistance (N : ℕ) :
    (∑ j ∈ range N, ∑ k ∈ range N, pairDistance j k) =
      (N : ℝ) * ((N : ℝ)^2 - 1) / 3 := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [double_sum_succ N (fun t => t) rfl, ih, sum_successors, Nat.cast_succ]
    ring

private theorem sum_pairDistance_sq (N : ℕ) :
    (∑ j ∈ range N, ∑ k ∈ range N, (pairDistance j k)^2) =
      (N : ℝ)^2 * ((N : ℝ)^2 - 1) / 6 := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [double_sum_succ N (fun t => t^2) (by norm_num), ih, sum_successor_squares, Nat.cast_succ]
    ring

private def curvature (y t : ℝ) := 2*K y-K (y+t)-K (y-t)

private theorem actual_series (rh : RiemannHypothesis) (s : ℝ) :
    HasSum (fun k => ‖actualCoeff k‖ * cos ((actualZero k).im * s)) (K s) := by
  have hnorm (k : ℕ) : ‖actualCoeff k‖ = 1 / (1 / 4 + (actualZero k).im ^ 2) := by
    rw [coeff_real rh k, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (one_div_pos.mpr (by positivity))]
  simpa only [Complex.ofReal_re, hnorm] using Complex.hasSum_re (actual_cosine_hasSum rh s)

private theorem defect_series (rh : RiemannHypothesis) (y t : ℝ) :
    HasSum (fun k => 2 * ‖actualCoeff k‖ * (1-cos ((actualZero k).im*y)) *
      (1-cos ((actualZero k).im*t))) (2*phaseDeficit t-curvature y t) := by
  have C := actual_series rh
  have lhs := ((coeff_norm_hasSum rh).sub (C t)).mul_left 2
  have rhs := (((C y).mul_left 2).sub (C (y+t))).sub (C (y-t))
  convert lhs.sub rhs using 1 <;> try rfl
  ext k
  simp only [mul_add, mul_sub, Real.cos_add, Real.cos_sub]
  ring

/-- A nonnegative finite cosine sum bounds all the midpoint defects by the same central deficit. -/
private theorem combined_phase {ι : Type*} (rh : RiemannHypothesis) (s : Finset ι)
    (t : ι → ℝ) (posPoly : ∀ u : ℝ, 0 ≤ ∑ i ∈ s, cos (u*t i)) (y : ℝ) :
    (∑ i ∈ s, (2*phaseDeficit (t i) - curvature y (t i))) ≤
      2*(s.card : ℝ)*phaseDeficit y := by
  let b (k : ℕ) := 2*‖actualCoeff k‖*(1-cos ((actualZero k).im*y))
  have subtotal (S : Finset ι) : HasSum
      (fun k => ∑ i ∈ S, b k*(1-cos ((actualZero k).im*t i)))
      (∑ i ∈ S, (2*phaseDeficit (t i)-curvature y (t i))) := by
    classical
    induction S using Finset.induction_on with
    | empty => simp
    | @insert i S hi ih =>
      simpa only [Finset.sum_insert hi, Pi.add_apply] using (defect_series rh y (t i)).add ih
  have target : HasSum (fun k => b k*(s.card:ℝ)) (2*(s.card:ℝ)*phaseDeficit y) := by
    convert (((coeff_norm_hasSum rh).sub (actual_series rh y)).mul_left (2*(s.card:ℝ))) using 1 <;> try rfl
    ext k
    simp only [b]
    ring
  apply hasSum_le _ (subtotal s) target
  intro k
  rw [← Finset.mul_sum, Finset.sum_sub_distrib]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
  apply mul_le_mul_of_nonneg_left (by linarith [posPoly ((actualZero k).im)])
  exact mul_nonneg (by positivity) (sub_nonneg.mpr (cos_le_one _))

private def shift (a y : ℝ) := a*y*negativeExp y

private def scale (y : ℝ) := negativeExp y*y^2

private def gain (a y : ℝ) := 2*phaseDeficit (shift a y)/scale y -
  a^2*((positiveExp (shift a y)-negativeExp (shift a y))/shift a y) -
  4*(firstLiMass+1)*a/y - 12*residualConstant/y^2

private lemma shift_pos {a y : ℝ} (ha : 0<a) (hy : 0<y) : 0<shift a y :=
  mul_pos (mul_pos ha hy) (negativeExp_pos _)

private lemma shift_small {a : ℝ} (ha : 0<a) : Tendsto (shift a) atTop (𝓝[>] 0) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · have H := (tendsto_nhdsWithin_iff.mp step_small).1.const_mul (4*a)
    apply (by simpa using H : Tendsto (fun y => 4*a*step y) atTop (𝓝 0)).congr
    intro y
    unfold step shift
    ring
  · filter_upwards [eventually_gt_atTop (0:ℝ)] with y hy using shift_pos ha hy

private lemma shift_log {a : ℝ} (ha : 0<a) :
    Tendsto (fun y => -log (shift a y) / y) atTop (𝓝 (1/2)) := by
  have H : Tendsto (fun y : ℝ => log (4*a)/y) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using (tendsto_const_nhds (x:=log (4*a))).mul tendsto_inv_atTop_zero
  apply (by simpa using log_step_scale.sub H : Tendsto
    (fun y => -log (step y)/y-log (4*a)/y) atTop (𝓝 (1/2))).congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with y hy
  have hstep : 0<step y := by dsimp [step]; exact mul_pos (by positivity) (negativeExp_pos _)
  rw [show shift a y = (4*a)*step y by unfold shift step; ring,
    log_mul (by positivity) hstep.ne']
  ring

private lemma origin {a : ℝ} (ha : 0<a) :
    Tendsto (fun y => phaseDeficit (shift a y) / scale y) atTop (𝓝 (a/4)) := by
  have H := ((deficit_log_limit.comp (shift_small ha)).mul (shift_log ha)).mul_const a
  apply (by convert H using 1 <;> first | rfl | ring : Tendsto
    (fun y => (firstLiMass - K (shift a y)) / (shift a y * log (1 / shift a y)) *
      (-log (shift a y) / y) * a) atTop (𝓝 (a/4))).congr'
  filter_upwards [eventually_gt_atTop (0:ℝ), (shift_small ha).eventually
    (eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds (zero_lt_one' ℝ)))]
    with y hy hh
  have hp := shift_pos ha hy
  have hl := (log_neg hp hh).ne
  rw [one_div, log_inv]
  unfold phaseDeficit scale
  field_simp [hp.ne',hl,(negativeExp_pos y).ne',hy.ne']
  unfold shift
  ring

private theorem gain_limit {a : ℝ} (ha : 0 ≤ a) :
    Tendsto (gain a) atTop (𝓝 (a/2-a^2)) := by
  have hi : Tendsto (fun y : ℝ => y⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  rcases ha.eq_or_lt with hh | hp
  · subst a
    have L := ((hi.pow 2).const_mul (-(12*residualConstant)))
    apply (by simpa using L : Tendsto (fun y : ℝ => -(12*residualConstant)*(y⁻¹)^2)
      atTop (𝓝 (0 / 2 - (0:ℝ)^2))).congr
    intro y
    simp [gain, shift, phaseDeficit, K_zero, div_eq_mul_inv]
  · have L := ((((origin hp).const_mul 2).sub ((sinh_slope.comp (shift_small hp)).const_mul
      (a^2))).sub (hi.const_mul (4*(firstLiMass+1)*a))).sub ((hi.pow 2).const_mul (12*residualConstant))
    convert L using 1
    · ext y
      simp only [gain, Function.comp_apply, div_eq_mul_inv, inv_pow]
      ring
    · ring_nf

private lemma gain_scaled {a y : ℝ} (ha : 0 ≤ a) (hy : 0 < y) :
    gain a y * scale y = 2*phaseDeficit (shift a y) -
      (positiveExp y * shift a y * (positiveExp (shift a y)-negativeExp (shift a y)) +
       4*(firstLiMass+1)*shift a y + 12*negativeExp y*residualConstant) := by
  have hq := negativeExp_pos y
  have hs : 0 < scale y := mul_pos hq (sq_pos_of_pos hy)
  rcases ha.eq_or_lt with h | ha
  · subst a
    simp [gain, shift, phaseDeficit, K_zero, scale, positiveExp, negativeExp]
    field_simp
  · have hp := shift_pos ha hy
    have pr := negativeExp_mul_positiveExp y
    have s : a^2*((positiveExp (shift a y)-negativeExp (shift a y))/shift a y)*scale y =
        positiveExp y*shift a y*(positiveExp (shift a y)-negativeExp (shift a y)) := by
      field_simp [hp.ne']
      unfold shift scale
      linear_combination (norm := ring) -(a^2 * y^2 * negativeExp y *
        (positiveExp (a*y*negativeExp y)-negativeExp (a*y*negativeExp y))) * pr
    have b : 4*(firstLiMass+1)*a/y * scale y = 4*(firstLiMass+1)*shift a y := by
      unfold shift scale
      field_simp
    have r : 12*residualConstant/y^2*scale y = 12*negativeExp y*residualConstant := by
      unfold scale
      field_simp
    unfold gain
    rw [sub_mul,sub_mul,sub_mul,s,b,r,div_mul_cancel₀ _ hs.ne']
    ring

private lemma small_exp (a : ℝ) (ha : 0 ≤ a) : ∀ᶠ y : ℝ in atTop,
    |positiveExp (shift a y)-1| ≤ 2*shift a y ∧ |negativeExp (shift a y)-1| ≤ 2*shift a y ∧
    shift a y ≤ 1 := by
  rcases ha.eq_or_lt with he | hp
  · subst a
    simp [shift, positiveExp, negativeExp]
  · exact (shift_small hp).eventually eventually_abs_exp_sub_one_le

private theorem gain_transfer (rh : RiemannHypothesis) (a : ℝ) (ha : 0 ≤ a) :
    ∀ᶠ y : ℝ in atTop, gain a y * scale y ≤
      (2*phaseDeficit (shift a y) - (2*K y-K (y+shift a y)-K (y-shift a y))) -
      2*(G y-K y) := by
  filter_upwards [eventually_gt_atTop (2:ℝ), small_exp a ha,
    (actual_G_control rh).1 1 one_pos] with y hy hs hG
  let h := shift a y
  have hp : 0 ≤ h := mul_nonneg (mul_nonneg ha (by linarith)) (negativeExp_pos _).le
  obtain ⟨hplus,hminus,h1⟩ := hs
  change |positiveExp h-1| ≤ 2*h at hplus
  change |negativeExp h-1| ≤ 2*h at hminus
  change h ≤ 1 at h1
  have hq := (negativeExp_pos y).le
  have err := abs_G_sub_K_le (by linarith : 0 < y)
  have errP := abs_G_sub_K_le (by linarith : 0 < y+h)
  have errN := abs_G_sub_K_le (by linarith : 0 < y-h)
  rw [negativeExp_add] at errP
  rw [negativeExp_sub] at errN
  have bound (z : ℝ) (hz : z ≤ 3) :
      negativeExp y*z*residualConstant ≤ 3*negativeExp y*residualConstant := by
    nlinarith [mul_nonneg (mul_nonneg hq residualConstant_nonneg) (sub_nonneg.mpr hz)]
  have ep := (le_abs_self _).trans (errP.trans (bound _ (by linarith [(abs_le.mp hminus).2])))
  have en := (le_abs_self _).trans (errN.trans (bound _ (by linarith [(abs_le.mp hplus).2])))
  have hc : |2-(positiveExp h + negativeExp h)| ≤ 4*h := by
    rw [abs_le]
    constructor <;> linarith [(abs_le.mp hplus).1,(abs_le.mp hplus).2,
      (abs_le.mp hminus).1,(abs_le.mp hminus).2]
  have mul := mul_le_mul hc hG.le (abs_nonneg _) (by positivity)
  rw [← abs_mul] at mul
  have coeff := (le_abs_self _).trans mul
  have mid := G_second_difference_le y h
  rw [gain_scaled ha (by linarith)]
  change 2*phaseDeficit h - (positiveExp y*h*(positiveExp h-negativeExp h) +
    4*(firstLiMass+1)*h+12*negativeExp y*residualConstant) ≤
    2*phaseDeficit h - (2*K y-K (y+h)-K (y-h)) - 2*(G y-K y)
  linarith [mul_nonneg hq residualConstant_nonneg]

private def pairs (N : ℕ) := range N ×ˢ range N

private def amplitude (N : ℕ) (p : ℕ × ℕ) : ℝ :=
  pairDistance p.1 p.2 / (2 * N)

private lemma amplitude_nonneg (N : ℕ) (p : ℕ × ℕ) : 0 ≤ amplitude N p :=
  div_nonneg (abs_nonneg _) (by positivity)

private lemma amplitude_moment {N : ℕ} (hN : 0 < (N : ℝ)) :
    ∑ p ∈ pairs N, (amplitude N p / 2 - amplitude N p ^ 2) = ((N : ℝ)^2 - 1)/24 := by
  have A : (∑ p ∈ pairs N, pairDistance p.1 p.2) = (N : ℝ) * ((N : ℝ)^2-1)/3 := by
    rw [pairs, sum_product]
    exact sum_pairDistance N
  have B : (∑ p ∈ pairs N, (pairDistance p.1 p.2)^2) = (N : ℝ)^2 * ((N : ℝ)^2-1)/6 := by
    rw [pairs, sum_product]
    exact sum_pairDistance_sq N
  simp only [amplitude, div_pow, sum_sub_distrib, ← sum_div, A, B]
  field_simp
  ring

private lemma phase_positive (N : ℕ) (u y : ℝ) :
    0 ≤ ∑ p ∈ pairs N, cos (u * shift (amplitude N p) y) := by
  rw [pairs, sum_product]
  convert cos_sum_nonneg N (u / (2*N) * y * negativeExp y) using 1
  congr 1
  funext j
  apply sum_congr rfl
  intro k _
  congr 1
  dsimp [shift, amplitude]
  ring

/-- Sum the arithmetic gains over all ordered pairs of indices in the finite array. -/
private lemma finite_gap (rh : RiemannHypothesis) {N : ℕ} (hn : 0 < (N : ℝ))
    (c : ℝ) (hc : 2*(N:ℝ)^2*c < ((N:ℝ)^2-1)/24) :
    ∀ᶠ y : ℝ in atTop, c * scale y ≤ firstLiMass - G y := by
  have lim : Tendsto (fun y : ℝ => ∑ p ∈ pairs N, gain (amplitude N p) y)
      atTop (𝓝 (((N:ℝ)^2-1)/24)) := by
    rw [← amplitude_moment hn]
    exact tendsto_finsetSum _ (fun p _ => gain_limit (amplitude_nonneg N p))
  have bound := (eventually_all_finset (pairs N)).mpr
    (fun p _ => gain_transfer rh (amplitude N p) (amplitude_nonneg N p))
  filter_upwards [lim.eventually_const_lt hc, bound, eventually_gt_atTop (0:ℝ)] with y h b hy
  have ph := combined_phase rh (pairs N) (fun p => shift (amplitude N p) y)
    (fun u => phase_positive N u y) y
  have hu := sum_le_sum (s := pairs N) (fun p hp => b p hp)
  rw [← sum_mul, sum_sub_distrib] at hu
  have cardN : ((pairs N).card : ℝ) = (N : ℝ)^2 := by simp [pairs, pow_two]
  simp only [Finset.sum_const, nsmul_eq_mul, cardN] at hu
  rw [cardN] at ph
  change (∑ p ∈ pairs N, (2*phaseDeficit (shift (amplitude N p) y) -
    curvature y (shift (amplitude N p) y))) ≤ _ at ph
  change (∑ p ∈ pairs N, gain (amplitude N p) y) * scale y ≤
    (∑ p ∈ pairs N, (2*phaseDeficit (shift (amplitude N p) y) -
      curvature y (shift (amplitude N p) y))) - (N : ℝ)^2 * (2*(G y - K y)) at hu
  have hs : 0 < scale y := mul_pos (negativeExp_pos y) (sq_pos_of_pos hy)
  have lower := mul_le_mul_of_nonneg_right h.le hs.le
  have upper := le_trans (le_trans lower hu) (sub_le_sub_right ph _)
  unfold phaseDeficit at upper
  apply le_of_mul_le_mul_left (a:=2*(N:ℝ)^2) _ (by positivity)
  linarith

private lemma large_degree {c : ℝ} (hc : c < 1/48) :
    ∃ N : ℕ, 0 < (N : ℝ) ∧ 2*(N:ℝ)^2*c < ((N:ℝ)^2-1)/24 := by
  have hd : 0 < 1-48*c := by linarith
  obtain ⟨N,hN⟩ := exists_nat_gt (max (1:ℝ) (1/(1-48*c)))
  have h1 : (1:ℝ) < N := (le_max_left _ _).trans_lt hN
  have h2 : 1/(1-48*c) < N := (le_max_right _ _).trans_lt hN
  have h3 : (N:ℝ) ≤ (N:ℝ)^2 := by nlinarith
  have h4 := (div_lt_iff₀ hd).mp (lt_of_lt_of_le h2 h3)
  exact ⟨N, by linarith, by linarith⟩

/-- Classical RH is equivalent to an eventual real-axis saving of every fixed coefficient
strictly below one forty-eighth times the square of the logarithm. -/
theorem rh_iff_eventually_fejer_gap :
    RiemannHypothesis ↔ ∀ c : ℝ, c < 1/48 → ∀ᶠ x : ℝ in atTop,
      U x ≤ firstLiMass * sqrt x - c * (log x)^2 := by
  constructor
  · intro rh c hc
    obtain ⟨N, hn, hN⟩ := large_degree hc
    filter_upwards [tendsto_log_atTop.eventually (finite_gap rh hn c hN),
      eventually_gt_atTop (1:ℝ)] with x h hx
    have hx0 := zero_lt_one.trans hx
    have hw : negativeExp (log x) * sqrt x = 1 := by
      simpa [positiveExp, exp_half, exp_log hx0] using negativeExp_mul_positiveExp (log x)
    change c*(negativeExp (log x)*(log x)^2) ≤ firstLiMass - G (log x) at h
    rw [G, exp_log hx0] at h
    change c*(negativeExp (log x)*(log x)^2) ≤ firstLiMass - negativeExp (log x)*U x at h
    apply le_of_mul_le_mul_left (a:=negativeExp (log x)) _ (negativeExp_pos _)
    nlinarith [congrArg (fun t : ℝ => firstLiMass*t) hw]
  · intro h
    apply MangoldtLogSquareGap.rh_iff_eventually_log_squared_gap.mpr
    exact fun c hc => h c (hc.trans (by norm_num))

end D5.S3.Weil.Mertens.IntegratedExplicit.MangoldtFejerGap
