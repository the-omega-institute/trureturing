/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHMidpointWindowTransfer
   generality: I
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHMidpointWindowTransfer
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Pass bounds on weighted midpoint averages to signed prime-window limsups. -/

import D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder.RHRootLateIncrement
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! A single late phase return controls the whole weighted window and its midpoint. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter Set MeasureTheory ArithmeticFunction
open scoped ArithmeticFunction.Moebius Topology

namespace D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder

open D5.S3.Weil.Mertens.IntegratedExplicit (actualCoeff actualCoeff_hasSum)
open D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelCusp (c)
open D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower
open D5.S3.Weil.Mertens.IntegratedExplicit.PrimePhaseCluster (phaseOrbit phaseOrbit_cluster_iff)
open D5.S3.Weil.Mertens.IntegratedExplicit.RHPrimeWindowMean (frequency exp_mode_norm)

private theorem exponential_midpoint_returns (hRH : RiemannHypothesis) {r : ℝ}
    (hr : 1 < r) (L U : ℝ) {b : ℝ} :
    let s : ℝ := 1 / 2 - (2 * r)⁻¹
    let M := fun u : ℝ =>
      (∫ t in (0 : ℝ)..L, Real.exp (-s * t) * rootSignal r (u + t)) /
        (∫ t in (0 : ℝ)..L, Real.exp (-s * t)) - rootSignal r (u + L / 2)
    b < M (-L / 2) → ∃ u ≥ U, b < M u := by
  dsimp only
  let s : ℝ := 1 / 2 - (2 * r)⁻¹
  let w : ℝ → ℝ := fun t => Real.exp (-s * t)
  let W := ∫ t in (0 : ℝ)..L, w t
  let M := fun u : ℝ =>
    (∫ t in (0 : ℝ)..L, w t * rootSignal r (u + t)) / W - rootSignal r (u + L / 2)
  let readWindow : (ℕ → Circle) → ℝ := fun p =>
    (∫ t in (0 : ℝ)..L, w t * readSignal r (-L / 2 + t) p) / W - readSignal r 0 p
  change b < M (-L / 2) → ∃ u ≥ U, b < M u
  intro hb
  have hsignal : Continuous (fun q : (ℕ → Circle) × ℝ => readSignal r q.2 q.1) := by
    unfold readSignal
    apply Continuous.div_const
    apply Complex.continuous_re.comp
    apply continuous_tsum (fun k => by fun_prop) (actualCoeff_hasSum.summable.norm.mul_left r)
    intro k q
    simpa only [norm_mul, Circle.norm_coe, exp_mode_norm hRH, mul_one] using rootCoeff_bound hr k
  have hweighted : Continuous (Function.uncurry
      (fun (p : ℕ → Circle) (t : ℝ) => w t * readSignal r (-L / 2 + t) p)) := by
    change Continuous (fun q : (ℕ → Circle) × ℝ => w q.2 * readSignal r (-L / 2 + q.2) q.1)
    have hw : Continuous w := by fun_prop
    exact (hw.comp continuous_snd).mul
      (hsignal.comp (continuous_fst.prodMk (continuous_const.add continuous_snd)))
  have hcont : Continuous readWindow := by
    exact ((intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      hweighted 0 L).div_const W).sub
      (hsignal.comp (continuous_id.prodMk continuous_const))
  have horbit (t : ℝ) : readWindow (phaseOrbit t) = M (r * t - L / 2) := by
    simp only [readWindow, M, read_signal_orbit hRH hr, add_zero, sub_add_cancel]
    simp only [sub_eq_add_neg, neg_div, add_assoc]
  have hzero : b < readWindow (phaseOrbit 0) := by
    simpa only [horbit, mul_zero, zero_sub, neg_div] using hb
  have hreturn := (phaseOrbit_cluster_iff (phaseOrbit 0)).2 (subset_closure (mem_range_self _))
  have hlarge := (hreturn.continuousAt_comp hcont.continuousAt).frequently
    (eventually_gt_nhds hzero)
  have hr0 : 0 < r := by linarith
  obtain ⟨t, hvalue, hlate⟩ :=
    (hlarge.and_eventually (eventually_ge_atTop ((U + L / 2) / r))).exists
  have ht := (div_le_iff₀ hr0).1 hlate
  refine ⟨r * t - L / 2, by linarith only [ht.trans_eq (mul_comm _ _)], ?_⟩
  simpa only [Function.comp_apply, horbit] using hvalue

/-- A two-sided midpoint comparison transfers to the original signed prime-window limsup. -/
theorem signed_window_midpoint_transfer (hRH : RiemannHypothesis)
    (m r : ℕ) (hm : 2 ≤ m) (heven : m + 1 = 2 * r)
    (remainder : ℝ → ℝ)
    (hmidpoint :
      let s : ℝ := 1 / 2 - (2 * (r : ℝ))⁻¹
      let G := fun L : ℝ =>
        (L / (8 * s)) * (Real.log (1 / L) + Real.log (2 * r) - 2 * c + 1 / 2)
      let M := fun u L : ℝ =>
        (∫ t in (0 : ℝ)..L, Real.exp (-s * t) * rootSignal r (u + t)) /
          (∫ t in (0 : ℝ)..L, Real.exp (-s * t)) - rootSignal r (u + L / 2)
      ∃ C > 0, ∀ L : ℝ, 0 < L → L ≤ 1 / 4 →
        (∀ u : ℝ, |M u L| ≤ G L + C * remainder L) ∧
        G L - C * remainder L ≤ M (-L / 2) L) :
    let s := orderRate m
    let cm := (μ (m + 1) : ℝ) * (((m : ℝ) + 1) / ((m : ℝ) * s))
    let V := fun L u : ℝ =>
      |signedWindowResidual m (Real.exp u) (Real.exp (u + L)) /
        powerGap s (Real.exp u) (Real.exp (u + L)) + cm + (μ r : ℝ) * rootSignal r (u + L / 2)|
    ∃ C > 0, ∀ L : ℝ, 0 < L → L ≤ 1 / 4 →
      (atTop : Filter ℝ).IsBoundedUnder (· ≤ ·) (V L) ∧
      |limsup (V L) atTop -
        |(μ r : ℝ)| * ((L / (8 * s)) * (Real.log (1 / L) + Real.log (2 * r) - 2 * c + 1 / 2))| ≤
        |(μ r : ℝ)| * (C * remainder L) := by
  dsimp only
  let s := orderRate m
  let δ := ((m : ℝ) + 1)⁻¹ - ((m : ℝ) + 2)⁻¹
  let cm := (μ (m + 1) : ℝ) * (((m : ℝ) + 1) / ((m : ℝ) * s))
  let a := (μ r : ℝ)
  have ha : 0 ≤ |a| := abs_nonneg a
  have hr : (1 : ℝ) < r := by exact_mod_cast (show 1 < r by omega)
  have hq : (m : ℝ) + 1 = 2 * (r : ℝ) := by exact_mod_cast heven
  have hs' : s = 1 / 2 - (2 * (r : ℝ))⁻¹ := by dsimp [s, orderRate]; rw [hq]
  have hs : 0 < s := by
    rw [hs', inv_eq_one_div, sub_pos]
    exact (div_lt_iff₀ (by positivity)).2 (by linarith)
  have hδ : 0 < δ := sub_pos.mpr (inv_strictAnti₀ (by positivity) (by linarith))
  obtain ⟨a₀, K, ha₂, hK, hexpansion⟩ := signed_window_even_cutoff_expansion hRH
  have ha₀ : 0 < a₀ := by linarith
  obtain ⟨D, hD, hmidpoint⟩ := hmidpoint
  let G := fun L : ℝ => (L / (8 * s)) * (Real.log (1 / L) + Real.log (2 * r) - 2 * c + 1 / 2)
  refine ⟨D, hD, fun L hL hL' => ?_⟩
  let E := D * remainder L
  let P := fun u : ℝ => rootPrimitive r (Real.exp (u + L)) - rootPrimitive r (Real.exp u)
  let gap := fun u : ℝ => powerGap s (Real.exp u) (Real.exp (u + L))
  let T := fun u : ℝ =>
    signedWindowResidual m (Real.exp u) (Real.exp (u + L)) / gap u + cm +
      a * rootSignal r (u + L / 2)
  let M := fun u : ℝ => P u / gap u - rootSignal r (u + L / 2)
  let W := K * (((m + 1 : ℕ) : ℝ) * (1 + Real.log ((m + 1 : ℕ) : ℝ)) ^ 2)
  let K' := W * ((s + δ) / s)
  have hM (u : ℝ) :
      M u =
        (∫ t in (0 : ℝ)..L, Real.exp (-(1 / 2 - (2 * (r : ℝ))⁻¹) * t) *
          rootSignal r (u + t)) /
          (∫ t in (0 : ℝ)..L, Real.exp (-(1 / 2 - (2 * (r : ℝ))⁻¹) * t)) -
          rootSignal r (u + L / 2) := by
    dsimp only [M, P, gap]
    rw [hs', root_increment_eq_weighted_average hr hL u]
  obtain ⟨hup, hlow⟩ := hmidpoint L hL hL'
  have hupper (u : ℝ) : |M u| ≤ G L + E := by
    simpa only [hM, G, E, hs'] using hup u
  have hlower : G L - E ≤ M (-L / 2) := by
    simpa only [hM, G, E, hs'] using hlow
  have hreturn (U : ℝ) {b : ℝ} (hb : b < M (-L / 2)) : ∃ u ≥ U, b < M u := by
    simpa only [hM] using exponential_midpoint_returns hRH hr L U (b := b) (by
      simpa only [hM] using hb)
  have hdecay (u : ℝ) (hu : Real.log a₀ ≤ u) : |T u + a * M u| ≤ K' * Real.exp (-δ * u) := by
    let x := Real.exp u
    let y := Real.exp (u + L)
    have hau : a₀ ≤ x := by
      rw [← Real.exp_log ha₀]
      exact Real.exp_le_exp.mpr hu
    have hxy : x < y := Real.exp_lt_exp.mpr (by linarith)
    have hg : 0 < gap u :=
      sub_pos.mpr (Real.rpow_lt_rpow_of_neg (Real.exp_pos _) hxy (neg_neg_of_pos hs))
    have hex := hexpansion m r hm heven x y hau hxy.le
    have he : |signedWindowResidual m x y + cm * gap u + a * P u| ≤
        K' * Real.exp (-δ * u) * gap u := by
      simpa only [s, δ, cm, W, K', a, P, gap, x, y, Real.rpow_def_of_pos (Real.exp_pos _),
        Real.log_exp, mul_comm u (-δ)] using hex.1.trans hex.2
    rw [show T u + a * M u = (signedWindowResidual m x y + cm * gap u + a * P u) / gap u by
      dsimp only [T, M, x, y]
      field_simp [hg.ne']
      ring, abs_div, abs_of_pos hg, div_le_iff₀ hg]
    exact he
  have hzero : Tendsto (fun u : ℝ => K' * Real.exp (-δ * u)) atTop (𝓝 0) := by
    simpa only [mul_zero, Function.comp_apply, id_eq] using
      (Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (neg_neg_of_pos hδ))).const_mul K'
  have hsmall (ε : ℝ) (hε : 0 < ε) : ∀ᶠ u in atTop, |T u + a * M u| < ε := by
    filter_upwards [eventually_ge_atTop (Real.log a₀), hzero (eventually_lt_nhds hε)] with u hu hεu
    exact (hdecay u hu).trans_lt hεu
  have hupperTriangle (u : ℝ) : |T u| ≤ |T u + a * M u| + |a| * |M u| := by
    simpa only [add_sub_cancel_right, abs_mul] using abs_sub (T u + a * M u) (a * M u)
  have hlowerTriangle (u : ℝ) : |a| * M u ≤ |T u + a * M u| + |T u| := by
    have h := abs_sub (T u + a * M u) (T u)
    rw [add_sub_cancel_left, abs_mul] at h
    exact (mul_le_mul_of_nonneg_left (le_abs_self _) ha).trans h
  let V := fun u : ℝ => |T u|
  have hbounded : (atTop : Filter ℝ).IsBoundedUnder (· ≤ ·) V := by
    refine ⟨|a| * (G L + E) + 1, ?_⟩
    change ∀ᶠ u in (atTop : Filter ℝ), V u ≤ _
    filter_upwards [hsmall 1 zero_lt_one] with u hu
    have hmul := mul_le_mul_of_nonneg_left (hupper u) ha
    change |T u| ≤ _
    linarith only [hupperTriangle u, hu, hmul]
  have hcobounded : (atTop : Filter ℝ).IsCoboundedUnder (· ≤ ·) V :=
    isCoboundedUnder_le_of_le _ (fun u => abs_nonneg (T u))
  have hQupper : limsup V atTop ≤ |a| * (G L + E) := by
    apply (limsup_le_iff' hcobounded hbounded).2
    intro b hb
    filter_upwards [hsmall (b - |a| * (G L + E)) (sub_pos.mpr hb)] with u hu
    have hmul := mul_le_mul_of_nonneg_left (hupper u) ha
    change |T u| ≤ b
    linarith only [hupperTriangle u, hu, hmul]
  have hQlower : |a| * (G L - E) ≤ limsup V atTop := by
    rcases ha.eq_or_lt with ha_zero | ha_pos
    · rw [← ha_zero, zero_mul]
      exact le_limsup_of_frequently_le
        (Frequently.of_forall fun u => abs_nonneg (T u)) hbounded
    apply (le_limsup_iff' hcobounded hbounded).2
    intro b hb
    let ε := (|a| * (G L - E) - b) / 2
    have hε : 0 < ε := by dsimp [ε]; linarith
    have hthreshold : (b + ε) / |a| < M (-L / 2) := by
      apply (div_lt_iff₀ ha_pos).2
      have h := mul_le_mul_of_nonneg_left hlower ha
      dsimp [ε]
      linarith only [h, hb]
    obtain ⟨U₀, hlate⟩ := eventually_atTop.1 (hsmall ε hε)
    refine frequently_atTop.2 fun U => ?_
    obtain ⟨u, hu, hval⟩ := hreturn (max U U₀) hthreshold
    refine ⟨u, (le_max_left _ _).trans hu, ?_⟩
    have he := hlate u ((le_max_right _ _).trans hu)
    have hv := (div_lt_iff₀ ha_pos).1 hval
    change b ≤ |T u|
    linarith only [hlowerTriangle u, he, hv]
  refine ⟨hbounded, abs_le.mpr ⟨?_, ?_⟩⟩
  · change -(|a| * (D * remainder L)) ≤
      limsup V atTop - |a| * G L
    dsimp [E] at hQlower
    linarith only [hQlower]
  · change limsup V atTop - |a| * G L ≤ |a| * (D * remainder L)
    dsimp [E] at hQupper
    linarith only [hQupper]

end D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder
