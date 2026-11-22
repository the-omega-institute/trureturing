/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHMobiusEvenCutoffLeftLimsup
   generality: I
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHMobiusEvenCutoffLeftLimsup
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The exact left-endpoint limsup scale of the original signed prime window. -/

import D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder.RHRootQuarterPhaseIncrement
import D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder.RHMobiusEvenCutoffMidpoint

/-! The signed forward increment transfers the midpoint estimate to the left endpoint. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter Set ArithmeticFunction
open scoped ArithmeticFunction.Moebius Topology

namespace D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder

open D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower
open D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelCusp (c)
open D5.S3.Weil.ZeroData.ZetaOrdinateCompleteOptimizer (quarterPhase phaseHull)

private theorem limsup_sub_signed_increment (F D : ℝ → ℝ) (a P E M : ℝ)
    (hM : 0 ≤ M)
    (hbounded : (atTop : Filter ℝ).IsBoundedUnder (· ≤ ·) (fun u => |F u|))
    (hmid : limsup (fun u => |F u|) atTop ≤ M)
    (hupper : ∀ u, |D u| ≤ P + E)
    (hreturn : ∀ U b : ℝ, b < P - E → ∃ u ≥ U, b < D u) :
    let V := fun u => |F u - a * D u|
    (atTop : Filter ℝ).IsBoundedUnder (· ≤ ·) V ∧
      |limsup V atTop - |a| * P| ≤ |a| * E + M := by
  dsimp only
  let V := fun u => |F u - a * D u|
  have hmidSmall (ε : ℝ) (hε : 0 < ε) : ∀ᶠ u in atTop, |F u| ≤ M + ε :=
    (limsup_le_iff' (isCoboundedUnder_le_of_le _ fun u => abs_nonneg (F u)) hbounded).1
      hmid _ (lt_add_of_pos_right _ hε)
  have htri (u : ℝ) : V u ≤ |F u| + |a| * (P + E) := by
    exact (by simpa only [abs_mul] using abs_sub (F u) (a * D u) :
      V u ≤ |F u| + |a| * |D u|).trans (by gcongr; exact hupper u)
  have hlate : (atTop : Filter ℝ).IsBoundedUnder (· ≤ ·) V := by
    refine ⟨M + 1 + |a| * (P + E), ?_⟩
    change ∀ᶠ u in atTop, V u ≤ _
    filter_upwards [hmidSmall 1 zero_lt_one] with u hu
    exact (htri u).trans (by gcongr)
  have hco : (atTop : Filter ℝ).IsCoboundedUnder (· ≤ ·) V :=
    isCoboundedUnder_le_of_le _ fun u => abs_nonneg (F u - a * D u)
  have hup : limsup V atTop ≤ |a| * (P + E) + M := by
    apply (limsup_le_iff' hco hlate).2
    intro b hb
    filter_upwards [hmidSmall (b - (|a| * (P + E) + M)) (sub_pos.mpr hb)] with u hu
    linarith only [htri u, hu]
  have hlo : |a| * (P - E) - M ≤ limsup V atTop := by
    rcases (abs_nonneg a).eq_or_lt with ha | ha
    · rw [← ha, zero_mul, zero_sub]
      apply (neg_nonpos.mpr hM).trans
      exact le_limsup_of_frequently_le (Frequently.of_forall fun u => abs_nonneg (F u - a * D u))
        hlate
    apply (le_limsup_iff' hco hlate).2
    intro b hb
    let ε := (|a| * (P - E) - M - b) / 2
    have hε : 0 < ε := by dsimp [ε]; linarith
    have hthreshold : (b + M + ε) / |a| < P - E := by
      apply (div_lt_iff₀ ha).2
      dsimp [ε]
      linarith only [hb]
    obtain ⟨U₀, hU₀⟩ := eventually_atTop.1 (hmidSmall ε hε)
    apply frequently_atTop.2
    intro U
    obtain ⟨u, hu, hDu⟩ := hreturn (max U U₀) _ hthreshold
    have hFu := hU₀ u ((le_max_right _ _).trans hu)
    have hDu' := (div_lt_iff₀ ha).1 hDu
    have hrev : |a| * D u ≤ |F u| + V u := by
      have h := abs_sub (F u) (F u - a * D u)
      rw [sub_sub_cancel, abs_mul] at h
      exact (mul_le_mul_of_nonneg_left (le_abs_self _) ha.le).trans h
    exact ⟨u, (le_max_left _ _).trans hu, by linarith only [hFu, hDu', hrev]⟩
  refine ⟨hlate, abs_le.mpr ⟨?_, ?_⟩⟩ <;>
    linarith only [hlo, hup]

/-- The original signed window with its left-endpoint correction has a finite late limsup
at every sufficiently small positive width, with the sharp logarithmic-square coefficient. -/
theorem signed_window_even_cutoff_left_limsup (hRH : RiemannHypothesis)
    (hquarter : quarterPhase ∈ phaseHull) (m r : ℕ) (hm : 2 ≤ m) (heven : m + 1 = 2 * r) :
    let s := orderRate m
    let cm := (μ (m + 1) : ℝ) * (((m : ℝ) + 1) / ((m : ℝ) * s))
    let V := fun L u : ℝ =>
      |signedWindowResidual m (Real.exp u) (Real.exp (u + L)) /
        powerGap s (Real.exp u) (Real.exp (u + L)) + cm + (μ r : ℝ) * rootSignal r u|
    (∀ᶠ L in 𝓝[>] (0 : ℝ), (atTop : Filter ℝ).IsBoundedUnder (· ≤ ·) (V L)) ∧
      Tendsto (fun L : ℝ => limsup (V L) atTop / (L * (Real.log (1 / L)) ^ 2))
        (𝓝[>] 0) (𝓝 (|(μ r : ℝ)| / (4 * Real.pi * s))) := by
  dsimp only
  let s := orderRate m
  let cm := (μ (m + 1) : ℝ) * (((m : ℝ) + 1) / ((m : ℝ) * s))
  let a := (μ r : ℝ)
  let F (L u : ℝ) := signedWindowResidual m (Real.exp u) (Real.exp (u + L)) /
    powerGap s (Real.exp u) (Real.exp (u + L)) + cm
  let V (L u : ℝ) := |F L u + a * rootSignal r u|
  let Vmid (L u : ℝ) := F L u + a * rootSignal r (u + L / 2)
  let logWidth (L : ℝ) := Real.log (1 / L)
  have hr : (1 : ℝ) < r := by exact_mod_cast (show 1 < r by omega)
  have hr0 : 0 < (r : ℝ) := zero_lt_one.trans hr
  have hq : (m : ℝ) + 1 = 2 * (r : ℝ) := by exact_mod_cast heven
  have hs' : s = 1 / 2 - (2 * (r : ℝ))⁻¹ := by dsimp [s, orderRate]; rw [hq]
  have hs : 0 < s := by
    rw [hs', inv_eq_one_div, sub_pos]
    exact (div_lt_iff₀ (by positivity)).2 (by linarith)
  obtain ⟨A, C, hA, hC, hspec⟩ := root_signal_quarter_phase_increment hRH hr
  obtain ⟨K, hK, hmid⟩ := signed_window_even_cutoff_midpoint_limsup hRH m r hm heven
  let t (L : ℝ) := L / (2 * (r : ℝ))
  let P (L : ℝ) := (r : ℝ) / (2 * Real.pi * s) * t L * (Real.log (t L)⁻¹) ^ 2
  let E (L : ℝ) := C * t L * (1 + Real.log (t L)⁻¹)
  let M (L : ℝ) := |a| * ((L / (8 * s)) * (logWidth L + Real.log (2 * (r : ℝ)) - 2 * c + 1 / 2) +
    K * L ^ 2 * (1 + logWidth L) ^ 2)
  let W (L : ℝ) := L * (logWidth L) ^ 2
  let H := min (1 / 4 : ℝ) (2 * (r : ℝ) / A)
  have hH : 0 < H := lt_min (by norm_num) (div_pos (by positivity) (by linarith))
  have hwidth : ∀ᶠ L in 𝓝[>] (0 : ℝ), L ∈ Ioc 0 H := Ioc_mem_nhdsGT hH
  have hband : ∀ᶠ L in 𝓝[>] (0 : ℝ),
      (atTop : Filter ℝ).IsBoundedUnder (· ≤ ·) (V L) ∧
        |limsup (V L) atTop - |a| * P L| ≤ |a| * E L + M L := by
    filter_upwards [hwidth] with L hL
    have hL' := hL.2.trans (min_le_left _ _)
    have ht : 0 < t L := div_pos hL.1 (by positivity)
    have htA : A * t L ≤ 1 := by
      dsimp only [t]
      rw [← mul_div_assoc, div_le_one₀ (by positivity : 0 < 2 * (r : ℝ)), mul_comm A]
      exact (le_div_iff₀ (show 0 < A by linarith)).1 (hL.2.trans (min_le_right _ _))
    have hshift : (r : ℝ) * t L = L / 2 := by
      dsimp only [t]
      field_simp [hr0.ne']
    obtain ⟨hup, hret⟩ := hspec (t L) ht htA
    rw [hshift, ← hs'] at hup hret
    obtain ⟨hmidBound, hmidEstimate⟩ := hmid L hL.1 hL'
    change (atTop : Filter ℝ).IsBoundedUnder (· ≤ ·) (fun u => |Vmid L u|) at hmidBound
    have hmidUpper : limsup (fun u => |Vmid L u|) atTop ≤ M L := by
      have h := (abs_le.mp hmidEstimate).2
      dsimp only [M, logWidth, Vmid, F, a, cm, s]
      linarith only [h]
    have hM : 0 ≤ M L :=
      (le_limsup_of_frequently_le (Frequently.of_forall fun u => abs_nonneg (Vmid L u))
        hmidBound).trans hmidUpper
    have hh := limsup_sub_signed_increment (Vmid L)
      (fun u => rootSignal r (u + L / 2) - rootSignal r u) a (P L) (E L) (M L)
      hM hmidBound hmidUpper hup (hret hquarter)
    have heq (u : ℝ) :
        |Vmid L u - a * (rootSignal r (u + L / 2) - rootSignal r u)| = V L u := by
      congr 1
      dsimp only [Vmid, V]
      ring
    simpa only [heq] using hh
  refine ⟨hband.mono (fun _ h => h.1), ?_⟩
  change Tendsto (fun L => limsup (V L) atTop / W L) _ (𝓝 (|a| / (4 * Real.pi * s)))
  have hlog_pos {L : ℝ} (hL : L ∈ Ioc 0 H) : 0 < logWidth L := by
    exact Real.log_pos ((lt_div_iff₀ hL.1).2 (by linarith [hL.2.trans (min_le_left _ _)]))
  have hlog_shift {L : ℝ} (hL : 0 < L) :
      Real.log (t L)⁻¹ = logWidth L + Real.log (2 * (r : ℝ)) := by
    dsimp only [t, logWidth]
    rw [inv_div, Real.log_div (by positivity) hL.ne', one_div, Real.log_inv]
    ring
  have hInvLog : Tendsto (fun L => (logWidth L)⁻¹) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    apply tendsto_inv_atTop_zero.comp
    simpa only [logWidth, Function.comp_def, one_div] using
      Real.tendsto_log_atTop.comp tendsto_inv_nhdsGT_zero
  have hLzero : Tendsto (fun L : ℝ => L) (𝓝[>] 0) (𝓝 0) :=
    nhdsWithin_le_nhds
  let midCoeff := Real.log (2 * (r : ℝ)) - 2 * c + 1 / 2
  let shift := Real.log (2 * (r : ℝ))
  let leading (z : ℝ) := |a| / (4 * Real.pi * s) * (1 + shift * z) ^ 2
  let error (x : ℝ × ℝ) := |a| * (
    C / (2 * (r : ℝ)) * (x.2 + (1 + shift) * x.2 ^ 2) +
    1 / (8 * s) * (x.2 + midCoeff * x.2 ^ 2) + K * x.1 * (1 + x.2) ^ 2)
  have hleading : Tendsto (fun L => |a| * P L / W L) (𝓝[>] (0 : ℝ))
      (𝓝 (|a| / (4 * Real.pi * s))) := by
    have hcont : Continuous leading := by unfold leading; fun_prop
    have htend := (hcont.tendsto (0 : ℝ)).comp hInvLog
    simp only [leading, mul_zero, add_zero, one_pow, mul_one] at htend
    refine htend.congr' ?_
    filter_upwards [hwidth] with L hL
    dsimp only [Function.comp_def, P, W, t, shift] at *
    rw [show Real.log (L / (2 * (r : ℝ)))⁻¹ =
      logWidth L + Real.log (2 * (r : ℝ)) by exact hlog_shift hL.1]
    field_simp [hr0.ne', hs.ne', Real.pi_ne_zero, (hlog_pos hL).ne', hL.1.ne']
    <;> ring
  have herror : Tendsto (fun L => (|a| * E L + M L) / W L) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hcont : Continuous error := by unfold error; fun_prop
    have htend := (hcont.tendsto ((0 : ℝ), (0 : ℝ))).comp (hLzero.prodMk_nhds hInvLog)
    have hzero : error (0, 0) = 0 := by simp [error]
    rw [hzero] at htend
    refine htend.congr' ?_
    filter_upwards [hwidth] with L hL
    change error (L, (logWidth L)⁻¹) = (|a| * E L + M L) / W L
    dsimp only [error, midCoeff, shift, E, M, W]
    rw [hlog_shift hL.1]
    dsimp only [t]
    field_simp [hr0.ne', hs.ne', (hlog_pos hL).ne', hL.1.ne']
    <;> ring
  have hdiff : Tendsto (fun L => limsup (V L) atTop / W L - |a| * P L / W L)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    apply tendsto_iff_norm_sub_tendsto_zero.2
    simp only [sub_zero, Real.norm_eq_abs]
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds herror
      (Eventually.of_forall fun L => abs_nonneg _) ?_
    filter_upwards [hwidth, hband] with L hL hbound
    have hW : 0 < W L := mul_pos hL.1 (sq_pos_of_pos (hlog_pos hL))
    rw [← sub_div, abs_div, abs_of_pos hW]
    exact div_le_div_of_nonneg_right hbound.2 hW.le
  simpa only [sub_add_cancel, zero_add] using hdiff.add hleading

#print axioms signed_window_even_cutoff_left_limsup

end D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder
