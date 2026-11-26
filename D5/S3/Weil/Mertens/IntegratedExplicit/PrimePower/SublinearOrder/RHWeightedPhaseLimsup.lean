/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHWeightedPhaseLimsup
   generality: I
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHWeightedPhaseLimsup
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The RH left-endpoint limsup is governed by weighted phase alignment. -/

import D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder.RHRootWeightedSine
import D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder.RHMobiusEvenCutoffLeftLimsup

/-! The harmonic mass normalizes the supremum of the finite sine polynomial. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter Set ArithmeticFunction
open scoped ArithmeticFunction.Moebius Topology

namespace D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder

open D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower
open D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelCusp (c)

/-- At cutoffs of positive harmonic mass, the deficit from full weighted sine alignment. -/
def weightedPhaseDefect (hRH : RiemannHypothesis) (T : ℝ) : ℝ :=
  1 - weightedSineSup hRH T / harmonicMass hRH T

private theorem map_reciprocal_width {a : ℝ} (ha : 0 < a) :
    map (fun L : ℝ => a / L) (𝓝[>] (0 : ℝ)) = atTop := by
  have hforward : Tendsto (fun L : ℝ => a / L) (𝓝[>] (0 : ℝ)) atTop := by
    simpa only [div_eq_mul_inv] using
      (tendsto_const_mul_atTop_of_pos ha).2 tendsto_inv_nhdsGT_zero
  have hreverse : Tendsto (fun T : ℝ => a / T) atTop (𝓝[>] (0 : ℝ)) := by
    have hdiv : Tendsto (fun T : ℝ => T / a) atTop atTop := by
      simpa only [div_eq_mul_inv, mul_comm, id_eq] using
        (tendsto_const_mul_atTop_of_pos (inv_pos.mpr ha)).2 tendsto_id
    simpa only [Function.comp_def, inv_div] using tendsto_inv_atTop_nhdsGT_zero.comp hdiv
  apply le_antisymm hforward
  calc
    atTop = map (fun T : ℝ => a / (a / T)) atTop := by
      simp only [div_div_eq_mul_div, mul_comm a, mul_div_cancel_right₀ _ ha.ne', map_id']
    _ = map (fun L : ℝ => a / L) (map (fun T : ℝ => a / T) atTop) := by
      rw [map_map]
      rfl
    _ ≤ _ := map_mono hreverse

set_option maxHeartbeats 800000 in
-- The estimates and filter identities use the normalizations of the original window.
/-- With the original signed normalization, the RH-only left-endpoint limsup
has the weighted-phase formula. For a nonzero Möbius factor its full coefficient
is attained as a limit exactly when the phase deficit tends to zero. -/
theorem signed_window_even_cutoff_weighted_phase (hRH : RiemannHypothesis)
    (m r : ℕ) (hm : 2 ≤ m) (heven : m + 1 = 2 * r) :
    let s := orderRate m
    let cm := (μ (m + 1) : ℝ) * (((m : ℝ) + 1) / ((m : ℝ) * s))
    let V := fun L u : ℝ =>
      |signedWindowResidual m (Real.exp u) (Real.exp (u + L)) /
        powerGap s (Real.exp u) (Real.exp (u + L)) + cm + (μ r : ℝ) * rootSignal r u|
    let Q := fun L : ℝ => limsup (V L) atTop / (L * (Real.log (1 / L)) ^ 2)
    let κ := |(μ r : ℝ)| / (4 * Real.pi * s)
    (∀ᶠ L in 𝓝[>] (0 : ℝ), (atTop : Filter ℝ).IsBoundedUnder (· ≤ ·) (V L)) ∧
      Tendsto (fun L : ℝ => Q L - κ * (1 - weightedPhaseDefect hRH (2 * (r : ℝ) / L)))
        (𝓝[>] 0) (𝓝 0) ∧
      (μ r ≠ 0 → (Tendsto Q (𝓝[>] 0) (𝓝 κ) ↔ Tendsto (weightedPhaseDefect hRH) atTop (𝓝 0))) := by
  dsimp only
  let s := orderRate m
  let cm := (μ (m + 1) : ℝ) * (((m : ℝ) + 1) / ((m : ℝ) * s))
  let a := (μ r : ℝ)
  let κ := |a| / (4 * Real.pi * s)
  let F (L u : ℝ) := signedWindowResidual m (Real.exp u) (Real.exp (u + L)) /
    powerGap s (Real.exp u) (Real.exp (u + L)) + cm
  let V (L u : ℝ) := |F L u + a * rootSignal r u|
  let Vmid (L u : ℝ) := F L u + a * rootSignal r (u + L / 2)
  let logWidth (L : ℝ) := Real.log (1 / L)
  let scale (L : ℝ) := L * (logWidth L) ^ 2
  let Q (L : ℝ) := limsup (V L) atTop / scale L
  let cutoff (L : ℝ) := 2 * (r : ℝ) / L
  change (∀ᶠ L in 𝓝[>] (0 : ℝ), (atTop : Filter ℝ).IsBoundedUnder (· ≤ ·) (V L)) ∧
    Tendsto (fun L => Q L - κ * (1 - weightedPhaseDefect hRH (cutoff L))) (𝓝[>] 0) (𝓝 0) ∧
    (μ r ≠ 0 → (Tendsto Q (𝓝[>] 0) (𝓝 κ) ↔ Tendsto (weightedPhaseDefect hRH) atTop (𝓝 0)))
  have hr : (1 : ℝ) < r := by exact_mod_cast (show 1 < r by omega)
  have hr₀ : 0 < (r : ℝ) := zero_lt_one.trans hr
  have heven' : (m : ℝ) + 1 = 2 * (r : ℝ) := by exact_mod_cast heven
  have hs' : s = 1 / 2 - (2 * (r : ℝ))⁻¹ := by dsimp [s, orderRate]; rw [heven']
  have hs : 0 < s := by
    rw [hs', inv_eq_one_div, sub_pos]
    exact (div_lt_iff₀ (by positivity)).2 (by linarith)
  obtain ⟨C, _, hspec⟩ := root_signal_weighted_sine_return hRH hr
  obtain ⟨K, _, hmid⟩ := signed_window_even_cutoff_midpoint_limsup hRH m r hm heven
  let P (L : ℝ) := L / s * weightedSineSup hRH (cutoff L)
  let E (L : ℝ) := C * ((L / 2) * Real.log (1 / (L / 2)))
  let midCoeff := Real.log (2 * (r : ℝ)) - 2 * c + 1 / 2
  let M (L : ℝ) := |a| * ((L / (8 * s)) * (logWidth L + midCoeff) +
    K * L ^ 2 * (1 + logWidth L) ^ 2)
  let H := min (1 / 4 : ℝ) (2 * (Real.exp 1)⁻¹)
  have hwidth : ∀ᶠ L in 𝓝[>] (0 : ℝ), L ∈ Ioc 0 H :=
    Ioc_mem_nhdsGT (lt_min (by norm_num) (by positivity))
  have hband : ∀ᶠ L in 𝓝[>] (0 : ℝ),
      (atTop : Filter ℝ).IsBoundedUnder (· ≤ ·) (V L) ∧
        |limsup (V L) atTop - |a| * P L| ≤ |a| * E L + M L := by
    filter_upwards [hwidth] with L hL
    have hL' := hL.2.trans (min_le_left _ _)
    have hh : L / 2 ≤ (Real.exp 1)⁻¹ := by
      linarith only [hL.2.trans (min_le_right _ _)]
    have hspecL := hspec (L / 2) (half_pos hL.1) hh
    dsimp only at hspecL
    rw [← hs', show 2 * (L / 2) = L by ring,
      show (r : ℝ) / (L / 2) = cutoff L by dsimp only [cutoff]; field_simp] at hspecL
    obtain ⟨hmidBound, hmidEstimate⟩ := hmid L hL.1 hL'
    change (atTop : Filter ℝ).IsBoundedUnder (· ≤ ·) (fun u => |Vmid L u|) at hmidBound
    have hmidUpper : limsup (fun u => |Vmid L u|) atTop ≤ M L := by
      have h := (abs_le.mp hmidEstimate).2
      dsimp only [M, midCoeff, logWidth, Vmid, F, a, cm, s]
      linarith only [h]
    have hM : 0 ≤ M L :=
      (le_limsup_of_frequently_le (Frequently.of_forall fun u => abs_nonneg (Vmid L u))
        hmidBound).trans hmidUpper
    have h := limsup_sub_signed_increment (Vmid L)
      (fun u => rootSignal r (u + L / 2) - rootSignal r u) a (P L) (E L) (M L)
      hM hmidBound hmidUpper hspecL.1 hspecL.2
    have heq (u : ℝ) :
        |Vmid L u - a * (rootSignal r (u + L / 2) - rootSignal r u)| = V L u := by
      congr 1
      dsimp only [Vmid, V]
      ring
    simpa only [heq] using h
  refine ⟨hband.mono (fun _ h => h.1), ?_⟩
  have hlog_pos {L : ℝ} (hL : L ∈ Ioc 0 H) : 0 < logWidth L :=
    Real.log_pos ((lt_div_iff₀ hL.1).2 (by linarith [hL.2.trans (min_le_left _ _)]))
  have hlog_scale {L d : ℝ} (hL : 0 < L) (hd : 0 < d) :
      Real.log (d / L) = logWidth L + Real.log d := by
    dsimp only [logWidth]
    rw [Real.log_div hd.ne' hL.ne', Real.log_div one_ne_zero hL.ne', Real.log_one]
    ring
  have hinvlog : Tendsto (fun L => (logWidth L)⁻¹) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    apply tendsto_inv_atTop_zero.comp
    simpa only [logWidth, Function.comp_def, one_div] using
      Real.tendsto_log_atTop.comp tendsto_inv_nhdsGT_zero
  have hLzero : Tendsto (fun L : ℝ => L) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
  let error (x : ℝ × ℝ) := |a| * (C / 2 * (x.2 + Real.log 2 * x.2 ^ 2) +
    1 / (8 * s) * (x.2 + midCoeff * x.2 ^ 2) + K * x.1 * (1 + x.2) ^ 2)
  have herror : Tendsto (fun L => (|a| * E L + M L) / scale L) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hcont : Continuous error := by unfold error; fun_prop
    have htend := (hcont.tendsto ((0 : ℝ), (0 : ℝ))).comp (hLzero.prodMk_nhds hinvlog)
    have hzero : error (0, 0) = 0 := by simp [error]
    rw [hzero] at htend
    refine htend.congr' ?_
    filter_upwards [hwidth] with L hL
    change error (L, (logWidth L)⁻¹) = (|a| * E L + M L) / scale L
    dsimp only [error, E, M, scale]
    rw [show 1 / (L / 2) = 2 / L by rw [div_div_eq_mul_div, one_mul],
      hlog_scale hL.1 (by norm_num : 0 < (2 : ℝ))]
    field_simp [hs.ne', (hlog_pos hL).ne', hL.1.ne']
    <;> ring
  have hdiff : Tendsto (fun L => Q L - |a| * P L / scale L) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    apply (tendsto_zero_iff_abs_tendsto_zero _).2
    refine squeeze_zero' (Eventually.of_forall fun _ => abs_nonneg _) ?_ herror
    filter_upwards [hwidth, hband] with L hL hbound
    have hscale : 0 < scale L := mul_pos hL.1 (sq_pos_of_pos (hlog_pos hL))
    dsimp only [Function.comp_def, Q]
    rw [← sub_div, abs_div, abs_of_pos hscale]
    exact div_le_div_of_nonneg_right hbound.2 hscale.le
  have hcutoff : map cutoff (𝓝[>] (0 : ℝ)) = atTop :=
    map_reciprocal_width (mul_pos two_pos hr₀)
  have hcut : Tendsto cutoff (𝓝[>] (0 : ℝ)) atTop := hcutoff.le
  have hratio : Tendsto (fun L => (Real.log (cutoff L) / logWidth L) ^ 2)
      (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    have h := ((hinvlog.const_mul (Real.log (2 * (r : ℝ)))).const_add 1).pow 2
    simp only [mul_zero, add_zero, one_pow] at h
    refine h.congr' ?_
    filter_upwards [hwidth] with L hL
    rw [show Real.log (cutoff L) = logWidth L + Real.log (2 * (r : ℝ)) from
      hlog_scale hL.1 (by positivity)]
    rw [add_div, div_self (hlog_pos hL).ne', div_eq_mul_inv]
  let massScale (L : ℝ) := |a| / s * (harmonicMass hRH (cutoff L) / (logWidth L) ^ 2)
  have hmassScale : Tendsto massScale (𝓝[>] (0 : ℝ)) (𝓝 κ) := by
    have h := (((harmonic_mass_limit hRH).comp hcut).mul hratio).const_mul (|a| / s)
    rw [mul_one, show |a| / s * (1 / (4 * Real.pi)) = κ by
      dsimp only [κ]; field_simp] at h
    apply h.congr'
    filter_upwards [hcut.eventually_ge_atTop 2, hwidth] with L hT hL
    have hlogT : 0 < Real.log (cutoff L) := Real.log_pos (by linarith)
    dsimp only [Function.comp_def, massScale]
    field_simp [hlogT.ne', (hlog_pos hL).ne']
  have hmassPos : ∀ᶠ L in 𝓝[>] (0 : ℝ), 0 < harmonicMass hRH (cutoff L) := by
    filter_upwards [((harmonic_mass_limit hRH).comp hcut).eventually_const_lt
        (by positivity : 0 < 1 / (4 * Real.pi))] with L h
    exact ((div_pos_iff.mp h).resolve_right (fun hn => (not_lt_of_ge (sq_nonneg _)) hn.2)).1
  have hlead : Tendsto (fun L => |a| * P L / scale L -
      κ * (1 - weightedPhaseDefect hRH (cutoff L))) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hdiffScale : Tendsto (fun L => massScale L - κ) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      simpa only [sub_self] using hmassScale.sub (tendsto_const_nhds (x := κ))
    have hsmall := (tendsto_zero_iff_abs_tendsto_zero _).1 hdiffScale
    apply (tendsto_zero_iff_abs_tendsto_zero _).2
    refine squeeze_zero' (Eventually.of_forall fun _ => abs_nonneg _) ?_ hsmall
    filter_upwards [hwidth, hmassPos] with L hL hpos
    let ρ := weightedSineSup hRH (cutoff L) / harmonicMass hRH (cutoff L)
    obtain ⟨hlo, hhi⟩ := weighted_sine_sup_bounds hRH (cutoff L)
    have hρ : 0 ≤ ρ := div_nonneg hlo hpos.le
    have hρ' : ρ ≤ 1 := (div_le_one₀ hpos).2 hhi
    have heq : |a| * P L / scale L - κ * (1 - weightedPhaseDefect hRH (cutoff L)) =
        (massScale L - κ) * ρ := by
      dsimp only [weightedPhaseDefect, P, scale, massScale, ρ]
      rw [sub_sub_cancel]
      field_simp [hs.ne', hL.1.ne', (hlog_pos hL).ne', hpos.ne']
      <;> ring
    dsimp only [Function.comp_def]
    rw [heq, abs_mul, abs_of_nonneg hρ]
    exact mul_le_of_le_one_right (abs_nonneg _) hρ'
  have hformula : Tendsto (fun L => Q L - κ * (1 - weightedPhaseDefect hRH (cutoff L)))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h := hdiff.add hlead
    rw [zero_add] at h
    exact h.congr (fun L => by ring)
  refine ⟨hformula, fun hμ => ?_⟩
  have ha : a ≠ 0 := by
    change (μ r : ℝ) ≠ 0
    exact_mod_cast hμ
  have hk : 0 < κ := div_pos (abs_pos.mpr ha) (by positivity)
  have hcomp : Tendsto (fun L => weightedPhaseDefect hRH (cutoff L)) (𝓝[>] (0 : ℝ)) (𝓝 0) ↔
      Tendsto (weightedPhaseDefect hRH) atTop (𝓝 0) := by
    rw [← hcutoff, tendsto_map'_iff]
    rfl
  rw [← hcomp]
  constructor
  · intro hfull
    have h := (hformula.sub (hfull.sub (tendsto_const_nhds (x := κ)))).div_const κ
    simp only [sub_self, div_zero, zero_div] at h
    refine h.congr (fun L => ?_)
    field_simp [hk.ne']
    <;> ring
  · intro hD
    have h := hformula.add (((tendsto_const_nhds (x := (1 : ℝ))).sub hD).const_mul κ)
    simpa only [sub_zero, mul_one, zero_add, sub_add_cancel] using h

#print axioms signed_window_even_cutoff_weighted_phase

end D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder
