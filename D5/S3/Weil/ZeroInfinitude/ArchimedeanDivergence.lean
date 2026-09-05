/- GID: D5/S3/Weil/ZeroInfinitude/ArchimedeanDivergence
   generality: G
   mirror-B: D5/B/S3/Weil/ZeroInfinitude/ArchimedeanDivergence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Translated nonnegative packets have a quantified mu-weighted lower bound and diverge. -/

import D5.S3.Weil.ZetaGamma.GammaStirlingVert
import D5.S3.Weil.ZetaCore.ExplicitFormula
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

open Filter MeasureTheory Set
open scoped Topology

noncomputable section

namespace D5.S3.Weil.ZeroInfinitude.ArchimedeanDivergence

def packet (H : ℝ → ℝ) (T r : ℝ) : ℝ :=
  (H (r + T) + H (r - T)) / 2

private theorem packet_integrable {H : ℝ → ℝ} (hH : Integrable H) (T : ℝ) :
    Integrable (packet H T) := by
  exact ((hH.comp_add_right T).add (hH.comp_sub_right T)).div_const 2

theorem packet_integral {H : ℝ → ℝ} (hH : Integrable H) (T : ℝ) :
    ∫ r : ℝ, packet H T r = ∫ r : ℝ, H r := by
  rw [show packet H T = fun r => (H (r + T) + H (r - T)) / 2 by rfl,
    integral_div, integral_add (hH.comp_add_right T) (hH.comp_sub_right T),
    integral_add_right_eq_self H T, integral_sub_right_eq_self H T]
  ring

theorem mu_add_one_pos (r : ℝ) : 0 < Zeta23.mu r + 1 := by
  have h0 := Zeta23.MuFields.neg_one_lt_mu_zero
  have hr := Zeta23.MuFields.mu_zero_le r
  linarith

theorem mu_tendsto_atTop : Tendsto Zeta23.mu atTop atTop := by
  obtain ⟨C, hC⟩ := Zeta23.StirlingVert.mu_stirling
  have hlog : Tendsto (fun T : ℝ => Real.log (T / (2 * Real.pi))) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_id.atTop_div_const (by positivity))
  have hmain :
      Tendsto (fun T : ℝ => (1 / (2 * Real.pi)) * Real.log (T / (2 * Real.pi)))
        atTop atTop :=
    hlog.const_mul_atTop (by positivity)
  have hlower :
      Tendsto
        (fun T : ℝ =>
          (1 / (2 * Real.pi)) * Real.log (T / (2 * Real.pi)) - |C|)
        atTop atTop := by
    simpa [sub_eq_add_neg] using
      (tendsto_atTop_add_const_right atTop (-|C|) hmain)
  apply tendsto_atTop_mono' atTop _ hlower
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
  have hTabs : |T| = T := abs_of_nonneg (by linarith)
  have hst := hC T (by simpa [hTabs] using hT)
  have hT2 : 0 < T ^ 2 := sq_pos_of_pos (lt_of_lt_of_le zero_lt_one hT)
  have hT2one : 1 ≤ T ^ 2 := by nlinarith
  have hCdiv : C / T ^ 2 ≤ |C| := by
    by_cases hC0 : 0 ≤ C
    · rw [abs_of_nonneg hC0]
      exact (div_le_iff₀ hT2).2 (by nlinarith)
    · have : C / T ^ 2 < 0 := div_neg_of_neg_of_pos (lt_of_not_ge hC0) hT2
      exact this.le.trans (abs_nonneg C)
  rw [hTabs] at hst
  have hdiff :
      -(C / T ^ 2) ≤
        Zeta23.mu T -
          (1 / (2 * Real.pi)) * Real.log (T / (2 * Real.pi)) := by
    exact (abs_le.mp hst).1
  linarith

private theorem abs_mu_growth :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ r : ℝ, |Zeta23.mu r| ≤ K * (1 + |r|) ^ (1 / 2 : ℝ) := by
  obtain ⟨C, hC⟩ := Zeta23.StirlingVert.mu_stirling
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (Zeta23.mu_smooth.continuous.continuousOn (s := Icc (-1 : ℝ) 1))
  have hpi : 0 < 1 / (2 * Real.pi) := by positivity
  let K : ℝ := max M 0 + |C| +
    (1 / (2 * Real.pi)) * |Real.log (2 * Real.pi)| + 1 / Real.pi
  have hK : 0 ≤ K := by
    dsimp [K]
    positivity
  refine ⟨K, hK, fun r => ?_⟩
  have hone : 1 ≤ (1 + |r|) ^ (1 / 2 : ℝ) :=
    Real.one_le_rpow (by linarith [abs_nonneg r]) (by norm_num)
  rcases le_or_gt |r| 1 with hr | hr
  · have hm := hM r (abs_le.mp hr)
    rw [Real.norm_eq_abs] at hm
    calc
      |Zeta23.mu r| ≤ max M 0 := hm.trans (le_max_left _ _)
      _ ≤ K * 1 := by
        rw [mul_one]
        dsimp [K]
        have hlognonneg : 0 ≤
            (1 / (2 * Real.pi)) * |Real.log (2 * Real.pi)| :=
          mul_nonneg hpi.le (abs_nonneg _)
        have hinvpi : 0 ≤ 1 / Real.pi := by positivity
        linarith [abs_nonneg C]
      _ ≤ K * (1 + |r|) ^ (1 / 2 : ℝ) := by gcongr
  · have hr1 : 1 ≤ |r| := hr.le
    have hst := hC r hr1
    have hrsq : 1 ≤ r ^ 2 := by rw [← sq_abs]; nlinarith
    have hCr : C / r ^ 2 ≤ |C| := by
      calc
        C / r ^ 2 ≤ |C| / r ^ 2 := by gcongr; exact le_abs_self C
        _ ≤ |C| := div_le_self (abs_nonneg C) hrsq
    have hlog : |Real.log (|r| / (2 * Real.pi))| ≤
        Real.log |r| + |Real.log (2 * Real.pi)| := by
      rw [Real.log_div (by positivity) (by positivity)]
      calc
        |Real.log |r| - Real.log (2 * Real.pi)| ≤
            |Real.log (|r|)| + |Real.log (2 * Real.pi)| := abs_sub _ _
        _ = Real.log |r| + |Real.log (2 * Real.pi)| := by
          rw [abs_of_nonneg (Real.log_nonneg hr1)]
    have hlog2 : Real.log |r| ≤ 2 * (1 + |r|) ^ (1 / 2 : ℝ) := by
      have hraw := Real.log_le_rpow_div (abs_nonneg r) (by norm_num : (0 : ℝ) < 1 / 2)
      have hmono : |r| ^ (1 / 2 : ℝ) ≤ (1 + |r|) ^ (1 / 2 : ℝ) :=
        Real.rpow_le_rpow (abs_nonneg r) (by linarith) (by norm_num)
      calc
        Real.log |r| ≤ |r| ^ (1 / 2 : ℝ) / (1 / 2) := hraw
        _ = 2 * |r| ^ (1 / 2 : ℝ) := by ring
        _ ≤ 2 * (1 + |r|) ^ (1 / 2 : ℝ) := by gcongr
    have hmub : |Zeta23.mu r| ≤
        |C| + (1 / (2 * Real.pi)) *
          (Real.log |r| + |Real.log (2 * Real.pi)|) := by
      have htri : |Zeta23.mu r| ≤
          |Zeta23.mu r - (1 / (2 * Real.pi)) *
            Real.log (|r| / (2 * Real.pi))| +
          |(1 / (2 * Real.pi)) * Real.log (|r| / (2 * Real.pi))| := by
        have hadd := abs_add_le
          (Zeta23.mu r - (1 / (2 * Real.pi)) * Real.log (|r| / (2 * Real.pi)))
          ((1 / (2 * Real.pi)) * Real.log (|r| / (2 * Real.pi)))
        rwa [sub_add_cancel] at hadd
      calc
        |Zeta23.mu r| ≤ C / r ^ 2 +
            |(1 / (2 * Real.pi)) * Real.log (|r| / (2 * Real.pi))| := by
          linarith
        _ ≤ |C| + (1 / (2 * Real.pi)) *
            (Real.log |r| + |Real.log (2 * Real.pi)|) := by
          rw [abs_mul, abs_of_pos hpi]
          gcongr
    let b : ℝ := (1 + |r|) ^ (1 / 2 : ℝ)
    calc
      |Zeta23.mu r| ≤
          |C| + (1 / (2 * Real.pi)) *
            (Real.log |r| + |Real.log (2 * Real.pi)|) := hmub
      _ ≤ |C| + (1 / (2 * Real.pi)) *
          (2 * b + |Real.log (2 * Real.pi)|) := by gcongr
      _ = (|C| + (1 / (2 * Real.pi)) * |Real.log (2 * Real.pi)|) * 1 +
          (1 / Real.pi) * b := by ring
      _ ≤ (|C| + (1 / (2 * Real.pi)) * |Real.log (2 * Real.pi)|) * b +
          (1 / Real.pi) * b := by gcongr
      _ = (|C| + (1 / (2 * Real.pi)) * |Real.log (2 * Real.pi)| +
          1 / Real.pi) * b := by ring
      _ ≤ K * b := by
        gcongr
        dsimp [K]
        linarith [le_max_right M 0]

private theorem integrable_mul_mu_of_decay
    {φ : ℝ → ℝ} (hφm : AEStronglyMeasurable φ) {K : ℝ}
    (hφ : ∀ r : ℝ, |φ r| ≤ K / (1 + r ^ 2)) :
    Integrable (fun r : ℝ => φ r * Zeta23.mu r) := by
  obtain ⟨Kmu, hKmu, hmu⟩ := abs_mu_growth
  have hmeas : AEStronglyMeasurable (fun r : ℝ => φ r * Zeta23.mu r) :=
    hφm.mul Zeta23.mu_smooth.continuous.aestronglyMeasurable
  have hdom : Integrable
      (fun r : ℝ => 2 * K * Kmu * (1 + ‖r‖) ^ (-(3 / 2) : ℝ)) :=
    (integrable_one_add_norm (E := ℝ) (μ := volume)
      (by rw [Module.finrank_self]; norm_num)).const_mul _
  refine hdom.mono' hmeas (Eventually.of_forall fun r => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  have hb : 0 < 1 + |r| := by linarith [abs_nonneg r]
  have hden : 0 < 1 + r ^ 2 := by positivity
  have h1 : |φ r| * (1 + r ^ 2) ≤ K := by
    calc
      |φ r| * (1 + r ^ 2) ≤ (K / (1 + r ^ 2)) * (1 + r ^ 2) :=
        mul_le_mul_of_nonneg_right (hφ r) hden.le
      _ = K := by field_simp
  have h2 := hmu r
  have hsq : (1 + |r|) ^ (2 : ℝ) ≤ 2 * (1 + r ^ 2) := by
    rw [Real.rpow_two]
    nlinarith [sq_abs r, sq_nonneg (1 - |r|)]
  have hkey : (1 + |r|) ^ (1 / 2 : ℝ) ≤
      2 * (1 + r ^ 2) * (1 + |r|) ^ (-(3 / 2) : ℝ) := by
    rw [show (1 / 2 : ℝ) = 2 + (-(3 / 2)) by norm_num, Real.rpow_add hb]
    exact mul_le_mul_of_nonneg_right hsq (Real.rpow_nonneg hb.le _)
  calc
    |φ r| * |Zeta23.mu r| ≤
        |φ r| * (Kmu * (1 + |r|) ^ (1 / 2 : ℝ)) := by gcongr
    _ ≤ |φ r| *
        (Kmu * (2 * (1 + r ^ 2) * (1 + |r|) ^ (-(3 / 2) : ℝ))) := by gcongr
    _ = (|φ r| * (1 + r ^ 2)) *
        (2 * Kmu * (1 + |r|) ^ (-(3 / 2) : ℝ)) := by ring
    _ ≤ K * (2 * Kmu * (1 + |r|) ^ (-(3 / 2) : ℝ)) := by gcongr
    _ = 2 * K * Kmu * (1 + |r|) ^ (-(3 / 2) : ℝ) := by ring

private theorem packet_decay
    {H : ℝ → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (hdecay : ∀ x : ℝ, |H x| ≤ K / (1 + x ^ 2)) (T : ℝ) :
    ∀ r : ℝ, |packet H T r| ≤ (2 * K * (1 + T ^ 2)) / (1 + r ^ 2) := by
  intro r
  have hden : 0 < 1 + r ^ 2 := by positivity
  have hplusRatio :
      1 + r ^ 2 ≤ 2 * (1 + T ^ 2) * (1 + (r + T) ^ 2) := by
    have hbase : r ^ 2 ≤ 2 * (r + T) ^ 2 + 2 * T ^ 2 := by
      nlinarith [sq_nonneg (r + 2 * T)]
    have hcross : 0 ≤ T ^ 2 * (r + T) ^ 2 :=
      mul_nonneg (sq_nonneg T) (sq_nonneg (r + T))
    nlinarith
  have hminusRatio :
      1 + r ^ 2 ≤ 2 * (1 + T ^ 2) * (1 + (r - T) ^ 2) := by
    have hbase : r ^ 2 ≤ 2 * (r - T) ^ 2 + 2 * T ^ 2 := by
      nlinarith [sq_nonneg (r - 2 * T)]
    have hcross : 0 ≤ T ^ 2 * (r - T) ^ 2 :=
      mul_nonneg (sq_nonneg T) (sq_nonneg (r - T))
    nlinarith
  have hplus : |H (r + T)| ≤ (2 * K * (1 + T ^ 2)) / (1 + r ^ 2) := by
    apply (le_div_iff₀ hden).2
    calc
      |H (r + T)| * (1 + r ^ 2) ≤
          (K / (1 + (r + T) ^ 2)) * (1 + r ^ 2) :=
        mul_le_mul_of_nonneg_right (hdecay (r + T)) hden.le
      _ = K * ((1 + r ^ 2) / (1 + (r + T) ^ 2)) := by ring
      _ ≤ K * (2 * (1 + T ^ 2)) := by
        apply mul_le_mul_of_nonneg_left _ hK
        exact (div_le_iff₀ (by positivity : 0 < 1 + (r + T) ^ 2)).2 hplusRatio
      _ = 2 * K * (1 + T ^ 2) := by ring
  have hminus : |H (r - T)| ≤ (2 * K * (1 + T ^ 2)) / (1 + r ^ 2) := by
    apply (le_div_iff₀ hden).2
    calc
      |H (r - T)| * (1 + r ^ 2) ≤
          (K / (1 + (r - T) ^ 2)) * (1 + r ^ 2) :=
        mul_le_mul_of_nonneg_right (hdecay (r - T)) hden.le
      _ = K * ((1 + r ^ 2) / (1 + (r - T) ^ 2)) := by ring
      _ ≤ K * (2 * (1 + T ^ 2)) := by
        apply mul_le_mul_of_nonneg_left _ hK
        exact (div_le_iff₀ (by positivity : 0 < 1 + (r - T) ^ 2)).2 hminusRatio
      _ = 2 * K * (1 + T ^ 2) := by ring
  calc
    |packet H T r| = |H (r + T) + H (r - T)| / 2 := by
      simp [packet, abs_div]
    _ ≤ (|H (r + T)| + |H (r - T)|) / 2 := by
      gcongr
      exact abs_add_le _ _
    _ ≤ (((2 * K * (1 + T ^ 2)) / (1 + r ^ 2)) +
          ((2 * K * (1 + T ^ 2)) / (1 + r ^ 2))) / 2 := by gcongr
    _ = (2 * K * (1 + T ^ 2)) / (1 + r ^ 2) := by ring

theorem packet_weighted_integrable_of_decay
    {H : ℝ → ℝ} (hH : Integrable H) {K : ℝ} (hK : 0 ≤ K)
    (hdecay : ∀ x : ℝ, |H x| ≤ K / (1 + x ^ 2)) (T : ℝ) :
    Integrable (fun r => packet H T r * Zeta23.mu r) :=
  integrable_mul_mu_of_decay (packet_integrable hH T).aestronglyMeasurable
    (packet_decay hK hdecay T)

private theorem archimedean_lower_bound_of_weighted
    {H : ℝ → ℝ} (hH : Integrable H) (hHnonneg : ∀ r, 0 ≤ H r)
    {δ : ℝ} (hδ : 0 < δ)
    (hlocal : ∀ t, |t| ≤ δ → (1 / 2 : ℝ) ≤ H t)
    (hweighted : ∀ T : ℝ, Integrable (fun r => packet H T r * Zeta23.mu r))
    {T : ℝ} (hT : δ ≤ T) :
    δ / 2 * (Zeta23.mu (T - δ) + 1) - (∫ r : ℝ, H r) ≤
      ∫ r : ℝ, packet H T r * Zeta23.mu r := by
  let G : ℝ → ℝ := fun r => packet H T r * (Zeta23.mu r + 1)
  have hFint : Integrable (packet H T) := packet_integrable hH T
  have hGint : Integrable G := by
    have hadd := (hweighted T).add hFint
    apply hadd.congr
    filter_upwards with r
    dsimp [G]
    ring
  have hFnonneg : ∀ r, 0 ≤ packet H T r := by
    intro r
    dsimp [packet]
    exact div_nonneg (add_nonneg (hHnonneg (r + T)) (hHnonneg (r - T))) (by norm_num)
  have hGnonneg : ∀ r, 0 ≤ G r := by
    intro r
    exact mul_nonneg (hFnonneg r) (mu_add_one_pos r).le
  have hrestrict : ∫ r in Icc (T - δ) (T + δ), G r ≤ ∫ r, G r :=
    setIntegral_le_integral hGint (ae_of_all _ hGnonneg)
  have hpoint : ∀ r ∈ Icc (T - δ) (T + δ),
      (1 / 4 : ℝ) * (Zeta23.mu (T - δ) + 1) ≤ G r := by
    intro r hr
    have hrsub : |r - T| ≤ δ := by
      rw [abs_le]
      constructor <;> linarith [hr.1, hr.2]
    have hFlocal : (1 / 4 : ℝ) ≤ packet H T r := by
      have hloc := hlocal (r - T) hrsub
      dsimp [packet]
      nlinarith [hHnonneg (r + T)]
    have hleft0 : 0 ≤ T - δ := sub_nonneg.mpr hT
    have hr0 : 0 ≤ r := hleft0.trans hr.1
    have hmu := Zeta23.MuFields.mu_monotoneOn
      (Set.mem_Ici.mpr hleft0) (Set.mem_Ici.mpr hr0) hr.1
    dsimp [G]
    exact mul_le_mul hFlocal (by simpa [add_comm] using add_le_add_right hmu 1)
      (mu_add_one_pos (T - δ)).le (hFnonneg r)
  have hmeasure : volume.real (Icc (T - δ) (T + δ)) = 2 * δ := by
    rw [measureReal_def, Real.volume_Icc, ENNReal.toReal_ofReal]
    · ring
    · linarith
  have hset :
      (1 / 4 : ℝ) * (Zeta23.mu (T - δ) + 1) *
          volume.real (Icc (T - δ) (T + δ)) ≤
        ∫ r in Icc (T - δ) (T + δ), G r :=
    setIntegral_ge_of_const_le_real measurableSet_Icc measure_Icc_lt_top.ne hpoint
      hGint.integrableOn
  have hGlower :
      δ / 2 * (Zeta23.mu (T - δ) + 1) ≤ ∫ r, G r := by
    rw [hmeasure] at hset
    nlinarith [hset.trans hrestrict]
  have hGvalue :
      (∫ r, G r) =
        (∫ r, packet H T r * Zeta23.mu r) + ∫ r, H r := by
    calc
      (∫ r, G r) =
          ∫ r, packet H T r * Zeta23.mu r + packet H T r := by
            apply integral_congr_ae
            filter_upwards with r
            dsimp [G]
            ring
      _ = (∫ r, packet H T r * Zeta23.mu r) + ∫ r, packet H T r :=
        integral_add (hweighted T) hFint
      _ = (∫ r, packet H T r * Zeta23.mu r) + ∫ r, H r := by
        rw [packet_integral hH T]
  rw [hGvalue] at hGlower
  linarith

theorem archimedean_lower_bound
    {H : ℝ → ℝ} (hH : Integrable H) (hHnonneg : ∀ r, 0 ≤ H r)
    {δ : ℝ} (hδ : 0 < δ)
    (hlocal : ∀ t, |t| ≤ δ → (1 / 2 : ℝ) ≤ H t)
    {K : ℝ} (hK : 0 ≤ K)
    (hdecay : ∀ x, |H x| ≤ K / (1 + x ^ 2))
    {T : ℝ} (hT : δ ≤ T) :
    δ / 2 * (Zeta23.mu (T - δ) + 1) - (∫ r, H r) ≤
      ∫ r, packet H T r * Zeta23.mu r := by
  exact archimedean_lower_bound_of_weighted hH hHnonneg hδ hlocal
    (fun S => packet_weighted_integrable_of_decay hH hK hdecay S) hT

private theorem archimedean_divergence
    {H : ℝ → ℝ} (hH : Integrable H) (hHnonneg : ∀ r, 0 ≤ H r)
    {δ : ℝ} (hδ : 0 < δ)
    (hlocal : ∀ t, |t| ≤ δ → (1 / 2 : ℝ) ≤ H t)
    (hweighted : ∀ T : ℝ, Integrable (fun r => packet H T r * Zeta23.mu r)) :
    Tendsto (fun T : ℝ => ∫ r : ℝ, packet H T r * Zeta23.mu r) atTop atTop := by
  have hshift : Tendsto (fun T : ℝ => T - δ) atTop atTop := by
    simpa [sub_eq_add_neg] using
      (tendsto_atTop_add_const_right atTop (-δ) tendsto_id)
  have hmu : Tendsto (fun T : ℝ => Zeta23.mu (T - δ)) atTop atTop :=
    mu_tendsto_atTop.comp hshift
  have hmu1 : Tendsto (fun T : ℝ => Zeta23.mu (T - δ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 hmu
  have hscaled :
      Tendsto (fun T : ℝ => δ / 2 * (Zeta23.mu (T - δ) + 1)) atTop atTop :=
    hmu1.const_mul_atTop (by positivity)
  have hlower :
      Tendsto
        (fun T : ℝ => δ / 2 * (Zeta23.mu (T - δ) + 1) - (∫ r : ℝ, H r))
        atTop atTop := by
    simpa [sub_eq_add_neg] using
      (tendsto_atTop_add_const_right atTop (-(∫ r : ℝ, H r)) hscaled)
  apply tendsto_atTop_mono' atTop _ hlower
  filter_upwards [eventually_ge_atTop δ] with T hT
  exact archimedean_lower_bound_of_weighted hH hHnonneg hδ hlocal hweighted hT

theorem archimedean_divergence_of_decay
    {H : ℝ → ℝ} (hH : Integrable H) (hHnonneg : ∀ r, 0 ≤ H r)
    {δ : ℝ} (hδ : 0 < δ)
    (hlocal : ∀ t, |t| ≤ δ → (1 / 2 : ℝ) ≤ H t)
    {K : ℝ} (hK : 0 ≤ K)
    (hdecay : ∀ x : ℝ, |H x| ≤ K / (1 + x ^ 2)) :
    Tendsto (fun T : ℝ => ∫ r : ℝ, packet H T r * Zeta23.mu r) atTop atTop := by
  apply archimedean_divergence hH hHnonneg hδ hlocal
  exact fun T => packet_weighted_integrable_of_decay hH hK hdecay T

private theorem complex_packet_integral_re
    {H : ℝ → ℝ} {T : ℝ}
    (hweighted : Integrable (fun r => packet H T r * Zeta23.mu r)) :
    (∫ r : ℝ, (packet H T r : ℂ) * (Zeta23.mu r : ℂ)).re =
      ∫ r : ℝ, packet H T r * Zeta23.mu r := by
  have hcomplex :
      Integrable (fun r : ℝ => (packet H T r : ℂ) * (Zeta23.mu r : ℂ)) := by
    convert hweighted.ofReal using 1
    norm_num
  calc
    (∫ r : ℝ, (packet H T r : ℂ) * (Zeta23.mu r : ℂ)).re =
        ∫ r : ℝ, Complex.re ((packet H T r : ℂ) * (Zeta23.mu r : ℂ)) :=
      (integral_re hcomplex).symm
    _ = ∫ r : ℝ, packet H T r * Zeta23.mu r := by
      apply integral_congr_ae
      filter_upwards with r
      norm_num

theorem archimedean_divergence_complex_of_decay
    {H : ℝ → ℝ} (hH : Integrable H) (hHnonneg : ∀ r, 0 ≤ H r)
    {δ : ℝ} (hδ : 0 < δ)
    (hlocal : ∀ t, |t| ≤ δ → (1 / 2 : ℝ) ≤ H t)
    {K : ℝ} (hK : 0 ≤ K)
    (hdecay : ∀ x : ℝ, |H x| ≤ K / (1 + x ^ 2)) :
    Tendsto
      (fun T : ℝ =>
        (∫ r : ℝ, (packet H T r : ℂ) * (Zeta23.mu r : ℂ)).re)
      atTop atTop := by
  have hreal :=
    archimedean_divergence_of_decay hH hHnonneg hδ hlocal hK hdecay
  convert hreal using 1
  funext T
  exact complex_packet_integral_re
    (packet_weighted_integrable_of_decay hH hK hdecay T)

theorem gamma_term_packet
    (k : ℝ → ℂ) {H : ℝ → ℝ} {T : ℝ}
    (hpacket : ∀ r : ℝ, Zeta23.paperFT k r = (packet H T r : ℂ)) :
    (1 / (2 * Real.pi) : ℂ) *
        ∫ r : ℝ, Zeta23.paperFT k r * (Zeta23.EF.gammaBracket r : ℂ) =
      ∫ r : ℝ, (packet H T r : ℂ) * (Zeta23.mu r : ℂ) := by
  rw [Zeta23.EF.gamma_term]
  apply integral_congr_ae
  filter_upwards with r
  rw [hpacket r]

#print axioms packet_integral
#print axioms mu_add_one_pos
#print axioms mu_tendsto_atTop
#print axioms packet_weighted_integrable_of_decay
#print axioms archimedean_lower_bound
#print axioms archimedean_divergence_of_decay
#print axioms archimedean_divergence_complex_of_decay
#print axioms gamma_term_packet

end D5.S3.Weil.ZeroInfinitude.ArchimedeanDivergence
