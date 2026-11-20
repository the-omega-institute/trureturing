/- GID: D5/S3/Analytic/Asymptotics/CanonicalThresholdWindowTransfer
   generality: G
   mirror-B: D5/B/S3/Analytic/Asymptotics/CanonicalThresholdWindowTransfer
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Signed logarithmic windows and uniform sampling give two divergent integer grids. -/

import D5.S3.Analytic.Asymptotics.RatioOneLogThreshold
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Order.Filter.AtTopBot.Field
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
The threshold and log-window argument of `canonical-mesh-pro.txt`.

In the Robin application, `K x` is `-ActualThetaTailLaplace.F x`, the raw
weighted tail of `Chebyshev.theta x - x`. The exact margin `G N` is
`robinLogMargin (strictInteger (firstLayerPrice ((N : ℝ) + 1)))`.
The two forward maps are the first integer theta crossing and the natural
ceiling. Their asymptotics and signed transfer estimates enter as hypotheses.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter
open scoped Topology

namespace CanonicalThresholdWindowTransfer

def tailScale (b x : ℝ) : ℝ := x ^ (b - 1) / Real.log x

/-- A sampling map asymptotic to the identity preserves this tail scale. -/
theorem tendsto_tailScale_ratio {n : ℝ → ℕ} (b : ℝ)
    (hRatio : Tendsto (fun x : ℝ => (n x : ℝ) / x) atTop (𝓝 1))
    (hLog : Tendsto (fun x : ℝ => Real.log (n x : ℝ) - Real.log x) atTop (𝓝 0)) :
    Tendsto (fun x : ℝ => tailScale b (n x : ℝ) / tailScale b x) atTop (𝓝 1) := by
  have hpow := (Real.continuousAt_rpow_const 1 (b - 1) (Or.inl one_ne_zero)).tendsto.comp hRatio
  simp only [Function.comp_def, Real.one_rpow] at hpow
  have hlog := (hLog.div_atTop Real.tendsto_log_atTop).add_const 1
  simp only [zero_add] at hlog
  have hdiv := hpow.div hlog (one_ne_zero : (1 : ℝ) ≠ 0)
  rw [div_self one_ne_zero] at hdiv
  apply hdiv.congr'
  filter_upwards [eventually_gt_atTop (4 : ℝ),
    hRatio.eventually (Ioi_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1))] with x hx hratio
  have hx1 : 1 < x := by linarith
  have hx0 : 0 < x := by linarith
  have hn1 : 1 < (n x : ℝ) := by
    have hr := (lt_div_iff₀ hx0).mp (Set.mem_Ioi.mp hratio)
    linarith
  have hn0 : 0 < (n x : ℝ) := by linarith
  have hlogn := Real.log_pos hn1
  have hlogx := Real.log_pos hx1
  have hpowx := Real.rpow_pos_of_pos hx0 (b - 1)
  change ((n x : ℝ) / x) ^ (b - 1) /
      ((Real.log (n x : ℝ) - Real.log x) / Real.log x + 1) =
    ((n x : ℝ) ^ (b - 1) / Real.log (n x : ℝ)) / (x ^ (b - 1) / Real.log x)
  have hlogRatio : (Real.log (n x : ℝ) - Real.log x) / Real.log x + 1 =
      Real.log (n x : ℝ) / Real.log x := by
    rw [sub_div, div_self hlogx.ne', sub_add_cancel]
  rw [hlogRatio]
  rw [Real.div_rpow hn0.le hx0.le]
  field_simp [hlogn.ne', hlogx.ne', hpowx.ne']
  <;> ring

def normalizedMargin (α : ℝ) (G : ℕ → ℝ) (N : ℕ) : ℝ :=
  (N : ℝ) ^ α * Real.log (N : ℝ) * G N

/-- Apply to `G` for the positive threshold and to `fun N => -G N` for the negative threshold. -/
def thresholdSet (α δ : ℝ) (G : ℕ → ℝ) : Set ℕ :=
  {N | 2 ≤ N ∧ (N : ℝ) ^ δ ≤ normalizedMargin α G N}

def LogWindowCoverage (A : Set ℕ) : Prop :=
  ∀ h : ℝ, 0 < h → ∀ᶠ T : ℝ in atTop,
    ∃ N ∈ A, T < Real.log (N : ℝ) ∧ Real.log (N : ℝ) ≤ T + h

/-- Sampling with log shift tending to zero transports witnesses from the closed
middle half to the target log window, with a strict lower endpoint. -/
theorem eventually_logWindow_of_sampling {A : Set ℕ} {P : ℝ → Prop}
    {n : ℝ → ℕ} {h : ℝ} (hh : 0 < h)
    (hwitness : ∀ᶠ S : ℝ in atTop, ∃ t ∈ Set.Icc S (S + h / 2), P (Real.exp t))
    (hmem : ∀ᶠ x : ℝ in atTop, P x → n x ∈ A)
    (hshift : Tendsto (fun x : ℝ => Real.log (n x : ℝ) - Real.log x) atTop (𝓝 0)) :
    ∀ᶠ T : ℝ in atTop,
      ∃ N ∈ A, T < Real.log (N : ℝ) ∧ Real.log (N : ℝ) ≤ T + h := by
  have habs : Tendsto (fun x : ℝ => |Real.log (n x : ℝ) - Real.log x|) atTop (𝓝 0) := by
    simpa only [abs_zero] using hshift.abs
  have hshiftBound : ∀ᶠ x : ℝ in atTop, |Real.log (n x : ℝ) - Real.log x| < h / 4 :=
    habs.eventually_lt_const (by linarith only [hh])
  obtain ⟨S₀, hS₀⟩ := eventually_atTop.mp hwitness
  obtain ⟨t₀, ht₀⟩ := eventually_atTop.mp
    (Real.tendsto_exp_atTop.eventually (hmem.and hshiftBound))
  filter_upwards [eventually_ge_atTop (max S₀ t₀)] with T hT
  have hstart : S₀ ≤ T + h / 4 := by
    have hle := (le_max_left S₀ t₀).trans hT
    linarith only [hle, hh]
  obtain ⟨t, ⟨htlo, hthi⟩, hP⟩ := hS₀ (T + h / 4) hstart
  have ht : t₀ ≤ t := by
    have hle := (le_max_right S₀ t₀).trans hT
    linarith only [hle, htlo, hh]
  obtain ⟨hm, hclose⟩ := ht₀ t ht
  have hclose' : |Real.log (n (Real.exp t) : ℝ) - t| < h / 4 := by
    simpa only [Real.log_exp] using hclose
  obtain ⟨hl, hu⟩ := abs_lt.mp hclose'
  exact ⟨n (Real.exp t), hm hP, by linarith only [hl, htlo],
    by linarith only [hu, hthi]⟩

private theorem eventually_mem_thresholdSet_of_transfer {α b δ c : ℝ}
    (hgap : δ < α + b - 1) (hc : 0 < c)
    {K : ℝ → ℝ} {G : ℕ → ℝ} {n : ℝ → ℕ}
    (hratio : Tendsto (fun x : ℝ => (n x : ℝ) / x) atTop (𝓝 1))
    (htransfer : ∀ᶠ x : ℝ in atTop,
      c * tailScale b x ≤ K x → (c / 4) * tailScale b (n x : ℝ) ≤ G (n x)) :
    ∀ᶠ x : ℝ in atTop, c * tailScale b x ≤ K x → n x ∈ thresholdSet α δ G := by
  have hnTop : Tendsto (fun x : ℝ => (n x : ℝ)) atTop atTop := by
    refine Filter.tendsto_atTop.mpr fun y => ?_
    filter_upwards [hratio.eventually_const_lt (by norm_num : (1 / 2 : ℝ) < 1),
      eventually_ge_atTop (max 1 (2 * y))] with x hxRatio hx
    have hxPos : 0 < x := zero_lt_one.trans_le ((le_max_left 1 (2 * y)).trans hx)
    have hxLarge : 2 * y ≤ x := (le_max_right 1 (2 * y)).trans hx
    have hhalf : (1 / 2 : ℝ) * x < (n x : ℝ) := (lt_div_iff₀ hxPos).mp hxRatio
    change y ≤ (n x : ℝ)
    linarith only [hhalf, hxLarge]
  have hpower : Tendsto (fun x : ℝ => (c / 4) * (n x : ℝ) ^ (α + b - 1 - δ))
      atTop atTop :=
    ((tendsto_rpow_atTop (sub_pos.mpr hgap)).comp hnTop).const_mul_atTop
      (div_pos hc (by norm_num))
  filter_upwards [htransfer, hnTop.eventually_ge_atTop 2, hpower.eventually_ge_atTop 1]
    with x hxTransfer hxTwo hxPower
  have hnTwo : 2 ≤ n x := by
    have hcastTwo : ((2 : ℕ) : ℝ) ≤ (n x : ℝ) := by
      simpa only [Nat.cast_ofNat] using hxTwo
    exact Nat.cast_le.mp hcastTwo
  have hnOne : 1 < (n x : ℝ) := (by norm_num : (1 : ℝ) < 2).trans_le hxTwo
  have hnPos : 0 < (n x : ℝ) := zero_lt_one.trans hnOne
  have hlog : 0 < Real.log (n x : ℝ) := Real.log_pos hnOne
  intro hxWitness
  refine ⟨hnTwo, ?_⟩
  calc
    (n x : ℝ) ^ δ ≤ (c / 4) * (n x : ℝ) ^ (α + b - 1) := by
      change 1 ≤ (c / 4) * (n x : ℝ) ^ (α + b - 1 - δ) at hxPower
      rw [Real.rpow_sub hnPos, ← mul_div_assoc] at hxPower
      have hle := (le_div_iff₀ (Real.rpow_pos_of_pos hnPos δ)).mp hxPower
      simpa only [one_mul] using hle
    _ = ((n x : ℝ) ^ α * Real.log (n x : ℝ)) * ((c / 4) * tailScale b (n x : ℝ)) := by
      rw [show α + b - 1 = α + (b - 1) by ring, Real.rpow_add hnPos, tailScale]
      calc
        _ = (c / 4) * ((n x : ℝ) ^ α *
            (((n x : ℝ) ^ (b - 1) / Real.log (n x : ℝ)) * Real.log (n x : ℝ))) := by
          rw [div_mul_cancel₀ _ hlog.ne']
        _ = _ := by ring
    _ ≤ normalizedMargin α G (n x) :=
      mul_le_mul_of_nonneg_left (hxTransfer hxWitness)
        (mul_nonneg (Real.rpow_nonneg hnPos.le α) hlog.le)

private theorem logWindowCoverage_of_signed_transfer {α b δ : ℝ}
    (hgap : δ < α + b - 1) {K : ℝ → ℝ} {G : ℕ → ℝ} {n : ℝ → ℕ}
    (hwindow : ∀ h : ℝ, 0 < h → ∃ c : ℝ, 0 < c ∧ ∀ᶠ T : ℝ in atTop,
      ∃ t ∈ Set.Icc T (T + h), c * tailScale b (Real.exp t) ≤ K (Real.exp t))
    (hratio : Tendsto (fun x : ℝ => (n x : ℝ) / x) atTop (𝓝 1))
    (hshift : Tendsto (fun x : ℝ => Real.log (n x : ℝ) - Real.log x) atTop (𝓝 0))
    (htransfer : ∀ c : ℝ, 0 < c → ∀ᶠ x : ℝ in atTop,
      c * tailScale b x ≤ K x → (c / 4) * tailScale b (n x : ℝ) ≤ G (n x)) :
    LogWindowCoverage (thresholdSet α δ G) := by
  intro h hh
  obtain ⟨c, hc, hwitness⟩ := hwindow (h / 2) (half_pos hh)
  exact eventually_logWindow_of_sampling (P := fun x => c * tailScale b x ≤ K x) hh hwitness
    (eventually_mem_thresholdSet_of_transfer hgap hc hratio (htransfer c hc)) hshift

private theorem exists_threshold_grid {α δ : ℝ} {G : ℕ → ℝ} (hδ : 0 < δ)
    (hwindow : LogWindowCoverage (thresholdSet α δ G)) :
    ∃ N : ℕ → ℕ, StrictMono N ∧ (∀ k, N k ∈ thresholdSet α δ G) ∧
      Tendsto (fun k => (N (k + 1) : ℝ) / (N k : ℝ)) atTop (𝓝 1) ∧
      Tendsto (fun k => normalizedMargin α G (N k)) atTop atTop := by
  have hpositiveWindow (h : ℝ) (hh : 0 < h) : ∀ᶠ T : ℝ in atTop,
      ∃ n : ℕ, n ∈ thresholdSet α δ G ∧ 0 < n ∧
        T < Real.log (n : ℝ) ∧ Real.log (n : ℝ) ≤ T + h := by
    refine (hwindow h hh).mono ?_
    rintro T ⟨n, hn, hlo, hhi⟩
    exact ⟨n, hn, (by decide : 0 < (2 : ℕ)).trans_le hn.1, hlo, hhi⟩
  obtain ⟨N, hmono, hmem, _, hratio⟩ :=
    RatioOneLogThreshold.exists_strictMono_ratio_tendsto_one_of_log_windows
      (fun n => n ∈ thresholdSet α δ G) hpositiveWindow
  have hcast : Tendsto (fun k => (N k : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_iff.mpr hmono.tendsto_atTop
  refine ⟨N, hmono, hmem, hratio, ?_⟩
  exact tendsto_atTop_mono (fun k => (hmem k).2) ((tendsto_rpow_atTop hδ).comp hcast)

/-- Both fixed power thresholds meet every late logarithmic window. The two
increasing enumerations supplied by `RatioOneLogThreshold` use `Nat.nth` and
have adjacent ratios tending to one. The normalized margins tend to the
corresponding signed infinities. -/
theorem threshold_grids_of_two_signed_samplings {α b δ : ℝ}
    (hδ : 0 < δ) (hgap : δ < α + b - 1)
    (K : ℝ → ℝ) (G : ℕ → ℝ) (n_pos n_neg : ℝ → ℕ)
    (hwindow : ∀ h : ℝ, 0 < h → ∃ c : ℝ, 0 < c ∧ ∀ᶠ T : ℝ in atTop,
      (∃ t ∈ Set.Icc T (T + h), c * tailScale b (Real.exp t) ≤ K (Real.exp t)) ∧
      (∃ t ∈ Set.Icc T (T + h), c * tailScale b (Real.exp t) ≤ -K (Real.exp t)))
    (hposRatio : Tendsto (fun x : ℝ => (n_pos x : ℝ) / x) atTop (𝓝 1))
    (hnegRatio : Tendsto (fun x : ℝ => (n_neg x : ℝ) / x) atTop (𝓝 1))
    (hposShift : Tendsto (fun x : ℝ => Real.log (n_pos x : ℝ) - Real.log x) atTop (𝓝 0))
    (hnegShift : Tendsto (fun x : ℝ => Real.log (n_neg x : ℝ) - Real.log x) atTop (𝓝 0))
    (hposTransfer : ∀ c : ℝ, 0 < c → ∀ᶠ x : ℝ in atTop,
      c * tailScale b x ≤ K x → (c / 4) * tailScale b (n_pos x : ℝ) ≤ G (n_pos x))
    (hnegTransfer : ∀ c : ℝ, 0 < c → ∀ᶠ x : ℝ in atTop,
      c * tailScale b x ≤ -K x → (c / 4) * tailScale b (n_neg x : ℝ) ≤ -G (n_neg x)) :
    LogWindowCoverage (thresholdSet α δ G) ∧
    LogWindowCoverage (thresholdSet α δ (fun N => -G N)) ∧
    ∃ N_pos N_neg : ℕ → ℕ, StrictMono N_pos ∧ StrictMono N_neg ∧
      (∀ k, N_pos k ∈ thresholdSet α δ G) ∧
      (∀ k, N_neg k ∈ thresholdSet α δ (fun N => -G N)) ∧
      Tendsto (fun k => (N_pos (k + 1) : ℝ) / (N_pos k : ℝ)) atTop (𝓝 1) ∧
      Tendsto (fun k => (N_neg (k + 1) : ℝ) / (N_neg k : ℝ)) atTop (𝓝 1) ∧
      Tendsto (fun k => normalizedMargin α G (N_pos k)) atTop atTop ∧
      Tendsto (fun k => normalizedMargin α G (N_neg k)) atTop atBot := by
  have hposCoverage : LogWindowCoverage (thresholdSet α δ G) := by
    refine logWindowCoverage_of_signed_transfer hgap (K := K) (G := G) (n := n_pos) ?_
      hposRatio hposShift hposTransfer
    intro h hh
    obtain ⟨c, hc, hboth⟩ := hwindow h hh
    exact ⟨c, hc, hboth.mono (fun _ hw => hw.1)⟩
  have hnegCoverage : LogWindowCoverage (thresholdSet α δ (fun N => -G N)) := by
    refine logWindowCoverage_of_signed_transfer hgap (K := fun x => -K x)
      (G := fun N => -G N) (n := n_neg) ?_
      hnegRatio hnegShift hnegTransfer
    intro h hh
    obtain ⟨c, hc, hboth⟩ := hwindow h hh
    exact ⟨c, hc, hboth.mono (fun _ hw => hw.2)⟩
  obtain ⟨N_pos, hposMono, hposMem, hposMesh, hposLimit⟩ :=
    exists_threshold_grid hδ hposCoverage
  obtain ⟨N_neg, hnegMono, hnegMem, hnegMesh, hnegLimit⟩ :=
    exists_threshold_grid hδ hnegCoverage
  refine ⟨hposCoverage, hnegCoverage, N_pos, N_neg, hposMono, hnegMono,
    hposMem, hnegMem, hposMesh, hnegMesh, hposLimit, ?_⟩
  simpa only [Function.comp_def, normalizedMargin, mul_neg, neg_neg] using
    tendsto_neg_atTop_atBot.comp hnegLimit

end CanonicalThresholdWindowTransfer
