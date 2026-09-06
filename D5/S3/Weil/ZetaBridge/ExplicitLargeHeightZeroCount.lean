/- GID: D5/S3/Weil/ZetaBridge/ExplicitLargeHeightZeroCount
   generality: I
   mirror-B: D5/B/S3/Weil/ZetaBridge/ExplicitLargeHeightZeroCount
   mirror-E: none(waiver:explicit-analytic-zero-count)
   anchors: []
   digest: Expose a numerical large-height zeta window count by retaining the explicit growth constants in the existing Jensen argument. -/

import D5.S3.Weil.ZetaRvm.LocalCount

/-!
# Explicit large-height local count

The existing `half_count_large` hides its constant behind an existential.
This quantitative strengthening retains the already proved growth coefficient
20/3 and exponent 1, and the same disks of radii 0.84 and 0.95.
It yields the conservative numerical bound 128 log(|t|+3) for |t| >= 4.
No small-height counting constant, RH, or numerical root oracle is used.

The disk argument adapts Zeta23/RvM/LocalCount.lean, originally from
anthropics/zeta-23-lean commit 3635e74826a4c1fcece7d1cd2b6fa75e43a00510,
Copyright (c) 2026 Anthropic, PBC, Apache-2.0. Geometry, analytic order
transport, zeta growth and Jensen's theorem are reused from that owner.
Classical reference: Titchmarsh, The Theory of the Riemann Zeta-function,
second edition, Section 9.2. The constant 128 below is this proof's coarse
rational enclosure, not a quoted optimal constant from that reference.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.Weil.ZetaBridge.ExplicitLargeHeightZeroCount

open Complex Set Filter Topology Metric
open Zeta23 Zeta23.RvM

/-- Retain the actual growth constants in the existing half-window disk proof. -/
theorem half_count_large_explicit (t : ℝ) (ht : 4 ≤ |t|) :
    NhalfR t ≤ 64 * Real.log (|t| + 3) := by
  let r : ℝ := 0.84
  let R : ℝ := 0.95
  have hlogRr : 0 < Real.log (R / r) := Real.log_pos (by norm_num [r, R])
  let c₀ : ℂ := 2 + (t + 1/2 : ℝ) * I
  let κ : ℂ := ((19/10 : ℝ) : ℂ)
  have hκ0 : κ ≠ 0 := by norm_num [κ]
  have hnormκ : ‖κ‖ = 1.9 := by norm_num [κ]
  have hζc₀ : (1/3 : ℝ) ≤ ‖riemannZeta c₀‖ := by
    simpa [c₀] using zeta_lower_bound_two (t + 1/2)
  have hζc₀ne : riemannZeta c₀ ≠ 0 := by
    intro h
    rw [h, norm_zero] at hζc₀
    norm_num at hζc₀
  let u : ℂ := (riemannZeta c₀)⁻¹
  have hu0 : u ≠ 0 := inv_ne_zero hζc₀ne
  have hnu : ‖u‖ ≤ 3 := by
    rw [show ‖u‖ = ‖riemannZeta c₀‖⁻¹ by simp [u]]
    rw [inv_le_comm₀ (norm_pos_iff.mpr hζc₀ne) (by norm_num)]
    linarith
  let g : ℂ → ℂ := gfun c₀ κ u
  have hc₀1 : |t + 1/2| ≤ ‖c₀ - 1‖ := by
    have him : (c₀ - 1).im = t + 1/2 := by simp [c₀]
    rw [← him]
    exact Complex.abs_im_le_norm _
  have ht' : 3.5 ≤ |t + 1/2| := by
    rcases le_abs'.mp ht with h | h
    · rw [abs_of_neg (by linarith)]
      linarith
    · rw [abs_of_pos (by linarith)]
      linarith
  have hdist (z : ℂ) : |t + 1/2| - 1.9 * ‖z‖ ≤ ‖c₀ + κ * z - 1‖ := by
    have h := norm_sub_norm_le (c₀ - 1) (-(κ * z))
    rw [norm_neg, norm_mul, hnormκ] at h
    have heq : c₀ - 1 - -(κ * z) = c₀ + κ * z - 1 := by ring
    rw [heq] at h
    linarith
  have hne1 (z : ℂ) (hz : ‖z‖ ≤ 1) : c₀ + κ * z ≠ 1 := by
    intro h
    have hd := hdist z
    rw [h, sub_self, norm_zero] at hd
    nlinarith
  have hfAnalytic : AnalyticOnNhd ℂ g (Metric.closedBall (0 : ℂ) 1) := by
    intro z hz
    rw [Metric.mem_closedBall, dist_zero_right] at hz
    exact gfun_analyticAt (hne1 z hz)
  have hg0 : g 0 = 1 := by simp [g, gfun, u, hζc₀ne]
  have hfin : (SetOfZeros 1 g).Finite := by
    have hK := riemannZeta_zeros_finite_of_isCompact (isCompact_closedBall c₀ (1.9 : ℝ))
    refine (hK.image fun ρ => (ρ - c₀) / κ).subset ?_
    rintro z ⟨hz, hgz⟩
    refine ⟨c₀ + κ * z, ⟨?_, hne1 z hz, ?_⟩, ?_⟩
    · rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_mul, hnormκ]
      nlinarith [norm_nonneg z]
    · simpa [g, gfun, hu0] using hgz
    · change (c₀ + κ * z - c₀) / κ = z
      rw [add_sub_cancel_left, mul_div_cancel_left₀ _ hκ0]
  let B : ℝ := 20 * (|t| + 6)
  have hfz (z : ℂ) (hz : ‖z‖ ≤ R) : ‖g z‖ ≤ B := by
    have hz1 : ‖z‖ ≤ 1 := hz.trans (by norm_num [R])
    let s : ℂ := c₀ + κ * z
    have hsre : (0.15 : ℝ) ≤ s.re := by
      have hre : s.re = 2 + 1.9 * z.re := by norm_num [s, c₀, κ]
      rw [hre]
      obtain ⟨h1, _⟩ := abs_le.mp ((abs_re_le_norm z).trans hz)
      dsimp [R] at h1
      nlinarith
    have hs1 : 1 ≤ ‖s - 1‖ := by
      have hd := hdist z
      dsimp [R] at hz
      dsimp [s]
      nlinarith
    have hsim : |s.im| + 3 ≤ |t| + 6 := by
      have him : s.im = t + 1/2 + 1.9 * z.im := by norm_num [s, c₀, κ]
      rw [him]
      have hzi := (abs_im_le_norm z).trans hz
      dsimp [R] at hzi
      have h1 := abs_add_le (t + 1/2) (1.9 * z.im)
      have h2 : |1.9 * z.im| ≤ 1.9 * 0.95 := by
        rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1.9)]
        nlinarith
      have h3 : |t + 1/2| ≤ |t| + 1/2 := by simpa using abs_add_le t (1/2)
      linarith
    have hζ : ‖riemannZeta s‖ ≤ (20 / 3 : ℝ) * (|t| + 6) := by
      have h := zeta_growth_right_at s hsre hs1
      rw [Real.rpow_one] at h
      exact h.trans (mul_le_mul_of_nonneg_left hsim (by norm_num))
    calc
      ‖g z‖ = ‖riemannZeta s‖ * ‖u‖ := by simp [g, gfun, s]
      _ ≤ ((20 / 3 : ℝ) * (|t| + 6)) * 3 :=
        mul_le_mul hζ hnu (norm_nonneg _) (by positivity)
      _ = B := by dsimp [B]; ring
  have hZ := ZerosBound (B := B) (r := r) (R := R)
    (by norm_num [r]) (by norm_num [r]) (by norm_num [r, R]) (by norm_num [R])
    hfAnalytic hg0 hfin hfz
  let W : Set ℂ := zetaZeroConfig.window t (t + 1) ∩ {ρ | 1/2 ≤ ρ.re}
  have hWfin : W.Finite := (zetaZeroConfig.window_finite t (t + 1)).subset inter_subset_left
  let φ : ℂ → ℂ := fun ρ => (ρ - c₀) / κ
  have hφinj : Function.Injective φ := by
    intro a b h
    have heq := congrArg (fun w => c₀ + κ * w) h
    simpa [φ, mul_div_cancel₀ _ hκ0] using heq
  have hφinv (ρ : ℂ) : c₀ + κ * φ ρ = ρ := by dsimp [φ]; field_simp; ring
  have hmemS : ∀ ρ ∈ W,
      φ ρ ∈ (finiteSetOfZeros_mono (by norm_num [r] : r < 1) hfin).toFinset := by
    rintro ρ ⟨⟨hρZ, hρt, hρt1⟩, hρre⟩
    simp only [Set.Finite.mem_toFinset]
    have hρ : Zeta23.IsNontrivialZero ρ := hρZ
    refine ⟨?_, ?_⟩
    · simp only [φ, norm_div, hnormκ]
      rw [div_le_iff₀ (by norm_num)]
      have hre : (ρ - c₀).re = ρ.re - 2 := by simp [c₀]
      have him : (ρ - c₀).im = ρ.im - (t + 1/2) := by simp [c₀]
      have hsq : ‖ρ - c₀‖ ^ 2 ≤ (r * 1.9) ^ 2 := by
        rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
        dsimp [r]
        have hrhoUpper := hρ.2.2
        have hReProduct := mul_nonneg
          (show 0 ≤ ρ.re - (1/2 : ℝ) by linarith)
          (show 0 ≤ (7/2 : ℝ) - ρ.re by linarith)
        have hImProduct := mul_nonneg
          (show 0 ≤ ρ.im - t by linarith)
          (show 0 ≤ t + 1 - ρ.im by linarith)
        nlinarith
      exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by norm_num [r]) two_ne_zero).mp hsq
    · change g (φ ρ) = 0
      simp only [g, gfun, hφinv]
      rw [hρ.1, zero_mul]
  have hmult : ∀ ρ ∈ W, (zeroMult ρ : ℝ) = (analyticOrderNatAt g (φ ρ) : ℝ) := by
    rintro ρ ⟨⟨hρZ, _, _⟩, _⟩
    have hρ : Zeta23.IsNontrivialZero ρ := hρZ
    rw [analyticOrderNatAt_gfun hκ0 hu0 (by rw [hφinv]; exact hρ.not_trivial.2), hφinv]
  have hsum : NhalfR t ≤ ((∑ ρ' ∈
      (finiteSetOfZeros_mono (by norm_num [r] : r < 1) hfin).toFinset,
      analyticOrderNatAt g ρ' : ℕ) : ℝ) := by
    unfold NhalfR
    change (∑ᶠ ρ ∈ W, (zeroMult ρ : ℝ)) ≤ _
    rw [finsum_mem_eq_finite_toFinset_sum _ hWfin,
      Finset.sum_congr rfl (fun ρ hρ => hmult ρ (hWfin.mem_toFinset.mp hρ)),
      ← Finset.sum_image (f := fun w => (analyticOrderNatAt g w : ℝ))
        (fun a _ b _ h => hφinj h)]
    push_cast
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro w hw
      obtain ⟨ρ, hρ, rfl⟩ := Finset.mem_image.mp hw
      exact hmemS ρ (hWfin.mem_toFinset.mp hρ)
    · intros
      positivity
  have hL : 1 ≤ Real.log (|t| + 3) := by
    rw [← Real.log_exp 1]
    apply Real.log_le_log (Real.exp_pos 1)
    have he := Real.exp_one_lt_three
    linarith [abs_nonneg t]
  have hlog6 : Real.log (|t| + 6) ≤ 2 * Real.log (|t| + 3) := by
    rw [← Real.log_rpow (by positivity), Real.rpow_two]
    apply Real.log_le_log (by positivity)
    nlinarith [abs_nonneg t]
  have hlog20 : Real.log (20 : ℝ) ≤ 5 := by
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 20) (by norm_num : (20 : ℝ) ≤ 2 ^ 5)
    rw [Real.log_pow] at h
    have h2 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    linarith
  have hlogB : Real.log B ≤ 7 * Real.log (|t| + 3) := by
    dsimp [B]
    rw [Real.log_mul (by norm_num) (by positivity)]
    nlinarith
  have hden : (11 / 95 : ℝ) ≤ Real.log (R / r) := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 84 / 95)
    have heq : (84 / 95 : ℝ) = (95 / 84)⁻¹ := by norm_num
    rw [heq, Real.log_inv] at h
    norm_num [R, r] at ⊢
    linarith
  calc
    NhalfR t ≤ _ := hsum
    _ ≤ 1 / Real.log (R / r) * Real.log B := by exact_mod_cast hZ
    _ ≤ 64 * Real.log (|t| + 3) := by
      rw [show 1 / Real.log (R / r) * Real.log B =
        Real.log B / Real.log (R / r) by ring, div_le_iff₀ hlogRr]
      have hproduct := mul_le_mul_of_nonneg_left hden
        (show 0 ≤ 64 * Real.log (|t| + 3) by positivity)
      nlinarith

/-- Numerical two-sided large-height count for the actual zeta configuration.
The coefficient 128 is proved; no claim of sharpness is made. -/
theorem zetaZeroConfig_large_count_explicit (t : ℝ) (ht : 4 ≤ |t|) :
    (zetaZeroConfig.N t (t + 1) : ℝ) ≤ 128 * Real.log (|t| + 3) := by
  have hhalf : (zetaZeroConfig.N t (t + 1) : ℝ) ≤ 2 * NhalfR t := by
    simpa [NhalfR] using zetaZeroConfig.N_le_two_mul_half t (t + 1)
  have h := half_count_large_explicit t ht
  linarith

#print axioms half_count_large_explicit
#print axioms zetaZeroConfig_large_count_explicit

end D5.S3.Weil.ZetaBridge.ExplicitLargeHeightZeroCount
