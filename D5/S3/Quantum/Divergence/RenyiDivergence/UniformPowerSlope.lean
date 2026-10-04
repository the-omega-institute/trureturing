/- GID: D5/S3/Quantum/Divergence/RenyiDivergence/UniformPowerSlope
   generality: G
   mirror-B: D5/B/S3/Quantum/Divergence/RenyiDivergence/UniformPowerSlope
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Uniform power slopes converge to x log x on bounded spectra including zero. -/

/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/



import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic

/-!
Adapted from QuantumInfo/Entropy/Relative.lean, rpow_slope_tendsto_uniformly,
at Physlib revision b9043cc548ef6d63a28454cf3a57fb12a0c2e142.
Source: https://github.com/leanprover-community/physlib/blob/b9043cc548ef6d63a28454cf3a57fb12a0c2e142/QuantumInfo/Entropy/Relative.lean
The supplier Apache license is retained at docs/reports/inoutbalance/physlib-LICENSE.txt.
This estimate controls singular eigenvalues in the alpha-one relative-entropy limit.
It does not assert data processing or close the thermal recovery theorem.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Quantum.Divergence.RenyiDivergence.UniformPowerSlope

open scoped Topology
open Filter

set_option maxHeartbeats 800000 in
/-- The estimate holds for every real upper bound K and both signs of h.
Zero belongs to the spectral interval and no positive lower bound is imposed. -/
theorem rpow_slope_tendsto_uniformly (K : ℝ) :
    ∀ ε > 0, ∃ δ > 0, ∀ h : ℝ, 0 < |h| → |h| < δ →
    ∀ x ∈ Set.Icc 0 K, |(x ^ (1 + h) - x) / h - x * Real.log x| < ε := by
  intro ε ε_pos
  obtain ⟨δ₁, δ₁_pos, hδ₁⟩ : ∃ δ₁ > 0, ∀ x ∈ Set.Icc 0 K, 0 < x → x < δ₁ → |x * Real.log x| < ε /
    4 ∧ ∀ h, 0 < |h| → |h| < 1 / 2 → |(x ^ (1 + h) - x) / h| < ε / 4 := by
    obtain ⟨δ₁, δ₁_pos, hδ₁⟩ : ∃ δ₁ > 0, ∀ x ∈ Set.Icc 0 K, 0 < x → x < δ₁ → |x * Real.log x| < ε
      / 4 := by
      have h_cont : Filter.Tendsto (fun x => x * Real.log x) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)
        := by
        exact tendsto_nhdsWithin_of_tendsto_nhds ( by simpa using Real.continuous_mul_log.tendsto 0 );
      have := Metric.tendsto_nhdsWithin_nhds.mp h_cont ( ε / 4 ) ( by linarith );
      exact ⟨ this.choose, this.choose_spec.1, fun x hx₁ hx₂ hx₃ => by simpa [ abs_mul ] using this.choose_spec.2 hx₂ ( by simpa [ abs_of_pos hx₂ ] using hx₃ ) ⟩;
    have h_bound : ∃ δ₁ > 0, ∀ x ∈ Set.Icc 0 K, 0 < x → x < δ₁ → ∀ h, 0 < |h| → |h| < 1 / 2 → |x ^
      (1 + h) - x| ≤ |h| * x * (|Real.log x| + 1) * Real.exp (|h| * (|Real.log x| + 1)) := by
      have h_bound : ∀ x ∈ Set.Icc 0 K, 0 < x → ∀ h : ℝ, 0 < |h| → |h| < 1 / 2 → |x ^ (1 + h) - x|
        ≤ |h| * x * (|Real.log x| + 1) * Real.exp (|h| * (|Real.log x| + 1)) := by
        intros x hx hx_pos h hh_pos hh_lt_half
        have h_exp_bound : |Real.exp (h * Real.log x) - 1| ≤ |h| * |Real.log x| * Real.exp (|h| *
          |Real.log x|) := by
          have h_exp_bound : ∀ y : ℝ, |Real.exp y - 1| ≤ |y| * Real.exp (|y|) := by
            intro y; rw [ abs_le ] ; constructor <;> cases abs_cases y <;> simp [ * ];
            · nlinarith [ Real.add_one_le_exp y ];
            · nlinarith [ Real.exp_pos y, Real.exp_neg y, mul_inv_cancel₀ ( ne_of_gt ( Real.exp_pos y ) ), Real.add_one_le_exp y, Real.add_one_le_exp ( -y ) ];
            · nlinarith [ Real.exp_pos y, Real.exp_neg y, mul_inv_cancel₀ ( ne_of_gt ( Real.exp_pos y ) ), Real.add_one_le_exp y, Real.add_one_le_exp ( -y ) ];
            · nlinarith [ Real.exp_pos y, Real.exp_neg y, mul_inv_cancel₀ ( ne_of_gt ( Real.exp_pos y ) ), Real.add_one_le_exp y, Real.add_one_le_exp ( -y ) ];
          simpa only [ abs_mul ] using h_exp_bound ( h * Real.log x );
        rw [ Real.rpow_add hx_pos, Real.rpow_one ];
        rw [ Real.rpow_def_of_pos hx_pos ];
        rw [ show x * Real.exp ( Real.log x * h ) - x = x * ( Real.exp ( h * Real.log x ) - 1 ) by ring_nf ]
        rw [ abs_mul, abs_of_nonneg hx_pos.le ]
        refine' le_trans ( mul_le_mul_of_nonneg_left h_exp_bound hx_pos.le ) _
        ring_nf
        exact le_add_of_le_of_nonneg ( mul_le_mul_of_nonneg_left ( Real.exp_le_exp.mpr ( by nlinarith [ abs_nonneg h, abs_nonneg ( Real.log x ) ] ) ) ( by positivity ) ) ( by positivity );
      exact ⟨ δ₁, δ₁_pos, fun x hx hx' hx'' h hh hh' => h_bound x hx hx' h hh hh' ⟩;
    obtain ⟨δ₂, δ₂_pos, hδ₂⟩ : ∃ δ₂ > 0, ∀ x ∈ Set.Icc 0 K, 0 < x → x < δ₂ → x * (|Real.log x| +
      1) * Real.exp (1 / 2 * (|Real.log x| + 1)) < ε / 4 := by
      have h_bound : Filter.Tendsto (fun x => x * (|Real.log x| + 1) * Real.exp (1 / 2 *
        (|Real.log x| + 1))) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
        -- Let $y = -\log x$, so we can rewrite the limit as $y \to \infty$.
        suffices h_log : Filter.Tendsto (fun y => Real.exp (-y) * (y + 1) * Real.exp ((y + 1) / 2)) Filter.atTop (nhds 0) by
          have h_subst : Filter.Tendsto (fun x => Real.exp (-(-Real.log x)) * ((-Real.log x) + 1)
            * Real.exp ((-Real.log x + 1) / 2)) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
            exact h_log.comp ( Filter.tendsto_neg_atBot_atTop.comp ( Real.tendsto_log_nhdsNE_zero.mono_left <| nhdsWithin_mono _ <| by norm_num ) );
          refine' h_subst.congr' _;
          filter_upwards [ Ioo_mem_nhdsGT_of_mem ⟨ le_rfl, zero_lt_one ⟩ ] with x hx
          rw [ abs_of_nonpos ( Real.log_nonpos hx.1.le hx.2.le ) ]
          rw [ neg_neg, Real.exp_log hx.1 ]
          ring_nf
        -- We can factor out $e^{-y/2}$ and use the fact that $e^{-y/2} \to 0$ as $y \to \infty$.
        suffices h_factor : Filter.Tendsto (fun y => Real.exp (-y / 2) * (y + 1)) Filter.atTop (nhds 0) by
          convert h_factor.const_mul ( Real.exp ( 1 / 2 ) ) using 2 <;> ring_nf
          norm_num [ mul_assoc, ← Real.exp_add ] ; ring_nf
        -- Let $z = \frac{y}{2}$, so we can rewrite the limit as $z \to \infty$.
        suffices h_z : Filter.Tendsto (fun z => Real.exp (-z) * (2 * z + 1)) Filter.atTop (nhds 0) by
          convert h_z.comp ( Filter.tendsto_id.atTop_mul_const ( by norm_num : 0 < ( 2⁻¹ : ℝ ) ) ) using 2 ; norm_num ; ring_nf
        have := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1;
        convert this.const_mul 2 |> Filter.Tendsto.add <| Real.tendsto_exp_atBot.comp <| Filter.tendsto_neg_atTop_atBot using 2 <;> norm_num
        ring;
      have := Metric.tendsto_nhdsWithin_nhds.mp h_bound ( ε / 4 ) ( by linarith );
      obtain ⟨ δ₂, δ₂_pos, H ⟩ := this; exact ⟨ δ₂, δ₂_pos, fun x hx₁ hx₂ hx₃ => by linarith [ abs_lt.mp ( H hx₂ ( by simpa [ abs_of_pos hx₂ ] using hx₃ ) ) ] ⟩ ;
    obtain ⟨δ₃, δ₃_pos, hδ₃⟩ : ∃ δ₃ > 0, ∀ x ∈ Set.Icc 0 K, 0 < x → x < δ₃ → ∀ h, 0 < |h| → |h| <
      1 / 2 → |(x ^ (1 + h) - x) / h| ≤ x * (|Real.log x| + 1) * Real.exp (|h| * (|Real.log x| +
      1)) := by
      obtain ⟨ δ₃, δ₃_pos, hδ₃ ⟩ := h_bound;
      exact ⟨ δ₃, δ₃_pos, fun x hx hx' hx'' h hh hh' => by rw [ abs_div, div_le_iff₀ ( by positivity ) ] ; convert! hδ₃ x hx hx' hx'' h hh hh' using 1 ; ring ⟩;
    refine' ⟨ Min.min δ₁ ( Min.min δ₂ δ₃ ), lt_min δ₁_pos ( lt_min δ₂_pos δ₃_pos ), fun x hx hx' hx'' => ⟨ hδ₁ x hx hx' ( lt_of_lt_of_le hx'' ( min_le_left _ _ ) ), fun h hh₁ hh₂ => lt_of_le_of_lt ( hδ₃ x hx hx' ( lt_of_lt_of_le hx'' ( min_le_right _ _ |> le_trans <| min_le_right _ _ ) ) h hh₁ hh₂ ) _ ⟩ ⟩;
    exact lt_of_le_of_lt ( mul_le_mul_of_nonneg_left ( Real.exp_le_exp.mpr <| mul_le_mul_of_nonneg_right hh₂.le <| by positivity ) <| by positivity ) <| hδ₂ x hx hx' <| lt_of_lt_of_le hx'' <| min_le_right _ _ |> le_trans <| min_le_left _ _;
  obtain ⟨δ₂, δ₂_pos, hδ₂⟩ : ∃ δ₂ > 0, ∀ x ∈ Set.Icc δ₁ K, ∀ h, 0 < |h| → |h| < δ₂ → |(x ^ (1 + h)
    - x) / h - x * Real.log x| < ε / 4 := by
    have h_mean_value : ∀ x ∈ Set.Icc δ₁ K, ∀ h, 0 < |h| → |h| < 1 / 2 → |(x ^ (1 + h) - x) / h -
      x * Real.log x| ≤ |h| * x * (Real.log x) ^ 2 * Real.exp (|h| * |Real.log x|) := by
      intros x hx h h_pos h_lt
      have h_mean_value : |(x ^ h - 1) / h - Real.log x| ≤ |h| * (Real.log x) ^ 2 * Real.exp (|h|
        * |Real.log x|) := by
        -- Applying the inequality |e^y - 1 - y| ≤ |y|^2 e^|y| with y = h * Real.log x.
        have h_exp_ineq : ∀ y : ℝ, |Real.exp y - 1 - y| ≤ |y|^2 * Real.exp |y| := by
          intro y; rw [ abs_le ] ; constructor <;> cases abs_cases y <;> simp [ * ];
          · nlinarith [ Real.add_one_le_exp y, Real.exp_pos y ];
          · nlinarith [ Real.add_one_le_exp y, Real.add_one_le_exp ( -y ), Real.exp_pos y, Real.exp_pos ( -y ) ];
          · -- Using the Taylor series expansion of $e^y$, we have $e^y \leq 1 + y + y^2 e^y$ for $y \geq 0$.
            have h_taylor : ∀ y : ℝ, 0 ≤ y → Real.exp y ≤ 1 + y + y^2 * Real.exp y := by
              intro y hy; nlinarith [ Real.exp_pos y, Real.exp_neg y, mul_inv_cancel₀ ( ne_of_gt ( Real.exp_pos y ) ), Real.add_one_le_exp y, Real.add_one_le_exp ( -y ), mul_nonneg hy ( Real.exp_nonneg y ), mul_nonneg hy ( Real.exp_nonneg ( -y ) ) ] ;
            linarith [ h_taylor y ( by linarith ) ];
          · nlinarith [ Real.exp_pos y, Real.exp_neg y, mul_inv_cancel₀ ( ne_of_gt ( Real.exp_pos y ) ), Real.add_one_le_exp y, Real.add_one_le_exp ( -y ) ];
        convert! mul_le_mul_of_nonneg_left ( h_exp_ineq ( h * Real.log x ) ) ( inv_nonneg.mpr h_pos.le ) using 1 <;> norm_num [ Real.rpow_def_of_pos ( show 0 < x from lt_of_lt_of_le δ₁_pos hx.1 ), mul_comm ] ; ring_nf
        · rw [ ← abs_inv, ← abs_mul ] ; ring_nf;
          by_cases hh : h = 0 <;> aesop;
        · simp [ sq, mul_assoc, mul_comm, mul_left_comm, h_pos.ne' ];
      convert! mul_le_mul_of_nonneg_left h_mean_value ( show 0 ≤ x by linarith [ hx.1 ] ) using 1 <;> ring_nf

      rw [ show x ^ (1 + h) * h⁻¹ - x * h⁻¹ - x * Real.log x = x * ( -h⁻¹ + ( h⁻¹ * x ^ h - Real.log x ) ) by rw [ Real.rpow_add ( by linarith [ hx.1 ] ), Real.rpow_one ] ; ring ]
      rw [ abs_mul, abs_of_nonneg ( by linarith [ hx.1 ] : 0 ≤ x ) ]
      ring_nf

    -- Choose δ₂ such that |h| * x * (Real.log x) ^ 2 * Real.exp (|h| * |Real.log x|) < ε / 4 for all x ∈ [δ₁, K] and |h| < δ₂.
    obtain ⟨δ₂, δ₂_pos, hδ₂⟩ : ∃ δ₂ > 0, ∀ x ∈ Set.Icc δ₁ K, ∀ h, 0 < |h| → |h| < δ₂ → |h| * x *
      (Real.log x) ^ 2 * Real.exp (|h| * |Real.log x|) < ε / 4 := by
      -- Since $x * (\log x)^2 * \exp(|h| * |\log x|)$ is continuous on the compact interval $[\delta₁, K]$, it is bounded.
      obtain ⟨M, hM⟩ : ∃ M > 0, ∀ x ∈ Set.Icc δ₁ K, ∀ h, 0 < |h| → |h| < 1 / 2 → x * (Real.log x)
        ^ 2 * Real.exp (|h| * |Real.log x|) ≤ M := by
        have h_cont : ContinuousOn (fun x => x * (Real.log x) ^ 2 * Real.exp (1 / 2 * |Real.log
          x|)) (Set.Icc δ₁ K) := by
          exact ContinuousOn.mul ( ContinuousOn.mul continuousOn_id ( ContinuousOn.pow ( Real.continuousOn_log.mono ( by exact fun x hx => ne_of_gt <| lt_of_lt_of_le δ₁_pos hx.1 ) ) _ ) ) ( ContinuousOn.rexp <| ContinuousOn.mul continuousOn_const <| ContinuousOn.abs <| Real.continuousOn_log.mono ( by exact fun x hx => ne_of_gt <| lt_of_lt_of_le δ₁_pos hx.1 ) );
        obtain ⟨ M, hM ⟩ := IsCompact.exists_bound_of_continuousOn ( CompactIccSpace.isCompact_Icc ) h_cont;
        norm_num +zetaDelta at *;
        exact ⟨ Max.max M 1, by positivity, fun x hx₁ hx₂ h hh₁ hh₂ => le_trans ( by rw [ abs_of_nonneg ( by linarith : 0 ≤ x ) ] ; exact mul_le_mul_of_nonneg_left ( Real.exp_le_exp.mpr <| by nlinarith [ abs_nonneg ( Real.log x ) ] ) <| by nlinarith [ abs_nonneg ( Real.log x ) ] ) <| le_trans ( hM x hx₁ hx₂ ) <| le_max_left _ _ ⟩;
      exact ⟨ Min.min ( 1 / 2 ) ( ε / 4 / M ), lt_min ( by norm_num ) ( div_pos ( by linarith ) hM.1 ), fun x hx h hh₁ hh₂ => by nlinarith [ min_le_left ( 1 / 2 ) ( ε / 4 / M ), min_le_right ( 1 / 2 ) ( ε / 4 / M ), mul_div_cancel₀ ( ε / 4 ) hM.1.ne', abs_nonneg h, hM.2 x hx h hh₁ ( lt_of_lt_of_le hh₂ ( min_le_left _ _ ) ), mul_le_mul_of_nonneg_left ( hM.2 x hx h hh₁ ( lt_of_lt_of_le hh₂ ( min_le_left _ _ ) ) ) ( abs_nonneg h ) ] ⟩;
    exact ⟨ Min.min δ₂ ( 1 / 2 ), lt_min δ₂_pos ( by norm_num ), fun x hx h hh₁ hh₂ => lt_of_le_of_lt ( h_mean_value x hx h hh₁ ( lt_of_lt_of_le hh₂ ( min_le_right _ _ ) ) ) ( hδ₂ x hx h hh₁ ( lt_of_lt_of_le hh₂ ( min_le_left _ _ ) ) ) ⟩;
  refine' ⟨ Min.min ( 1 / 2 ) δ₂, lt_min ( by positivity ) δ₂_pos, fun h hh₁ hh₂ x hx => _ ⟩ ; cases lt_or_ge x δ₁ <;> simp_all [ abs_lt ];
  · cases lt_or_eq_of_le hx.1 <;> simp_all [ abs_of_nonneg ];
    · constructor <;> cases abs_cases ( Real.log x ) <;> nlinarith [ hδ₁ x hx.1 hx.2 ‹_› ‹_›, hδ₁ x hx.1 hx.2 ‹_› ‹_› |>.2 h hh₁ hh₂.1.1 hh₂.1.2 ];
    · by_cases h : 1 + h = 0 <;> simp_all [ division_def ] ; linarith [ Real.log_le_sub_one_of_pos ( show 0 < ε by linarith ) ] ;
      norm_num [ ← ‹0 = x› ] at * ; aesop;
  · constructor <;> linarith [ hδ₂ x ‹_› hx.2 h hh₁ hh₂.2.1 hh₂.2.2 ]

#print axioms rpow_slope_tendsto_uniformly

end D5.S3.Quantum.Divergence.RenyiDivergence.UniformPowerSlope
