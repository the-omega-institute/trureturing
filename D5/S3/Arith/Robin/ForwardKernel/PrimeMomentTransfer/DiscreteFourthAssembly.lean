/- GID: D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/DiscreteFourthAssembly
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/DiscreteFourthAssembly
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Mean-square prime correlations: Normalized discrete fourth moments converge uniformly on polynomial length bands. -/

import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.DiscreteMomentAsymptotics
import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.NormalizedFormalIntegrals
import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.FourthMainIntegral
import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.UniformRates

/-! Uniform normalization of discrete fourth moments. -/

open Set Filter MeasureTheory
open scoped Topology

namespace D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer
noncomputable section
set_option autoImplicit false

private theorem p_fourth_normalized_estimate
    (SS : Finset ℕ → ℝ) (N H M B C₁ C₂ E ε : ℝ)
    (w : ℝ → ℝ) (a b : Fin 4 → ℝ)
    (hN : 2 ≤ N) (hH : 1 ≤ H) (hHN : H ≤ N) (hM : 0 ≤ M)
    (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (hE : 0 ≤ E)
    (hw : BVBound w B) (hab : admissible M a b)
    (hDI : |discreteRaw N H a b w -
      (∫ x in N..2 * N, w (x / N) * Phi SS H (Real.log x) a b)| ≤
        C₁ * B * N ^ (1 / 2 + ε) * H ^ 4)
    (hf : ∀ x ∈ Icc N (2 * N), |Phi SS H (Real.log x) a b -
      H ^ 2 * (Real.log x - Real.log H) ^ 2 * W4 a b| ≤
        C₂ * (E * H ^ 2 * (Real.log N) ^ 2 + H ^ 2 * Real.log N)) :
    |discreteRaw N H a b w / (N * (H * Real.log N) ^ 2) -
      (∫ t in (1 : ℝ)..2, w t) * (kappa N H) ^ 2 * W4 a b| ≤
        (C₁ + C₂ + 9 * M ^ 2 * Real.log 2) * B * (E + 1 / Real.log N +
          N ^ (-1 / 2 + ε) * H ^ 2 * (Real.log N) ^ (-2 : ℝ)) := by
  have hN0 : 0 < N := by linarith
  have hH0 : 0 < H := by linarith
  have hL : 0 < Real.log N := Real.log_pos (by linarith)
  have hB : 0 ≤ B := hw.2.2.1
  have hi := integrated_fourth_envelope SS N H B C₂ E w a b hN hH0 hC₂ hE hw hf
  have hm := fourth_main_integral_error N H M B w a b hN hH hHN hM hw hab
  have hm' : |(∫ x in N..2 * N, w (x / N) *
      (((Real.log x - Real.log H) / Real.log N) ^ 2 * W4 a b)) / N -
      (∫ t in (1 : ℝ)..2, w t) * (kappa N H) ^ 2 * W4 a b| ≤
        (9 * M ^ 2 * Real.log 2) * B * (1 / Real.log N) := by
    have heq : (∫ x in N..2 * N, w (x / N) *
        (((Real.log x - Real.log H) / Real.log N) ^ 2 * W4 a b)) / N -
        (∫ t in (1 : ℝ)..2, w t) * (kappa N H) ^ 2 * W4 a b =
      ((∫ x in N..2 * N, w (x / N) *
        (((Real.log x - Real.log H) / Real.log N) ^ 2 * W4 a b)) -
        N * (∫ t in (1 : ℝ)..2, w t) * (kappa N H) ^ 2 * W4 a b) / N := by
      rw [sub_div]
      congr 1
      field_simp
    rw [heq, abs_div, abs_of_pos hN0]
    calc
      _ ≤ (N * B * (9 * M ^ 2 * Real.log 2 / Real.log N)) / N :=
        div_le_div_of_nonneg_right hm hN0.le
      _ = _ := by field_simp
  have hIA := (abs_sub_le _ _ _).trans (add_le_add hi hm')
  have hNQ : 0 < N * (H * Real.log N) ^ 2 :=
    mul_pos hN0 (pow_pos (mul_pos hH0 hL) _)
  have hscaled := div_le_div_of_nonneg_right hDI hNQ.le
  rw [← abs_of_pos hNQ, ← abs_div, sub_div] at hscaled
  rw [abs_of_pos hNQ] at hscaled
  have ht := (abs_sub_le (discreteRaw N H a b w / (N * (H * Real.log N) ^ 2))
    _ _).trans (add_le_add hscaled hIA)
  have har : (C₁ * B * N ^ (1 / 2 + ε) * H ^ 4) /
      (N * (H * Real.log N) ^ 2) =
        C₁ * B * (N ^ (-1 / 2 + ε) * H ^ 2 * (Real.log N) ^ (-2 : ℝ)) := by
    rw [show C₁ * B * N ^ (1 / 2 + ε) * H ^ 4 =
      (C₁ * B) * (N ^ (1 / 2 + ε) * H ^ 4) by ring, mul_div_assoc,
      arithmetic_ratio_four N H ε hN0 hH0 hL]
  rw [har] at ht
  apply ht.trans
  have hr : 0 ≤ N ^ (-1 / 2 + ε) * H ^ 2 * (Real.log N) ^ (-2 : ℝ) := by positivity
  have hl : 0 ≤ 1 / Real.log N := by positivity
  have hc : 0 ≤ 9 * M ^ 2 * Real.log 2 := by positivity
  apply le_of_sub_nonneg
  convert add_nonneg (add_nonneg
    (mul_nonneg (mul_nonneg hC₁ hB) (add_nonneg hE hl))
    (mul_nonneg (mul_nonneg hC₂ hB) hr))
    (mul_nonneg (mul_nonneg hc hB) (add_nonneg hE hr)) using 1
  ring

/-- The fourth discrete mixed moment approaches its overlap pairing uniformly. -/
theorem eventual_discrete_fourth (SS : Finset ℕ → ℝ) (α β M : ℝ)
    (hα : 0 < α) (hαβ : α < β) (hβ : β < 1 / 4)
    (hSS : SS ∅ = 1) (hSS1 : ∀ d, SS {d} = 1)
    (hMS : MeanSquareHL4 SS β) (hcor : IntervalCorrelations SS) (hM : 1 ≤ M)
    (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ N : ℝ in atTop,
      ∀ H : ℕ, N ^ α ≤ (H : ℝ) → (H : ℝ) ≤ N ^ β →
      ∀ B (w : ℝ → ℝ), BVBound w B → ∀ a b : Fin 4 → ℝ, admissible M a b →
        |discreteRaw N H a b w / (N * ((H : ℝ) * Real.log N) ^ 2) -
          (∫ t in (1 : ℝ)..2, w t) * (kappa N H) ^ 2 * W4 a b| ≤ B * δ := by
  have hβ1 : β < 1 := by linarith
  obtain ⟨ε, hε, hεβ⟩ := transfer_epsilon_exists β hβ
  obtain ⟨⟨C₁, hC₁, htransfer⟩, ⟨C₂, hC₂, η, hη, hanti, hlim, hformal⟩⟩ :=
    discrete_moment_asymptotic_inputs SS α β hα hαβ hβ1 hSS hSS1 hMS hcor M hM ε hε
  let K := C₁ + C₂ + 9 * M ^ 2 * Real.log 2
  have hK : 0 ≤ K := by dsimp [K]; positivity
  let t := δ / (3 * (K + 1))
  have ht : 0 < t := by dsimp [t]; positivity
  have hbudget : (K + 1) * (t + t + t) = δ := by
    dsimp [t]
    field_simp
    ring
  filter_upwards [htransfer, hformal, range_geometry α β M hα hβ1 (by linarith),
    antitone_modulus_rate η α t hα ht hanti hlim, inverse_log_rate t ht,
    arithmetic_rate_four β ε t hε hεβ ht]
    with N htransfer hformal hgeom hmod hinv harith
  intro H hHlo hHhi B w hw a b hab
  have hN0 : 0 < N := by linarith [hgeom.1]
  obtain ⟨hH2, hHN, _⟩ := hgeom.2.2 H hHlo hHhi
  have hH1 : 1 ≤ (H : ℝ) := by linarith
  have hf : ∀ x ∈ Icc N (2 * N), |Phi SS H (Real.log x) a b -
      (H : ℝ) ^ 2 * (Real.log x - Real.log H) ^ 2 * W4 a b| ≤
        C₂ * (η H * (H : ℝ) ^ 2 * (Real.log N) ^ 2 + (H : ℝ) ^ 2 * Real.log N) := by
    intro x hx
    have hx0 : 0 < x := hN0.trans_le hx.1
    have hlower : Real.log N ≤ Real.log x := Real.log_le_log hN0 hx.1
    have hupper : Real.log x ≤ Real.log N + Real.log 2 := by
      calc
        _ ≤ Real.log (2 * N) := Real.log_le_log hx0 hx.2
        _ = _ := by rw [Real.log_mul (by norm_num) hN0.ne']; ring
    exact (hformal H (Real.log x) hHlo hHhi hlower hupper).2 a b hab
  have hb := p_fourth_normalized_estimate SS N H M B C₁ C₂ (η H) ε w a b
    hgeom.1 hH1 hHN (by linarith) hC₁ hC₂ (hη H) hw hab
    (htransfer H hHlo hHhi B w hw 4 ⟨Or.inr (Or.inr rfl), le_rfl⟩ a b hab) hf
  have hB : 0 ≤ B := hw.2.2.1
  calc
    _ ≤ K * B * (η H + 1 / Real.log N +
        N ^ (-1 / 2 + ε) * (H : ℝ) ^ 2 * (Real.log N) ^ (-2 : ℝ)) := hb
    _ ≤ K * B * (t + t + t) := mul_le_mul_of_nonneg_left
      (add_le_add (add_le_add (hmod H hHlo).2 hinv)
        (harith H (by positivity) hHhi)) (mul_nonneg hK hB)
    _ ≤ (K + 1) * B * (t + t + t) := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by linarith : K ≤ K + 1) hB) (by positivity)
    _ = B * δ := by calc
      _ = B * ((K + 1) * (t + t + t)) := by ring
      _ = _ := by rw [hbudget]

end
end D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer
