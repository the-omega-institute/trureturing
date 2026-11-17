/- GID: D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/DiscreteThirdAssembly
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/DiscreteThirdAssembly
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Mean-square prime correlations: Normalized discrete cubic moments vanish uniformly for bounded variation weights. -/

import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.DiscreteMomentAsymptotics
import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.NormalizedFormalIntegrals
import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.UniformRates

/-! Uniform decay of normalized discrete cubic moments. -/

open Set Filter MeasureTheory
open scoped Topology

namespace D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer
noncomputable section
set_option autoImplicit false

private theorem p_third_normalized_estimate
    (SS : Finset ℕ → ℝ) (N H B C₁ C₂ E ε : ℝ)
    (w : ℝ → ℝ) (a b : Fin 3 → ℝ) (hN : 2 ≤ N) (hH : 0 < H)
    (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (hE : 0 ≤ E) (hw : BVBound w B)
    (hdiscrete : |discreteRaw N H a b w -
        (∫ x in N..2 * N, w (x / N) * Phi SS H (Real.log x) a b)| ≤
      C₁ * B * N ^ (1 / 2 + ε) * H ^ 3)
    (hformal : ∀ x ∈ Icc N (2 * N), |Phi SS H (Real.log x) a b| ≤
      C₂ * (E * (H * Real.log N) ^ (3 / 2 : ℝ) + H * (Real.log N) ^ 2)) :
    |discreteRaw N H a b w / (N * (H * Real.log N) ^ (3 / 2 : ℝ))| ≤
      (C₁ + C₂) * B * (E + Real.sqrt (Real.log N / H) +
        N ^ (-1 / 2 + ε) * H ^ (3 / 2 : ℝ) * (Real.log N) ^ (-3 / 2 : ℝ)) := by
  have hN0 : 0 < N := by linarith
  have hL : 0 < Real.log N := Real.log_pos (by linarith)
  have hB : 0 ≤ B := hw.2.2.1
  have hQ : 0 < (H * Real.log N) ^ (3 / 2 : ℝ) :=
    Real.rpow_pos_of_pos (mul_pos hH hL) _
  have hi := integrated_third_envelope SS N H B C₂ E w a b hN hH hC₂ hE hw hformal
  have hscaled := div_le_div_of_nonneg_right hdiscrete (mul_pos hN0 hQ).le
  rw [← abs_of_pos (mul_pos hN0 hQ), ← abs_div, sub_div] at hscaled
  rw [abs_of_pos (mul_pos hN0 hQ)] at hscaled
  have ht := (abs_sub_le (discreteRaw N H a b w /
      (N * (H * Real.log N) ^ (3 / 2 : ℝ))) _ 0).trans
    (add_le_add hscaled (by simpa only [sub_zero] using hi))
  simp only [sub_zero] at ht
  have hratio : C₁ * B * N ^ (1 / 2 + ε) * H ^ 3 /
      (N * (H * Real.log N) ^ (3 / 2 : ℝ)) =
      C₁ * B * (N ^ (-1 / 2 + ε) * H ^ (3 / 2 : ℝ) *
        (Real.log N) ^ (-3 / 2 : ℝ)) := by
    rw [show C₁ * B * N ^ (1 / 2 + ε) * H ^ 3 =
      C₁ * B * (N ^ (1 / 2 + ε) * H ^ 3) by ring, mul_div_assoc,
      arithmetic_ratio_three N H ε hN0 hH hL]
  rw [hratio] at ht
  have hR : 0 ≤ N ^ (-1 / 2 + ε) * H ^ (3 / 2 : ℝ) *
      (Real.log N) ^ (-3 / 2 : ℝ) := by positivity
  have hS : 0 ≤ E + Real.sqrt (Real.log N / H) :=
    add_nonneg hE (Real.sqrt_nonneg _)
  calc
    _ ≤ C₁ * B * (N ^ (-1 / 2 + ε) * H ^ (3 / 2 : ℝ) *
        (Real.log N) ^ (-3 / 2 : ℝ)) +
        C₂ * B * (E + Real.sqrt (Real.log N / H)) := ht
    _ ≤ (C₁ * B + C₂ * B) * (N ^ (-1 / 2 + ε) * H ^ (3 / 2 : ℝ) *
        (Real.log N) ^ (-3 / 2 : ℝ)) +
        (C₁ * B + C₂ * B) * (E + Real.sqrt (Real.log N / H)) :=
      add_le_add
        (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (mul_nonneg hC₂ hB)) hR)
        (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (mul_nonneg hC₁ hB)) hS)
    _ = _ := by ring

/-- The normalized discrete cubic moment tends uniformly to zero over the length band. -/
theorem eventual_discrete_third
    (SS : Finset ℕ → ℝ) (α β M : ℝ) (hα : 0 < α) (hαβ : α < β)
    (hβ : β < 1 / 3) (hSS : SS ∅ = 1) (hSS1 : ∀ d, SS {d} = 1)
    (hMS : MeanSquareHL 3 SS β) (hcor : IntervalCorrelations SS) (hM : 1 ≤ M)
    (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ N : ℝ in atTop,
      ∀ H : ℕ, N ^ α ≤ (H : ℝ) → (H : ℝ) ≤ N ^ β →
      ∀ B (w : ℝ → ℝ), BVBound w B → ∀ a b : Fin 3 → ℝ, admissible M a b →
      |discreteRaw N H a b w / (N * ((H : ℝ) * Real.log N) ^ (3 / 2 : ℝ))| ≤
        B * δ := by
  let ε : ℝ := (1 / 2 - (3 / 2) * β) / 2
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hεβ : ε < 1 / 2 - (3 / 2) * β := by dsimp [ε]; linarith
  have hβ1 : β < 1 := by linarith
  obtain ⟨⟨C₁, hC₁, harith⟩, ⟨C₂, hC₂, η, hη, hanti, hlim, hformal⟩⟩ :=
    discrete_moment_asymptotic_inputs SS α β hα hαβ hβ1 hSS hSS1 hMS hcor M hM ε hε
  let t : ℝ := δ / (3 * (C₁ + C₂ + 1))
  have hC : 0 < C₁ + C₂ + 1 := by linarith
  have ht : 0 < t := div_pos hδ (mul_pos (by norm_num) hC)
  have hbudget : (C₁ + C₂) * (3 * t) ≤ δ := by
    calc
      _ ≤ (C₁ + C₂ + 1) * (3 * t) :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = δ := by dsimp [t]; field_simp
  filter_upwards [harith, hformal, sqrt_rate α t hα ht,
    arithmetic_rate_three β ε t (hα.trans hαβ) hε hεβ ht,
    antitone_modulus_rate η α t hα ht hanti hlim,
    range_geometry α β M hα hβ1 (by linarith)]
    with N hdiscrete hformal hsqrt hrate hmod hgeometry
  intro H hHlo hHhi B w hw a b hab
  have hN : 2 ≤ N := hgeometry.1
  have hN0 : 0 < N := by linarith
  have hH2 : 2 ≤ (H : ℝ) := (hgeometry.2.2 H hHlo hHhi).1
  have hH : 0 < (H : ℝ) := by linarith
  have hf : ∀ x ∈ Icc N (2 * N), |Phi SS H (Real.log x) a b| ≤
      C₂ * (η H * ((H : ℝ) * Real.log N) ^ (3 / 2 : ℝ) +
        (H : ℝ) * (Real.log N) ^ 2) := by
    intro x hx
    have hlo : Real.log N ≤ Real.log x := Real.log_le_log hN0 hx.1
    have hhi : Real.log x ≤ Real.log N + Real.log 2 := by
      calc
        _ ≤ Real.log (2 * N) := Real.log_le_log (hN0.trans_le hx.1) hx.2
        _ = _ := by rw [Real.log_mul (by norm_num) hN0.ne']; ring
    exact (hformal H (Real.log x) hHlo hHhi hlo hhi).1 a b hab
  have he := p_third_normalized_estimate SS N H B C₁ C₂ (η H) ε w a b
    hN hH hC₁ hC₂ (hη H) hw
    (hdiscrete H hHlo hHhi B w hw 3 ⟨Or.inr (Or.inl rfl), le_rfl⟩ a b hab) hf
  have hsmall : η H + Real.sqrt (Real.log N / (H : ℝ)) +
      N ^ (-1 / 2 + ε) * (H : ℝ) ^ (3 / 2 : ℝ) *
        (Real.log N) ^ (-3 / 2 : ℝ) ≤ 3 * t := by
    linarith only [(hmod H hHlo).2, hsqrt H hHlo, hrate H (by linarith) hHhi]
  calc
    _ ≤ (C₁ + C₂) * B * (η H + Real.sqrt (Real.log N / (H : ℝ)) +
        N ^ (-1 / 2 + ε) * (H : ℝ) ^ (3 / 2 : ℝ) *
          (Real.log N) ^ (-3 / 2 : ℝ)) := he
    _ ≤ (C₁ + C₂) * B * (3 * t) :=
      mul_le_mul_of_nonneg_left hsmall (mul_nonneg (add_nonneg hC₁ hC₂) hw.2.2.1)
    _ = B * ((C₁ + C₂) * (3 * t)) := by ring
    _ ≤ B * δ := mul_le_mul_of_nonneg_left hbudget hw.2.2.1

end
end D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer
