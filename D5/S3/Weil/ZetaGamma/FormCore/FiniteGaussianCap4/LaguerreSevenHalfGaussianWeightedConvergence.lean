/- GID: D5/S3/Weil/ZetaGamma/FormCore/FiniteGaussianCap4/LaguerreSevenHalfGaussianWeightedConvergence
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:finite-gaussian-helper)
   anchors: []
   utility: none
   digest: Actual Gaussian weighted convergence for the same-source cap comparison. -/

/-
SPDX-License-Identifier: Apache-2.0
UNCOMPILED source, 2026-10-26. No compiler or acceptance claim.

Actual weighted Gaussian error integrals, obtained by dominated convergence.
No L2 expansion, completeness, or continuous Mellin functional is assumed.
The imported supplier attribution/license notices remain applicable there.
This module contains new proofs using Mathlib APIs, not ported proof bodies.
-/
import D5.S3.Weil.ZetaGamma.FormCore.FiniteGaussianCap4.LaguerreSevenHalfGaussianBounds
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.Real.Sqrt

/-! Actual Gaussian weighted convergence for the same-source cap comparison. -/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped BigOperators Topology

namespace FiniteGaussianCap4.LaguerreSevenHalf

/-- Even a negative real power is continuous, hence measurable, on x>0. -/
private theorem positive_halfline_weight_measurable (s : ℝ) :
    AEStronglyMeasurable (fun x : ℝ => x ^ s) (volume.restrict (Ioi 0)) := by
  have hw : ContinuousOn (fun x : ℝ => x ^ s) (Ioi 0) :=
    continuousOn_id.rpow_const (fun x hx => Or.inl (ne_of_gt hx))
  exact hw.aestronglyMeasurable measurableSet_Ioi

/-- Used with the actual finite polynomial/exponential expressions below. -/
private theorem weighted_continuous_measurable (s : ℝ) {f : ℝ → ℝ}
    (hf : Continuous f) :
    AEStronglyMeasurable (fun x => x ^ s * f x) (volume.restrict (Ioi 0)) := by
  exact (positive_halfline_weight_measurable s).mul
    (hf.continuousOn.aestronglyMeasurable measurableSet_Ioi)

private theorem weighted_norm_bound (s x u B : ℝ) (hx : 0 ≤ x) (hu : |u| ≤ B) :
    ‖x ^ s * u‖ ≤ x ^ s * B := by
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg hx s)]
  exact mul_le_mul_of_nonneg_left hu (Real.rpow_nonneg hx s)

/-- Squaring the actual error majorant doubles the decay rate. -/
private theorem weighted_square_norm_bound (s x u K c : ℝ) (hx : 0 ≤ x)
    (hu : |u| ≤ 2 * K * Real.exp (-c * x)) :
    ‖x ^ s * |u| ^ 2‖ ≤ (2 * K) ^ 2 * (x ^ s * Real.exp (-(2 * c) * x)) := by
  have he : Real.exp (-c * x) ^ 2 = Real.exp (-(2 * c) * x) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hu2 : |u| ^ 2 ≤ (2 * K * Real.exp (-c * x)) ^ 2 :=
    pow_le_pow_left₀ (abs_nonneg u) hu 2
  calc
    ‖x ^ s * |u| ^ 2‖ = x ^ s * |u| ^ 2 := by
      rw [Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg (Real.rpow_nonneg hx s) (sq_nonneg _))]
    _ ≤ x ^ s * (2 * K * Real.exp (-c * x)) ^ 2 :=
      mul_le_mul_of_nonneg_left hu2 (Real.rpow_nonneg hx s)
    _ = (2 * K) ^ 2 * (x ^ s * Real.exp (-(2 * c) * x)) := by
      rw [mul_pow, he]
      ring

/-- Conditional DCT wrapper, consumed by both actual unconditional error theorems.
It also records integrability of every approximating error integrand. -/
private theorem dominated_zero_with_integrability
    (F : ℕ → ℝ → ℝ) (bound : ℝ → ℝ)
    (hF : ∀ N, AEStronglyMeasurable (F N) (volume.restrict (Ioi 0)))
    (hbound : Integrable bound (volume.restrict (Ioi 0)))
    (hdom : ∀ N, ∀ᵐ x ∂volume.restrict (Ioi 0), ‖F N x‖ ≤ bound x)
    (hlim : ∀ᵐ x ∂volume.restrict (Ioi 0),
      Tendsto (fun N => F N x) atTop (𝓝 (0 : ℝ))) :
    (∀ N, Integrable (F N) (volume.restrict (Ioi 0))) ∧
      Tendsto (fun N => ∫ x in Ioi (0 : ℝ), F N x) atTop (𝓝 (0 : ℝ)) := by
  refine ⟨fun N => hbound.mono' (hF N) (hdom N), ?_⟩
  simpa only [integral_zero] using
    (MeasureTheory.tendsto_integral_of_dominated_convergence
      (μ := volume.restrict (Ioi (0 : ℝ))) (f := fun _ : ℝ => (0 : ℝ))
      bound hF hbound hdom hlim)

/-- For each real site and each power s>-1, the actual weighted absolute error
is integrable at every N and its integral tends to zero. -/
theorem gaussian_weighted_abs_error_convergence (a s : ℝ) (hs : -1 < s) :
    (∀ N, IntegrableOn
      (fun x => x ^ s * |gaussianPartialSum a N x - gaussianAtom a x|) (Ioi 0)) ∧
    Tendsto (fun N => ∫ x in Ioi (0 : ℝ),
      x ^ s * |gaussianPartialSum a N x - gaussianAtom a x|)
      atTop (𝓝 (0 : ℝ)) := by
  obtain ⟨K, c, _hK, hc, _hT, _hf, hE⟩ := gaussian_dominated_bounds a
  refine dominated_zero_with_integrability
    (fun N x => x ^ s * |gaussianPartialSum a N x - gaussianAtom a x|)
    (fun x => (2 * K) * (x ^ s * Real.exp (-c * x))) ?_ ?_ ?_ ?_
  · intro N
    exact weighted_continuous_measurable s
      ((continuous_gaussianPartialSum a N).sub (continuous_gaussianAtom a)).abs
  · exact Integrable.const_mul (integrable_decay_weight s c hs hc) (2 * K)
  · intro N
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    calc
      ‖x ^ s * |gaussianPartialSum a N x - gaussianAtom a x|‖ ≤
          x ^ s * (2 * K * Real.exp (-c * x)) :=
        weighted_norm_bound s x _ _ hx.le (by simpa only [abs_abs] using hE N x hx)
      _ = (2 * K) * (x ^ s * Real.exp (-c * x)) := by ring
  · exact Filter.Eventually.of_forall (fun x => by
      simpa using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => x ^ s) atTop (𝓝 (x ^ s))).mul
          (gaussian_error_tendsto a x).abs)

/-- Squared weighted errors for every s>-1. The dominating function is
(2K)^2 x^s exp(-2cx), proved integrable before DCT is invoked. -/
theorem gaussian_weighted_square_error_convergence (a s : ℝ) (hs : -1 < s) :
    (∀ N, IntegrableOn
      (fun x => x ^ s * |gaussianPartialSum a N x - gaussianAtom a x| ^ 2) (Ioi 0)) ∧
    Tendsto (fun N => ∫ x in Ioi (0 : ℝ),
      x ^ s * |gaussianPartialSum a N x - gaussianAtom a x| ^ 2)
      atTop (𝓝 (0 : ℝ)) := by
  obtain ⟨K, c, _hK, hc, _hT, _hf, hE⟩ := gaussian_dominated_bounds a
  refine dominated_zero_with_integrability
    (fun N x => x ^ s * |gaussianPartialSum a N x - gaussianAtom a x| ^ 2)
    (fun x => (2 * K) ^ 2 * (x ^ s * Real.exp (-(2 * c) * x))) ?_ ?_ ?_ ?_
  · intro N
    exact weighted_continuous_measurable s
      (((continuous_gaussianPartialSum a N).sub (continuous_gaussianAtom a)).abs.pow 2)
  · exact Integrable.const_mul
      (integrable_decay_weight s (2 * c) hs (mul_pos (by norm_num) hc)) ((2 * K) ^ 2)
  · intro N
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact weighted_square_norm_bound s x _ K c hx.le (hE N x hx)
  · exact Filter.Eventually.of_forall (fun x => by
      simpa using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => x ^ s) atTop (𝓝 (x ^ s))).mul
          ((gaussian_error_tendsto a x).abs.pow 2))

/-- Actual signed integral convergence, with integrability of the finite
prefixes and the Gaussian limit. No integral/series interchange is a premise. -/
theorem gaussian_weighted_signed_convergence (a s : ℝ) (hs : -1 < s) :
    (∀ N, IntegrableOn (fun x => x ^ s * gaussianPartialSum a N x) (Ioi 0)) ∧
    IntegrableOn (fun x => x ^ s * gaussianAtom a x) (Ioi 0) ∧
    Tendsto (fun N => ∫ x in Ioi (0 : ℝ), x ^ s * gaussianPartialSum a N x)
      atTop (𝓝 (∫ x in Ioi (0 : ℝ), x ^ s * gaussianAtom a x)) := by
  obtain ⟨K, c, _hK, hc, hT, hf, _hE⟩ := gaussian_dominated_bounds a
  have hmeas (N : ℕ) : AEStronglyMeasurable
      (fun x => x ^ s * gaussianPartialSum a N x) (volume.restrict (Ioi 0)) :=
    weighted_continuous_measurable s (continuous_gaussianPartialSum a N)
  have hfmeas : AEStronglyMeasurable
      (fun x => x ^ s * gaussianAtom a x) (volume.restrict (Ioi 0)) :=
    weighted_continuous_measurable s (continuous_gaussianAtom a)
  have hb : Integrable (fun x => K * (x ^ s * Real.exp (-c * x)))
      (volume.restrict (Ioi 0)) :=
    Integrable.const_mul (integrable_decay_weight s c hs hc) K
  have hdom (N : ℕ) : ∀ᵐ x ∂volume.restrict (Ioi 0),
      ‖x ^ s * gaussianPartialSum a N x‖ ≤ K * (x ^ s * Real.exp (-c * x)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    calc
      ‖x ^ s * gaussianPartialSum a N x‖ ≤ x ^ s * (K * Real.exp (-c * x)) :=
        weighted_norm_bound s x _ _ hx.le (hT N x hx)
      _ = K * (x ^ s * Real.exp (-c * x)) := by ring
  have hdomf : ∀ᵐ x ∂volume.restrict (Ioi 0),
      ‖x ^ s * gaussianAtom a x‖ ≤ K * (x ^ s * Real.exp (-c * x)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    calc
      ‖x ^ s * gaussianAtom a x‖ ≤ x ^ s * (K * Real.exp (-c * x)) :=
        weighted_norm_bound s x _ _ hx.le (hf x hx)
      _ = K * (x ^ s * Real.exp (-c * x)) := by ring
  refine ⟨fun N => hb.mono' (hmeas N) (hdom N), hb.mono' hfmeas hdomf, ?_⟩
  apply MeasureTheory.tendsto_integral_of_dominated_convergence
    (fun x => K * (x ^ s * Real.exp (-c * x))) hmeas hb hdom
  exact Filter.Eventually.of_forall (fun x =>
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => x ^ s) atTop (𝓝 (x ^ s))).mul
      (gaussianPartialSum_tendsto a x))

/-- The physical H error integral, with weight x^(7/2). -/
theorem gaussian_H_error_integral_tendsto (a : ℝ) :
    Tendsto (fun N => ∫ x in Ioi (0 : ℝ),
      x ^ (7 / 2 : ℝ) * |gaussianPartialSum a N x - gaussianAtom a x| ^ 2)
      atTop (𝓝 (0 : ℝ)) := by
  exact (gaussian_weighted_square_error_convergence a (7 / 2) (by norm_num)).2

/-- The multiplication-by-x error integral, with weight x^(11/2). -/
theorem gaussian_x_graph_error_integral_tendsto (a : ℝ) :
    Tendsto (fun N => ∫ x in Ioi (0 : ℝ),
      x ^ (11 / 2 : ℝ) * |gaussianPartialSum a N x - gaussianAtom a x| ^ 2)
      atTop (𝓝 (0 : ℝ)) := by
  exact (gaussian_weighted_square_error_convergence a (11 / 2) (by norm_num)).2

/-- The central Mellin absolute error, with weight x^(5/4). -/
theorem gaussian_Mellin_abs_error_integral_tendsto (a : ℝ) :
    Tendsto (fun N => ∫ x in Ioi (0 : ℝ),
      x ^ (5 / 4 : ℝ) * |gaussianPartialSum a N x - gaussianAtom a x|)
      atTop (𝓝 (0 : ℝ)) := by
  exact (gaussian_weighted_abs_error_convergence a (5 / 4) (by norm_num)).2

theorem gaussian_Mellin_signed_integral_tendsto (a : ℝ) :
    Tendsto (fun N => ∫ x in Ioi (0 : ℝ),
      x ^ (5 / 4 : ℝ) * gaussianPartialSum a N x)
      atTop (𝓝 (∫ x in Ioi (0 : ℝ), x ^ (5 / 4 : ℝ) * gaussianAtom a x)) := by
  exact (gaussian_weighted_signed_convergence a (5 / 4) (by norm_num)).2.2

/-- Square-root packaging of the actual H error integral; no abstract basis. -/
theorem gaussian_H_error_sqrt_integral_tendsto (a : ℝ) :
    Tendsto (fun N => Real.sqrt (∫ x in Ioi (0 : ℝ),
      x ^ (7 / 2 : ℝ) * |gaussianPartialSum a N x - gaussianAtom a x| ^ 2))
      atTop (𝓝 (0 : ℝ)) := by
  simpa only [Real.sqrt_zero] using (gaussian_H_error_integral_tendsto a).sqrt

theorem gaussian_x_graph_error_sqrt_integral_tendsto (a : ℝ) :
    Tendsto (fun N => Real.sqrt (∫ x in Ioi (0 : ℝ),
      x ^ (11 / 2 : ℝ) * |gaussianPartialSum a N x - gaussianAtom a x| ^ 2))
      atTop (𝓝 (0 : ℝ)) := by
  simpa only [Real.sqrt_zero] using (gaussian_x_graph_error_integral_tendsto a).sqrt

/-- Explicit square root of the sum of H and x-graph squared errors. This
does not introduce an Lp quotient, a basis-completeness premise, or a Mellin
functional on all of H. -/
theorem gaussian_graph_error_size_tendsto (a : ℝ) :
    Tendsto (fun N => Real.sqrt
      ((∫ x in Ioi (0 : ℝ),
        x ^ (7 / 2 : ℝ) * |gaussianPartialSum a N x - gaussianAtom a x| ^ 2) +
       (∫ x in Ioi (0 : ℝ),
        x ^ (11 / 2 : ℝ) * |gaussianPartialSum a N x - gaussianAtom a x| ^ 2)))
      atTop (𝓝 (0 : ℝ)) := by
  simpa only [zero_add, Real.sqrt_zero] using
    ((gaussian_H_error_integral_tendsto a).add
      (gaussian_x_graph_error_integral_tendsto a)).sqrt

end FiniteGaussianCap4.LaguerreSevenHalf
