/- GID: D5/S3/Weil/ZetaBridge/WeilPrimeActivationEdge
   generality: I
   mirror-B: D5/B/S3/Weil/ZetaBridge/WeilPrimeActivationEdge
   mirror-E: none(waiver:original-compressed-translation-and-Schur-realization)
   anchors: []
   utility: none
   digest: Bound the actual prime edge overlap and its zero-trace even Fourier stencil, retaining the full complex cross terms. -/

import D5.S3.Weil.ZetaBridge.WeilEvenDualStencil
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Low-block behaviour of a newly visible prime

On the common interval [-1,1], a newly activated prime has shift 2-h.
Its even low-mode matrix involves integral_0^h cos(u*t)*cos(v*(h-t)) dt.
The first theorem computes its rank-one leading term with a cubic remainder.
For the existing zero-trace stencil V_n+V_(-n)-2V_0, the actual edge profile
is sqrt(2) times `evenStencilEdge`. Its squared mass and cross-edge pairing
are proved to have fifth-order bounds, with integrability derived.

The physical compressed-translation identification and the full-space Schur
certificate are explained in RH_RESEARCH_LANE_THEORY.md. The executable
uniform parameter certificate retains nonzero boundary values of the actual
candidate; it does not impose the stencil's zero trace on that candidate.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace D5.S3.Weil.ZetaBridge.WeilPrimeActivationEdge

open MeasureTheory Set
open scoped BigOperators ComplexConjugate

private theorem cos_defect (x : ℝ) : |Real.cos x - 1| ≤ x ^ 2 / 2 := by
  rw [abs_of_nonpos (sub_nonpos.mpr (Real.cos_le_one x))]
  linarith [Real.one_sub_sq_div_two_le_cos (x := x)]

private theorem square_overlap_integral (h : ℝ) :
    (∫ t : ℝ in 0..h, t ^ 2 * (h - t) ^ 2) = h ^ 5 / 30 := by
  have h2 : IntervalIntegrable (fun t : ℝ => h ^ 2 * t ^ 2) volume 0 h :=
    (by fun_prop : Continuous (fun t : ℝ => h ^ 2 * t ^ 2)).intervalIntegrable _ _
  have h3 : IntervalIntegrable (fun t : ℝ => (2 * h) * t ^ 3) volume 0 h :=
    (by fun_prop : Continuous (fun t : ℝ => (2 * h) * t ^ 3)).intervalIntegrable _ _
  have h4 : IntervalIntegrable (fun t : ℝ => t ^ 4) volume 0 h :=
    (by fun_prop : Continuous (fun t : ℝ => t ^ 4)).intervalIntegrable _ _
  have heq : (fun t : ℝ => t ^ 2 * (h - t) ^ 2) =
      (fun t => h ^ 2 * t ^ 2 - (2 * h) * t ^ 3 + t ^ 4) := by
    funext t
    ring
  rw [heq, intervalIntegral.integral_add (h2.sub h3) h4,
    intervalIntegral.integral_sub h2 h3,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  norm_num [integral_pow]
  <;> ring

private theorem quadratic_edge_integral (u v h : ℝ) :
    (∫ t : ℝ in 0..h, ((u * t) ^ 2 + (v * (h - t)) ^ 2) / 2) =
      (u ^ 2 + v ^ 2) * h ^ 3 / 6 := by
  have h2 : IntervalIntegrable (fun t : ℝ => ((u ^ 2 + v ^ 2) / 2) * t ^ 2) volume 0 h :=
    (by fun_prop : Continuous (fun t : ℝ => ((u ^ 2 + v ^ 2) / 2) * t ^ 2)).intervalIntegrable _ _
  have h1 : IntervalIntegrable (fun t : ℝ => (v ^ 2 * h) * t) volume 0 h :=
    (by fun_prop : Continuous (fun t : ℝ => (v ^ 2 * h) * t)).intervalIntegrable _ _
  have hc : IntervalIntegrable (fun _ : ℝ => v ^ 2 * h ^ 2 / 2) volume 0 h :=
    continuous_const.intervalIntegrable _ _
  have heq : (fun t : ℝ => ((u * t) ^ 2 + (v * (h - t)) ^ 2) / 2) =
      (fun t => ((u ^ 2 + v ^ 2) / 2) * t ^ 2 - (v ^ 2 * h) * t + v ^ 2 * h ^ 2 / 2) := by
    funext t
    ring
  rw [heq, intervalIntegral.integral_add (h2.sub h1) hc,
    intervalIntegral.integral_sub h2 h1,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  norm_num [integral_pow]
  <;> ring

/-- The actual edge-overlap integral of two even Fourier profiles has a
rank-one leading term h. The bound covers zero frequency and every h>=0. -/
theorem cosine_prime_edge_remainder (u v h : ℝ) (hh : 0 ≤ h) :
    |(∫ t : ℝ in 0..h, Real.cos (u * t) * Real.cos (v * (h - t))) - h| ≤
      (u ^ 2 + v ^ 2) * h ^ 3 / 6 := by
  have hf : Continuous (fun t : ℝ => Real.cos (u * t) * Real.cos (v * (h - t))) := by fun_prop
  have heq : (∫ t : ℝ in 0..h, Real.cos (u * t) * Real.cos (v * (h - t))) - h =
      ∫ t : ℝ in 0..h, Real.cos (u * t) * Real.cos (v * (h - t)) - 1 := by
    rw [intervalIntegral.integral_sub (hf.intervalIntegrable _ _) (continuous_const.intervalIntegrable _ _)]
    simp
  rw [heq]
  calc
    _ ≤ ∫ t : ℝ in 0..h, |Real.cos (u * t) * Real.cos (v * (h - t)) - 1| :=
      intervalIntegral.abs_integral_le_integral_abs hh
    _ ≤ ∫ t : ℝ in 0..h, ((u * t) ^ 2 + (v * (h - t)) ^ 2) / 2 := by
      apply intervalIntegral.integral_mono_on hh
        ((hf.sub continuous_const).abs.intervalIntegrable _ _)
        ((by fun_prop : Continuous (fun t : ℝ => ((u * t) ^ 2 + (v * (h - t)) ^ 2) / 2)).intervalIntegrable _ _)
      intro t _
      simp only [Pi.sub_apply]
      have hx := cos_defect (u * t)
      have hy := cos_defect (v * (h - t))
      calc
        _ = |(Real.cos (u * t) - 1) * Real.cos (v * (h - t)) +
            (Real.cos (v * (h - t)) - 1)| := by congr 1; ring
        _ ≤ |Real.cos (u * t) - 1| * |Real.cos (v * (h - t))| +
            |Real.cos (v * (h - t)) - 1| := by
              simpa only [abs_mul] using
                abs_add_le ((Real.cos (u * t) - 1) * Real.cos (v * (h - t)))
                  (Real.cos (v * (h - t)) - 1)
        _ ≤ ((u * t) ^ 2 / 2) * 1 + (v * (h - t)) ^ 2 / 2 :=
          add_le_add (mul_le_mul hx (Real.abs_cos_le_one _) (abs_nonneg _) (by positivity)) hy
        _ = _ := by ring
    _ = _ := quadratic_edge_integral u v h

/-- Boundary profile of the previously owned even zero-trace Fourier stencil.
On [-1,1] with the phase-adjusted basis its physical value is sqrt(2) times
this function of the inward endpoint distance. -/
def evenStencilEdge (S : Finset ℤ) (v : ℤ → ℂ) (t : ℝ) : ℂ :=
  ∑ n ∈ S, v n * ((Real.cos (Real.pi * (n : ℝ) * t) - 1 : ℝ) : ℂ)

private theorem edge_norm (S : Finset ℤ) (v : ℤ → ℂ) (t : ℝ) :
    ‖evenStencilEdge S v t‖ ≤
      (∑ n ∈ S, ‖v n‖ * (Real.pi * (n : ℝ)) ^ 2) * t ^ 2 / 2 := by
  unfold evenStencilEdge
  calc
    _ ≤ ∑ n ∈ S, ‖v n * ((Real.cos (Real.pi * (n : ℝ) * t) - 1 : ℝ) : ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ S, ‖v n‖ * ((Real.pi * (n : ℝ) * t) ^ 2 / 2) := by
      apply Finset.sum_le_sum
      intro n _
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (cos_defect _) (norm_nonneg _)
    _ = _ := by
      rw [Finset.sum_mul, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro n _
      ring

/-- Exact fifth-order envelopes for both the complete edge mass and the
cross-edge pairing. Coefficients may be complex; all mixed terms remain in
the functions being integrated. Neither integrability nor a vanished trace
is supplied as a hypothesis. -/
theorem even_stencil_edge_fifth_order (S : Finset ℤ) (v : ℤ → ℂ)
    (h : ℝ) (hh : 0 ≤ h) :
    let K := ∑ n ∈ S, ‖v n‖ * (Real.pi * (n : ℝ)) ^ 2
    IntervalIntegrable (fun t => ‖evenStencilEdge S v t‖ ^ 2) volume 0 h ∧
    (∫ t : ℝ in 0..h, ‖evenStencilEdge S v t‖ ^ 2) ≤ K ^ 2 * h ^ 5 / 20 ∧
    ‖∫ t : ℝ in 0..h, conj (evenStencilEdge S v t) * evenStencilEdge S v (h - t)‖ ≤
      K ^ 2 * h ^ 5 / 120 := by
  let K := ∑ n ∈ S, ‖v n‖ * (Real.pi * (n : ℝ)) ^ 2
  have hK : 0 ≤ K := Finset.sum_nonneg (fun n _ => mul_nonneg (norm_nonneg _) (sq_nonneg _))
  have hc : Continuous (evenStencilEdge S v) := by unfold evenStencilEdge; fun_prop
  have hn : Continuous (fun t => ‖evenStencilEdge S v t‖ ^ 2) := by fun_prop
  have hp : Continuous (fun t => conj (evenStencilEdge S v t) * evenStencilEdge S v (h - t)) := by fun_prop
  change _ ∧ _ ≤ K ^ 2 * h ^ 5 / 20 ∧ _ ≤ K ^ 2 * h ^ 5 / 120
  refine ⟨hn.intervalIntegrable _ _, ?_, ?_⟩
  · calc
      _ ≤ ∫ t : ℝ in 0..h, (K ^ 2 / 4) * t ^ 4 := by
        apply intervalIntegral.integral_mono_on hh (hn.intervalIntegrable _ _)
          ((by fun_prop : Continuous (fun t : ℝ => (K ^ 2 / 4) * t ^ 4)).intervalIntegrable _ _)
        intro t _
        have ht : ‖evenStencilEdge S v t‖ ≤ K * t ^ 2 / 2 := edge_norm S v t
        calc
          _ ≤ (K * t ^ 2 / 2) ^ 2 :=
            (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr ht
          _ = _ := by ring
      _ = _ := by rw [intervalIntegral.integral_const_mul]; norm_num [integral_pow]; ring
  · calc
      _ ≤ ∫ t : ℝ in 0..h, ‖conj (evenStencilEdge S v t) * evenStencilEdge S v (h - t)‖ :=
        intervalIntegral.norm_integral_le_integral_norm hh
      _ ≤ ∫ t : ℝ in 0..h, (K ^ 2 / 4) * (t ^ 2 * (h - t) ^ 2) := by
        apply intervalIntegral.integral_mono_on hh (hp.norm.intervalIntegrable _ _)
          ((by fun_prop : Continuous (fun t : ℝ => (K ^ 2 / 4) * (t ^ 2 * (h - t) ^ 2))).intervalIntegrable _ _)
        intro t _
        rw [norm_mul, Complex.norm_conj]
        calc
          _ ≤ (K * t ^ 2 / 2) * (K * (h - t) ^ 2 / 2) :=
            mul_le_mul (edge_norm S v t) (edge_norm S v (h - t)) (norm_nonneg _) (by positivity)
          _ = _ := by ring
      _ = _ := by rw [intervalIntegral.integral_const_mul, square_overlap_integral]; ring

#print axioms cosine_prime_edge_remainder
#print axioms even_stencil_edge_fifth_order

end D5.S3.Weil.ZetaBridge.WeilPrimeActivationEdge
