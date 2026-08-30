/- GID: D5/S3/Analytic/GoldenTomography/TwoNodeTomographyConditioning
   generality: G
   mirror-B: D5/B/S3/Analytic/GoldenTomography/TwoNodeTomographyConditioning
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Two distinct phase nodes admit exact amplitude recovery, with reconstruction error controlled by the inverse node separation. -/

import D5.S3.Analytic.GoldenTomography.FiniteVandermondeTomography

/-!
The exact kernel condition and metric conditioning are different statements.
Distinct nodes make the two-moment readout injective.  The explicit recovery
formula shows that perturbations are divided by `‖z1 - z0‖`, so near-colliding
nodes can remain exactly distinguishable while becoming numerically unstable.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Analytic.GoldenTomography.TwoNodeTomographyConditioning

/-- Zeroth and first moments of two hidden complex amplitudes. -/
def twoNodeMoments (z₀ z₁ a₀ a₁ : ℂ) : ℂ × ℂ :=
  (a₀ + a₁, z₀ * a₀ + z₁ * a₁)

/-- Reconstruct the amplitude at the first node. -/
def recoverFirst (z₀ z₁ m₀ m₁ : ℂ) : ℂ :=
  (z₁ * m₀ - m₁) / (z₁ - z₀)

/-- Reconstruct the amplitude at the second node. -/
def recoverSecond (z₀ z₁ m₀ m₁ : ℂ) : ℂ :=
  (m₁ - z₀ * m₀) / (z₁ - z₀)

/-- Two distinct nodes recover both amplitudes exactly from the first two
moments. -/
theorem recover_two_node_amplitudes
    {z₀ z₁ : ℂ} (hNodes : z₀ ≠ z₁) (a₀ a₁ : ℂ) :
    recoverFirst z₀ z₁
        (twoNodeMoments z₀ z₁ a₀ a₁).1
        (twoNodeMoments z₀ z₁ a₀ a₁).2 = a₀ ∧
      recoverSecond z₀ z₁
        (twoNodeMoments z₀ z₁ a₀ a₁).1
        (twoNodeMoments z₀ z₁ a₀ a₁).2 = a₁ := by
  have hDen : z₁ - z₀ ≠ 0 := sub_ne_zero.mpr hNodes.symm
  constructor <;>
    unfold recoverFirst recoverSecond twoNodeMoments <;>
    field_simp [hDen] <;> ring

/-- Exact first-amplitude reconstruction error under moment perturbations. -/
theorem recover_first_error
    {z₀ z₁ : ℂ} (hNodes : z₀ ≠ z₁)
    (a₀ a₁ e₀ e₁ : ℂ) :
    recoverFirst z₀ z₁
        ((twoNodeMoments z₀ z₁ a₀ a₁).1 + e₀)
        ((twoNodeMoments z₀ z₁ a₀ a₁).2 + e₁) - a₀ =
      (z₁ * e₀ - e₁) / (z₁ - z₀) := by
  have hDen : z₁ - z₀ ≠ 0 := sub_ne_zero.mpr hNodes.symm
  unfold recoverFirst twoNodeMoments
  field_simp [hDen]
  ring

/-- Exact second-amplitude reconstruction error under moment perturbations. -/
theorem recover_second_error
    {z₀ z₁ : ℂ} (hNodes : z₀ ≠ z₁)
    (a₀ a₁ e₀ e₁ : ℂ) :
    recoverSecond z₀ z₁
        ((twoNodeMoments z₀ z₁ a₀ a₁).1 + e₀)
        ((twoNodeMoments z₀ z₁ a₀ a₁).2 + e₁) - a₁ =
      (e₁ - z₀ * e₀) / (z₁ - z₀) := by
  have hDen : z₁ - z₀ ≠ 0 := sub_ne_zero.mpr hNodes.symm
  unfold recoverSecond twoNodeMoments
  field_simp [hDen]
  ring

/-- First-amplitude error is bounded by the perturbation size divided by node
separation. -/
theorem norm_recover_first_error_le
    {z₀ z₁ : ℂ} (hNodes : z₀ ≠ z₁)
    (a₀ a₁ e₀ e₁ : ℂ) :
    ‖recoverFirst z₀ z₁
        ((twoNodeMoments z₀ z₁ a₀ a₁).1 + e₀)
        ((twoNodeMoments z₀ z₁ a₀ a₁).2 + e₁) - a₀‖ ≤
      (‖z₁‖ * ‖e₀‖ + ‖e₁‖) / ‖z₁ - z₀‖ := by
  rw [recover_first_error hNodes]
  rw [norm_div]
  apply (div_le_div_iff_of_pos_right (norm_pos_iff.mpr
    (sub_ne_zero.mpr hNodes.symm))).2
  calc
    ‖z₁ * e₀ - e₁‖ ≤ ‖z₁ * e₀‖ + ‖e₁‖ := norm_sub_le _ _
    _ = ‖z₁‖ * ‖e₀‖ + ‖e₁‖ := by rw [norm_mul]

/-- A concrete pair of nodes exhibits an inhabited recovery problem. -/
example (a₀ a₁ : ℂ) :
    recoverFirst 0 1
        (twoNodeMoments 0 1 a₀ a₁).1
        (twoNodeMoments 0 1 a₀ a₁).2 = a₀ :=
  (recover_two_node_amplitudes (by norm_num) a₀ a₁).1

#print axioms recover_two_node_amplitudes
#print axioms recover_first_error
#print axioms recover_second_error
#print axioms norm_recover_first_error_le

end D5.S3.Analytic.GoldenTomography.TwoNodeTomographyConditioning
