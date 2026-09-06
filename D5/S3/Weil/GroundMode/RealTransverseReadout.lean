/- GID: D5/S3/Weil/GroundMode/RealTransverseReadout
   generality: G
   mirror-B: D5/B/S3/Weil/GroundMode/RealTransverseReadout
   mirror-E: none(waiver:continuous-kernel-real-L2-certificate)
   anchors: []
   digest: Realize continuous real kernels in the actual L2 space and transport a uniform transverse margin to nonvanishing for every real error in a norm ball. -/

import D5.S3.Weil.GroundMode.RealReadoutCancellation
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Real L2 kernels and a transverse certificate

The first statements identify actual continuous kernels with their L2 Riesz
vectors; their norm and mixed inner product are integrals, not oracle input.
The final statement transports a lower bound on a desingularized imaginary
readout and an independently bounded Riesz norm to every vector in the real
error ball. Its application uses the kernel
  -sin(x*t) * sinh(y*t)/y,
continuously extended to -t*sin(x*t) at y=0. The finite interval consumer
proves its candidate floor over full boxes, not merely sampled points.

The general L2 kernel realization here is proved. Its specialization to the
existing arithmetic Weil form-domain, and the elementary Fourier/kernel
identification with the interval consumer, remain separate analytic steps.
No determinant-positive premise is needed for the one-channel sign test.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.Weil.GroundMode.RealTransverseReadout

open MeasureTheory
open scoped InnerProductSpace

section ContinuousKernels

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X]
variable (mu : Measure X) [IsFiniteMeasure mu]

/-- The real L2 Riesz vector of an actual continuous kernel. -/
def kernelVector (g : C(X, ℝ)) : Lp ℝ 2 mu :=
  ContinuousMap.toLp (p := 2) (μ := mu) (𝕜 := ℝ) g

/-- Kernel evaluation is the actual integral against the L2 vector. -/
theorem kernelVector_inner (g : C(X, ℝ)) (f : Lp ℝ 2 mu) :
    ⟪kernelVector mu g, f⟫_ℝ = ∫ x, g x * f x ∂mu := by
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  have hg := ContinuousMap.coeFn_toLp (p := 2) (μ := mu) (𝕜 := ℝ) g
  filter_upwards [hg] with x hx
  simp only [kernelVector] at ⊢
  simp [RCLike.inner_apply, hx, mul_comm]

/-- The mixed kernel Gram is the full integral, with no coefficient cutoff. -/
theorem kernelVector_gram (g h : C(X, ℝ)) :
    ⟪kernelVector mu g, kernelVector mu h⟫_ℝ = ∫ x, g x * h x ∂mu := by
  rw [kernelVector_inner]
  apply integral_congr_ae
  have hh := ContinuousMap.coeFn_toLp (p := 2) (μ := mu) (𝕜 := ℝ) h
  filter_upwards [hh] with x hx
  simp only [kernelVector, hx]

/-- The squared Riesz norm equals the integral of the actual squared kernel. -/
theorem kernelVector_norm_sq (g : C(X, ℝ)) :
    ‖kernelVector mu g‖ ^ 2 = ∫ x, (g x) ^ 2 ∂mu := by
  rw [← real_inner_self_eq_norm_sq, kernelVector_gram]
  simp only [pow_two]

end ContinuousKernels

section Margin

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- A real readout with a certified candidate floor remains positive under
all errors in the ball. All quantities refer to the same Riesz vector. -/
theorem real_readout_lower (h k w : H) (radius K floor : ℝ)
    (hK : 0 ≤ K) (hradius : ‖w‖ ≤ radius) (hh : ‖h‖ ≤ K)
    (hk : floor ≤ ⟪h, k⟫_ℝ) :
    floor - K * radius ≤ ⟪h, k + w⟫_ℝ := by
  have hbound : |⟪h, w⟫_ℝ| ≤ K * radius := by
    calc
      _ ≤ ‖h‖ * ‖w‖ := abs_real_inner_le_norm _ _
      _ ≤ K * radius := mul_le_mul hh hradius (norm_nonneg w) hK
  have hlo := (abs_le.mp hbound).1
  rw [inner_add_right]
  linarith

/-- A nonzero ordinate can be factored from the imaginary part without
losing a uniform lower bound as it tends to zero. The conclusion concerns
every point in the declared region, not a finite collection of point tests. -/
theorem transverse_region_nonvanishing
    (readout : ℝ → ℝ → H → ℂ) (kernel : ℝ → ℝ → H)
    (region : Set (ℝ × ℝ)) (k w : H) (radius K floor : ℝ)
    (hK : 0 ≤ K) (hradius : ‖w‖ ≤ radius)
    (hkernel : ∀ p ∈ region, ‖kernel p.1 p.2‖ ≤ K)
    (hfloor : ∀ p ∈ region, floor ≤ ⟪kernel p.1 p.2, k⟫_ℝ)
    (hidentity : ∀ p ∈ region,
      (readout p.1 p.2 (k + w)).im = p.2 * ⟪kernel p.1 p.2, k + w⟫_ℝ)
    (hmargin : 0 < floor - K * radius) :
    ∀ p ∈ region, p.2 ≠ 0 →
      |p.2| * (floor - K * radius) ≤ |(readout p.1 p.2 (k + w)).im| ∧
      readout p.1 p.2 (k + w) ≠ 0 := by
  intro p hp hy
  have hl := real_readout_lower (kernel p.1 p.2) k w radius K floor hK hradius
    (hkernel p hp) (hfloor p hp)
  have hpos : 0 < ⟪kernel p.1 p.2, k + w⟫_ℝ := lt_of_lt_of_le hmargin hl
  have hb : |p.2| * (floor - K * radius) ≤
      |(readout p.1 p.2 (k + w)).im| := by
    rw [hidentity p hp, abs_mul, abs_of_pos hpos]
    exact mul_le_mul_of_nonneg_left hl (abs_nonneg _)
  refine ⟨hb, ?_⟩
  intro hz
  have hi := congrArg Complex.im hz
  rw [hidentity p hp] at hi
  have hm : p.2 * ⟪kernel p.1 p.2, k + w⟫_ℝ ≠ 0 :=
    mul_ne_zero hy (ne_of_gt hpos)
  exact hm hi

end Margin

#print axioms kernelVector_inner
#print axioms kernelVector_gram
#print axioms kernelVector_norm_sq
#print axioms real_readout_lower
#print axioms transverse_region_nonvanishing

end D5.S3.Weil.GroundMode.RealTransverseReadout
end
