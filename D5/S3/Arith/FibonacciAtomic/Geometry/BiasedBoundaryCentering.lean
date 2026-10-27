/- GID: D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryCentering
   generality: I
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryCentering
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Analysis.InnerProductSpace.Projection.Basic]
   utility: none
   digest: Actual mean centering and the all-vector conditional centered suffix residual. -/

import D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryPathSplit
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-! Centering the actual boundary trace before and after conditional restriction. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryCentering

open ActualTreeReadoutAcquisition (Address)
open FiniteSourceHardy (H P Edge)
open FiniteSourceMass (a)
open BiasedBoundaryTrace (Omega M G J)
open BiasedBoundaryConditionalLaw (pullback conditional_pullback_law)
open BiasedBoundaryPathSplit (constG S prefixSum boundary_path_split)
open MeasureTheory Filter
open scoped ENNReal

/-- The mean functional on the original boundary L2(M). -/
def mean : G →L[ℝ] ℝ := innerSL ℝ (constG 1)

/-- Orthogonal projection onto the orthogonal complement of the actual constants. -/
def Pi : G →L[ℝ] G := (ℝ ∙ constG 1)ᗮ.starProjection

/-- The actual centered trace, included in the original ambient G. -/
def C : H →L[ℝ] G := Pi.comp J

private theorem constG_norm_one : ‖constG 1‖ = 1 := by
  change ‖(1:ℝ) • Lp.const 2 M (1:ℝ)‖ = 1
  simp [Lp.norm_const (by norm_num : (2:ℝ≥0∞) ≠ 0)]

private theorem constG_eq_smul (c : ℝ) : constG c = c • constG 1 := by
  simp [BiasedBoundaryPathSplit.constG]

private theorem mean_const (c : ℝ) : mean (constG c) = c := by
  change inner ℝ (constG 1) (constG c) = c
  rw [constG_eq_smul, inner_smul_right, real_inner_self_eq_norm_sq, constG_norm_one]
  simp

private theorem mean_integral (F : G) : mean F = ∫ ω, F ω ∂M := by
  change inner ℝ (constG 1) F = _
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [boundary_path_split.2.2.2.1 (1:ℝ)] with ω hω
  change (constG 1 ω) * F ω = F ω
  rw [hω, one_mul]

private theorem Pi_formula (F : G) : Pi F = F-constG (mean F) := by
  rw [Pi, Submodule.starProjection_orthogonal_val,
    Submodule.starProjection_unit_singleton ℝ constG_norm_one,
    constG_eq_smul (mean F)]
  rfl

private theorem Pi_const (c : ℝ) : Pi (constG c) = 0 := by
  rw [Pi_formula, mean_const, sub_self]

private theorem pullback_const (p : Address) (c : ℝ) : pullback p (constG c) = constG c := by
  apply Lp.ext
  have hc := boundary_path_split.2.2.2.1 c
  have ht : (constG c : Omega → ℝ) =ᵐ[BiasedBoundaryConditionalLaw.conditional p]
      (fun _ : Omega => c) := Measure.ae_smul_measure (ae_restrict_of_ae hc) _
  have hp := (conditional_pullback_law.2.2.1 p).quasiMeasurePreserving.ae_eq_comp ht
  filter_upwards [conditional_pullback_law.2.2.2.2.1 p (constG c), hp, hc] with ω h1 h2 h3
  exact h1.trans (h2.trans h3.symm)

private theorem centered_pullback (p : Address) (z : H) :
    Pi (pullback p (C z)) = C (S p z) := by
  change Pi (pullback p (Pi (J z))) = Pi (J (S p z))
  rw [Pi_formula (J z), map_sub, pullback_const, map_sub, Pi_const, sub_zero,
    boundary_path_split.2.2.2.2, map_add, Pi_const, zero_add]

private theorem J_norm_sq (z : H) : ‖J z‖^2 ≤ Real.goldenRatio*‖z‖^2 := by
  have hz : P 0 z = 0 := by
    ext u
    have hu : 0 < u.val.length := List.length_pos_of_ne_nil u.property
    change (if u.val.length ≤ 0 then z u else 0) = 0
    simp [Nat.not_le.mpr hu]
  have hb := BiasedBoundaryTrace.boundary_trace_hardy.2 0 z
  have he : a/(1-a) = Real.goldenRatio := by
    have hp : Real.goldenRatio ≠ 0 := Real.goldenRatio_pos.ne'
    have hp1 : Real.goldenRatio-1 ≠ 0 := (sub_pos.mpr Real.one_lt_goldenRatio).ne'
    change Real.goldenRatio⁻¹/(1-Real.goldenRatio⁻¹) = Real.goldenRatio
    field_simp
    nlinarith [Real.goldenRatio_sq]
  simpa [hz, he] using hb

/-- Actual integral centering cancels the prefix and global constants for every
original increment vector. The centered suffix obeys the original Hardy bound. -/
theorem centered_suffix_residual :
    (∀ F : G, mean F = ∫ ω, F ω ∂M) ∧
    (∀ c : ℝ, mean (constG c) = c) ∧
    (∀ F : G, Pi F = F-constG (mean F)) ∧
    (∀ F : G, ‖Pi F‖ ≤ ‖F‖) ∧
    (∀ (p : Address) (z : H), Pi (pullback p (C z)) = C (S p z)) ∧
    (∀ (p : Address) (z : H),
      ‖Pi (pullback p (C z))‖^2 ≤ Real.goldenRatio*‖S p z‖^2) := by
  refine ⟨mean_integral, mean_const, Pi_formula,
    (fun F => Submodule.norm_starProjection_apply_le _ F), centered_pullback, ?_⟩
  intro p z
  rw [centered_pullback]
  exact (pow_le_pow_left₀ (norm_nonneg _) (Submodule.norm_starProjection_apply_le
    (ℝ ∙ constG 1)ᗮ (J (S p z))) 2).trans (J_norm_sq (S p z))

end D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryCentering
