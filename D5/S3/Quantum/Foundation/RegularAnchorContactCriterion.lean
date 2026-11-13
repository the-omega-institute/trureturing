/- GID: D5/S3/Quantum/Foundation/RegularAnchorContactCriterion
   generality: G
   mirror-B: D5/B/S3/Quantum/Foundation/RegularAnchorContactCriterion
   mirror-E: none(waiver:registration-template-not-established)
   anchors: []
   utility: none
   digest: Original regular anchors satisfy the complete width minimum and shell contact criterion. -/

import D5.S3.Quantum.Foundation.RegularAnchorShell
import Mathlib.Analysis.Normed.Module.Ball.Pointwise

noncomputable section
open Set
open scoped Pointwise

namespace D5.S3.Quantum.Foundation.RegularAnchorContactCriterion

open CircuitBalancedConfirmation FacetZeroGluing OrthogonalJointCompletion
open RegularAnchorNormalChart RegularAnchorWidthAntipode RegularAnchorShell

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] {C : PointedCone ℝ V} {u : V →ₗ[ℝ] ℝ}

/-- The complete contact and strict-scale conclusion for the same actual coordinates. -/
def ContactCriterion {p : pure C u} {e : V →ₗ[ℝ] ℝ} {a : FullBall3Chart C u p}
    (n : NativeChart C u p e a) : Prop :=
  (width a = 1 ↔ minimum n = 1) ∧
  (minimum n = 1 ↔
    (Metric.closedBall (0 : ThreeSpace) 1 ∩ frontier (shell n)).Nonempty) ∧
  (1 < minimum n →
    minimum n • Metric.closedBall (0 : ThreeSpace) 1 ⊆ shell n ∧
    Metric.closedBall (0 : ThreeSpace) 1 ⊆ interior (shell n) ∧
    minimum n - 1 ≤ boundaryDistance n ∧ 0 < minimum n - 1)

/-- The full original cone/base/effect telescope derives its own normal chart and
all three equivalent contact conditions, with the entire strict-scale conclusion. -/
theorem regular_anchor_contact_criterion
    (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (h3 : EB3 C u)
    (hinj : Function.Injective (fun p : pure C u => exclusion C u p))
    (p : pure C u) (e : V →ₗ[ℝ] ℝ) (he : common C u p e)
    (hreg : Regular C u p) (a : FullBall3Chart C u p) :
    ∃ n : NativeChart C u p e a, ContactCriterion n := by
  obtain ⟨n⟩ := regular_anchor_native hc hs hg h3 hinj p e he hreg a
  have hm : (∃ v : ThreeSpace, ‖v‖ = 1 ∧ rho n v = 1) ↔ minimum n = 1 := by
    obtain ⟨w,hw,hr,hl,hmin⟩ := minimum_attained n
    constructor
    · rintro ⟨v,hv,hvone⟩
      exact le_antisymm ((hmin v hv).trans_eq hvone) hl
    · intro h
      exact ⟨w,hw,hr.trans h⟩
  refine ⟨n,(width_one_iff_rho_one hc hs hg h3 n).trans hm,
    minimum_one_iff_contact n,?_⟩
  intro hδ
  have hnonneg : 0 ≤ minimum n := le_trans zero_le_one hδ.le
  have hscale : minimum n • Metric.closedBall (0 : ThreeSpace) 1 =
      Metric.closedBall (0 : ThreeSpace) (minimum n) := by
    rw [smul_unitClosedBall, Real.norm_eq_abs, abs_of_nonneg hnonneg]
  refine ⟨?_,(strict_margin n hδ).1,(strict_boundary_distance n hδ).1,
    (strict_boundary_distance n hδ).2⟩
  rw [hscale]
  exact minimum_ball_subset n

end D5.S3.Quantum.Foundation.RegularAnchorContactCriterion
