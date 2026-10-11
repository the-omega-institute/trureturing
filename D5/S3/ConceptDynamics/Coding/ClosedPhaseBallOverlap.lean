/- GID: D5/S3/ConceptDynamics/Coding/ClosedPhaseBallOverlap
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Coding/ClosedPhaseBallOverlap
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Closed circular phase balls meet precisely at the doubled-radius distance bound. -/

import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.Tactic
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.ConceptDynamics.Coding.ClosedPhaseBallOverlap

/-- The midpoint of a shortest lifted arc realizes every closed-boundary overlap. -/
theorem closed_phase_ball_overlap (P : Nat) (ε : ℝ) (x y : AddCircle (P : ℝ)) :
    (∃ q : AddCircle (P : ℝ), dist q x ≤ ε ∧ dist q y ≤ ε) ↔ dist x y ≤ 2 * ε := by
  constructor
  · rintro ⟨q, hx, hy⟩
    have triangle := dist_triangle x q y
    rw [dist_comm x q] at triangle
    linarith
  · intro close
    obtain ⟨x⟩ := x
    obtain ⟨y⟩ := y
    change dist (x : AddCircle (P : ℝ)) (y : AddCircle (P : ℝ)) ≤ 2 * ε at close
    let k : ℤ := round ((P : ℝ)⁻¹ * (x - y))
    let lifted : ℝ := x - (k : ℝ) * P
    let midpoint : ℝ := (lifted + y) / 2
    have residual : |x - y - (k : ℝ) * P| ≤ 2 * ε := by
      simpa only [dist_eq_norm, ← QuotientAddGroup.mk_sub, AddCircle.norm_eq, k] using close
    have first : |midpoint - lifted| ≤ ε := by
      dsimp [midpoint, lifted]
      have h := abs_le.mp residual
      apply abs_le.mpr
      constructor <;> linarith
    have second : |midpoint - y| ≤ ε := by
      dsimp [midpoint, lifted]
      have h := abs_le.mp residual
      apply abs_le.mpr
      constructor <;> linarith
    refine ⟨(midpoint : AddCircle (P : ℝ)), ?_, ?_⟩
    · have member : midpoint ∈ ((↑) : ℝ → AddCircle (P : ℝ)) ⁻¹'
          Metric.closedBall (x : AddCircle (P : ℝ)) ε := by
        rw [AddCircle.coe_real_preimage_closedBall_eq_iUnion]
        simp only [Set.mem_iUnion, Metric.mem_closedBall, Real.dist_eq]
        refine ⟨-k, ?_⟩
        simpa [lifted, zsmul_eq_mul, sub_eq_add_neg] using first
      exact member
    · have bound : ‖((midpoint - y : ℝ) : AddCircle (P : ℝ))‖ ≤ |midpoint - y| :=
        QuotientAddGroup.norm_mk_le_norm
      calc
        dist (midpoint : AddCircle (P : ℝ)) (y : AddCircle (P : ℝ)) =
            ‖((midpoint - y : ℝ) : AddCircle (P : ℝ))‖ := by
              rw [dist_eq_norm, ← QuotientAddGroup.mk_sub]
        _ ≤ ε := bound.trans second

end D5.S3.ConceptDynamics.Coding.ClosedPhaseBallOverlap
