/- GID: D5/S3/Quantum/Tomography/HolomorphicSublevelInvariance
   generality: G
   mirror-B: D5/B/S3/Quantum/Tomography/HolomorphicSublevelInvariance
   mirror-E: none(waiver:local-invariance-requires-checked-margins)
   anchors: []
   digest: An actual complex Jacobian bound gives an invariant residual-band Newton ball uniformly over any family of certified node types. -/

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Abel

/- This is the map-invariance condition missing from pole avoidance alone.
   The supplied derivative is the ACTUAL Frechet derivative; consumers bind
   it to dephased_cayley_residual_hasFDerivAt. C is fixed at each node. A
   varying C(z) would require its derivative and is not covered silently.
   No root existence, Jacobian inverse, global root count, or external PASS
   is assumed. The residual forcing is complex and norm bounded.
-/

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Tomography.HolomorphicSublevelInvariance

/-- On a complex ball, a checked derivative bound and center/forcing budget
make z-C(f(z)-e) a self-map for every allowed complex residual e. The family
index can represent arbitrary selected residuals and pruning/preconditioner
choices. A common radius is legitimate only when ALL these budgets hold.

This statement does not imply that every exclusion/split node is a Newton
self-map. Those operations retain their real set-theoretic semantics. -/
theorem complex_sublevel_newton_ball_invariant
    {n : ℕ} {Node : Type*}
    (f : Node → (Fin n → ℂ) → (Fin n → ℂ))
    (J : Node → (Fin n → ℂ) → (Fin n → ℂ) →L[ℂ] (Fin n → ℂ))
    (C : Node → (Fin n → ℂ) →L[ℂ] (Fin n → ℂ))
    (m : Node → Fin n → ℂ) (r q b kappa gamma : ℝ)
    (hr : 0 ≤ r) (hq : 0 ≤ q) (hgamma : 0 ≤ gamma)
    (hderiv : ∀ node, ∀ z ∈ Metric.closedBall (m node) r,
      HasFDerivAt (f node) (J node z) z)
    (hJac : ∀ node, ∀ z ∈ Metric.closedBall (m node) r,
      ‖ContinuousLinearMap.id ℂ (Fin n → ℂ) - (C node).comp (J node z)‖ ≤ q)
    (hcenter : ∀ node, ‖C node (f node (m node))‖ ≤ b)
    (hC : ∀ node, ‖C node‖ ≤ kappa)
    (hbudget : b + kappa * gamma + q * r ≤ r) :
    ∀ node e, ‖e‖ ≤ gamma →
      Set.MapsTo (fun z ↦ z - C node (f node z - e))
        (Metric.closedBall (m node) r) (Metric.closedBall (m node) r) := by
  intro node e he z hz
  let N : (Fin n → ℂ) → (Fin n → ℂ) := fun x ↦ x - C node (f node x)
  have hN : ∀ x ∈ Metric.closedBall (m node) r,
      HasFDerivWithinAt N
        (ContinuousLinearMap.id ℂ (Fin n → ℂ) - (C node).comp (J node x))
        (Metric.closedBall (m node) r) x := by
    intro x hx
    exact ((hasFDerivAt_id x).sub
      ((C node).hasFDerivAt.comp x (hderiv node x hx))).hasFDerivWithinAt
  have hm : m node ∈ Metric.closedBall (m node) r := by
    simpa only [Metric.mem_closedBall, dist_self] using hr
  have hmv := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
    hN (hJac node) (convex_closedBall (m node) r) hm hz
  have hdist : ‖z - m node‖ ≤ r := by
    simpa only [Metric.mem_closedBall, dist_eq_norm] using hz
  have hmove : ‖N z - N (m node)‖ ≤ q * r :=
    hmv.trans (mul_le_mul_of_nonneg_left hdist hq)
  have hforce : ‖C node e‖ ≤ kappa * gamma := by
    calc
      ‖C node e‖ ≤ ‖C node‖ * ‖e‖ := (C node).le_opNorm e
      _ ≤ ‖C node‖ * gamma := mul_le_mul_of_nonneg_left he (norm_nonneg _)
      _ ≤ kappa * gamma := mul_le_mul_of_nonneg_right (hC node) hgamma
  have hsplit :
      z - C node (f node z - e) - m node =
        (N z - N (m node)) - C node (f node (m node)) + C node e := by
    dsimp [N]
    rw [map_sub]
    abel
  have hfinal : ‖z - C node (f node z - e) - m node‖ ≤ r := by
    rw [hsplit]
    calc
      ‖(N z - N (m node)) - C node (f node (m node)) + C node e‖ ≤
          ‖N z - N (m node)‖ + ‖C node (f node (m node))‖ + ‖C node e‖ := by
        have hadd := norm_add_le
          ((N z - N (m node)) - C node (f node (m node))) (C node e)
        have hsub := norm_sub_le (N z - N (m node)) (C node (f node (m node)))
        linarith
      _ ≤ q * r + b + kappa * gamma := by
        linarith [hmove, hcenter node, hforce]
      _ ≤ r := by linarith
  simpa only [Metric.mem_closedBall, dist_eq_norm] using hfinal

#print axioms complex_sublevel_newton_ball_invariant

end D5.S3.Quantum.Tomography.HolomorphicSublevelInvariance
