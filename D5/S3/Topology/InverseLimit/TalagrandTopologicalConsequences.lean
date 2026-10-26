/- GID: D5/S3/Topology/InverseLimit/TalagrandTopologicalConsequences
   generality: G
   mirror-B: D5/B/S3/Topology/InverseLimit/TalagrandTopologicalConsequences
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Evaluation transfers whole signed dual-ball exclusion to the same point space. -/

import D5.S3.Topology.Measures.SignedBallReduction
import Mathlib.Topology.Category.Profinite.Basic

/-!
# Point-space consequences of signed dual-ball exclusion

Evaluation embeds a profinite space continuously into the weak-star closed
unit ball of its real continuous dual. Thus exclusion of continuous injections
of beta-N from that whole ball implies the same exclusion for the point space.
The dual-ball exclusion remains a hypothesis; no CH construction is asserted.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Function

namespace D5.S3.Topology.InverseLimit.TalagrandTopologicalConsequences

universe u

private def evaluation (K : Profinite.{u}) (x : K) : WeakDual ℝ C(K, ℝ) :=
  StrongDual.toWeakDual (ContinuousMap.evalCLM (R := ℝ) x)

private theorem continuous_evaluation (K : Profinite.{u}) :
    Continuous (evaluation K) := by
  apply WeakDual.continuous_of_continuous_eval
  intro g
  exact g.continuous

private theorem norm_evaluation_le_one (K : Profinite.{u}) (x : K) :
    ‖WeakDual.toStrongDual (evaluation K x)‖ ≤ 1 := by
  change ‖ContinuousMap.evalCLM (R := ℝ) x‖ ≤ 1
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro g
  simpa only [ContinuousMap.evalCLM_apply, one_mul] using g.norm_coe_le_norm x

private theorem evaluation_injective (K : Profinite.{u}) :
    Injective (evaluation K) := by
  classical
  intro x y hxy
  by_contra hne
  obtain ⟨U, hU, hx, hy⟩ := exists_isClopen_of_totally_separated hne
  let g : C(K, ℝ) := ⟨U.indicator (fun _ => 1), hU.continuous_indicator continuous_const⟩
  have htest := congrArg (fun F : WeakDual ℝ C(K, ℝ) => F g) hxy
  change g x = g y at htest
  simpa [g, hx, hy] using htest

private theorem point_space_no_beta_of_signed_ball (K : Profinite.{u})
    (Hball : ∀ h : StoneCech ℕ → WeakDual ℝ C(K, ℝ), Continuous h →
      (∀ p, ‖WeakDual.toStrongDual (h p)‖ ≤ 1) → ¬ Injective h) :
    ∀ f : StoneCech ℕ → K, Continuous f → ¬ Injective f := by
  intro f hf hfi
  exact Hball (evaluation K ∘ f) ((continuous_evaluation K).comp hf)
    (fun p => norm_evaluation_le_one K (f p)) ((evaluation_injective K).comp hfi)

end D5.S3.Topology.InverseLimit.TalagrandTopologicalConsequences
