/- GID: D5/S3/Topology/InverseLimit/TalagrandTopologicalConsequences
   generality: G
   mirror-B: D5/B/S3/Topology/InverseLimit/TalagrandTopologicalConsequences
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Evaluation transfers whole signed dual-ball exclusion to the same point space. -/

import D5.S3.Topology.Measures.SignedBallReduction
import D5.S3.Topology.InverseLimit.SignedOrdinalRealization
import Mathlib.Topology.Category.Profinite.Basic
import Mathlib.Topology.Metrizable.Basic
import Mathlib.Topology.Sequences

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
  have hy' : y ∉ U := hy
  let g : C(K, ℝ) := ⟨U.indicator (fun _ => 1), hU.continuous_indicator continuous_const⟩
  have htest := congrArg (fun F : WeakDual ℝ C(K, ℝ) => F g) hxy
  change g x = g y at htest
  simpa [g, hx, hy'] using htest

private theorem point_space_no_beta_of_signed_ball (K : Profinite.{u})
    (Hball : ∀ h : StoneCech ℕ → WeakDual ℝ C(K, ℝ), Continuous h →
      (∀ p, ‖WeakDual.toStrongDual (h p)‖ ≤ 1) → ¬ Injective h) :
    ∀ f : StoneCech ℕ → K, Continuous f → ¬ Injective f := by
  intro f hf hfi
  exact Hball (evaluation K ∘ f) ((continuous_evaluation K).comp hf)
    (fun p => norm_evaluation_le_one K (f p)) ((evaluation_injective K).comp hfi)

open Filter _root_.Topology _root_.TopologicalSpace

universe v

private theorem point_space_size_of_surjection_no_sequences (K : Profinite.{u})
    {X : Type v} [Infinite X] (f : K → X) (hf : Surjective f)
    (hseq : ∀ (x : ℕ → K) (p : K), Tendsto x atTop (𝓝 p) →
      ∀ᶠ n in atTop, x n = p) :
    Infinite K ∧ ¬ FirstCountableTopology K ∧ ¬ MetrizableSpace K := by
  letI : Infinite K := Infinite.of_surjective f hf
  have hnot : ¬ FirstCountableTopology K := by
    intro hfc
    letI : FirstCountableTopology K := hfc
    let e : ℕ ↪ K := Infinite.natEmbedding K
    obtain ⟨p, phi, hphi, hconv⟩ := CompactSpace.tendsto_subseq e
    obtain ⟨N, hN⟩ := eventually_atTop.1 (hseq (e ∘ phi) p hconv)
    have heq : phi N = phi (N + 1) :=
      e.injective ((hN N le_rfl).trans (hN (N + 1) (Nat.le_succ N)).symm)
    exact (Nat.ne_of_lt (Nat.lt_succ_self N)) (hphi.injective heq)
  refine ⟨inferInstance, hnot, ?_⟩
  intro hm
  letI : MetrizableSpace K := hm
  exact hnot inferInstance

open scoped Cardinal Ordinal

private theorem actual_point_space_consequences
    (hCH : Cardinal.continuum.{0} = ℵ₁)
    (Hball : ∀ h : StoneCech ℕ →
      WeakDual ℝ C((SignedOrdinalRealization.finalPrefix hCH).cone.pt, ℝ),
      Continuous h → (∀ p, ‖WeakDual.toStrongDual (h p)‖ ≤ 1) → ¬ Injective h)
    (hseq : ∀ (x : ℕ → (SignedOrdinalRealization.finalPrefix hCH).cone.pt)
      (p : (SignedOrdinalRealization.finalPrefix hCH).cone.pt),
      Tendsto x atTop (𝓝 p) → ∀ᶠ n in atTop, x n = p) :
    (∀ f : StoneCech ℕ → (SignedOrdinalRealization.finalPrefix hCH).cone.pt,
      Continuous f → ¬ Injective f) ∧
    Infinite (SignedOrdinalRealization.finalPrefix hCH).cone.pt ∧
    ¬ FirstCountableTopology (SignedOrdinalRealization.finalPrefix hCH).cone.pt ∧
    ¬ MetrizableSpace (SignedOrdinalRealization.finalPrefix hCH).cone.pt := by
  letI : Infinite (SignedProperLimit.Coord ω) :=
    Infinite.of_injective
      (fun n : ℕ => (⟨(n : Ordinal), Ordinal.natCast_lt_omega0 n⟩ :
        SignedProperLimit.Coord ω))
      (fun _ _ h => Nat.cast_injective (congrArg Subtype.val h))
  letI : Infinite (SignedProperLimit.Cube ω) := inferInstance
  refine ⟨point_space_no_beta_of_signed_ball _ Hball, ?_⟩
  exact point_space_size_of_surjection_no_sequences _
    (fun x => SignedProperLimit.restrict Ordinal.omega0_lt_omega_one.le x.1)
    (SignedOrdinalRealization.initial_onto hCH) hseq

end D5.S3.Topology.InverseLimit.TalagrandTopologicalConsequences
