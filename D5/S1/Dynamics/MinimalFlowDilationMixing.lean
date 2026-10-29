/- GID: D5/S1/Dynamics/MinimalFlowDilationMixing
   generality: G
   mirror-B: D5/B/S1/Dynamics/MinimalFlowDilationMixing
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Expanding covariance of a compact minimal real flow forces topological mixing. -/

import Mathlib.Dynamics.Minimal
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Analysis.SpecificLimits.Basic

/-! Compact minimality supplies uniformly bounded hitting times;
dilation shrinks them into any open source set. -/

noncomputable section

namespace D5.S1.Dynamics.MinimalFlowDilationMixing

open Set Filter
open scoped Pointwise

/-- A continuous map expanding a compact minimal real flow is topologically mixing:
every sufficiently large iterate sends some point of each nonempty open set into
each other nonempty open set. No nonemptiness assumption on the space is needed. -/
theorem minimal_real_flow_dilation_mixing
    {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [AddAction ℝ X] [ContinuousVAdd ℝ X] [AddAction.IsMinimal ℝ X]
    (a : ℝ) (ha : 1 < a) (f : X → X) (_hfcont : Continuous f)
    (hf : ∀ (t : ℝ) (x : X), f (t +ᵥ x) = (a * t) +ᵥ f x) :
    ∀ U V : Set X, IsOpen U → U.Nonempty → IsOpen V → V.Nonempty →
      ∃ N : ℕ, ∀ n ≥ N, ∃ x, x ∈ U ∧ (f^[n]) x ∈ V := by
  classical
  intro U V hU hUne hV hVne
  obtain ⟨u, hu⟩ := hUne
  have hpre : IsOpen ((fun s : ℝ => s +ᵥ u) ⁻¹' U) :=
    hU.preimage (continuous_id.vadd continuous_const)
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hpre 0 (by simpa using hu)
  obtain ⟨I, hI⟩ := isCompact_univ.exists_finite_cover_vadd (G := ℝ) hV hVne
  let M : ℝ := ∑ t ∈ I, |t|
  have hhit : ∀ z : X, ∃ t : ℝ, |t| ≤ M ∧ t +ᵥ z ∈ V := by
    intro z
    have hz := hI (Set.mem_univ z)
    simp only [Set.mem_iUnion] at hz
    obtain ⟨s, hs, v, hv, hvz⟩ := hz
    refine ⟨-s, ?_, ?_⟩
    · simpa only [abs_neg] using
        (Finset.single_le_sum (fun t _ => abs_nonneg t) hs : |s| ≤ M)
    · rw [← hvz, neg_vadd_vadd]
      exact hv
  have hcov : ∀ (n : ℕ) (s : ℝ) (x : X),
      (f^[n]) (s +ᵥ x) = (a ^ n * s) +ᵥ (f^[n]) x := by
    intro n
    induction n with
    | zero => intro s x; simp
    | succ n ih =>
      intro s x
      rw [Function.iterate_succ_apply', ih, hf, Function.iterate_succ_apply']
      congr 1
      rw [pow_succ]
      ring
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
    ((tendsto_pow_atTop_atTop_of_one_lt ha).eventually
      (Filter.eventually_gt_atTop (M / ε)))
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨t, ht, htv⟩ := hhit ((f^[n]) u)
  have hp : 0 < a ^ n := pow_pos (lt_trans zero_lt_one ha) n
  have hsmall : |t / a ^ n| < ε := by
    rw [abs_div, abs_of_pos hp, div_lt_iff₀ hp]
    have hlarge := (div_lt_iff₀ hε).mp (hN n hn)
    nlinarith
  refine ⟨(t / a ^ n) +ᵥ u, hball ?_, ?_⟩
  · simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using hsmall
  · rw [hcov, mul_div_cancel₀ _ hp.ne']
    exact htv

#print axioms minimal_real_flow_dilation_mixing

end D5.S1.Dynamics.MinimalFlowDilationMixing
