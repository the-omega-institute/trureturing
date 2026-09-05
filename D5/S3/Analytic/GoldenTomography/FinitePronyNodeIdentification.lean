/- GID: D5/S3/Analytic/GoldenTomography/FinitePronyNodeIdentification
   generality: G
   mirror-B: D5/B/S3/Analytic/GoldenTomography/FinitePronyNodeIdentification
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A polynomial recurrence valid on a full finite Prony window must vanish at every separated mode with nonzero weight. -/

import D5.S3.Analytic.GoldenTomography.FinitePronyHankelReconstruction

/-!
# Finite Prony node identification

The forward Prony theorem says that the node-annihilator polynomial generates a
linear recurrence for the moment sequence. This module proves the finite
converse needed for unknown-node recovery. If a candidate polynomial generates
that recurrence on the first `m` shifts of an `m`-mode sequence, then the
candidate vanishes at every true node, provided the nodes are distinct and all
mode weights are nonzero.

The theorem identifies the spectral support carried by a recurrence. It does
not yet choose recurrence coefficients algorithmically or prove a noisy root
perturbation bound.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped BigOperators

namespace D5.S3.Analytic.GoldenTomography.FinitePronyNodeIdentification

open Polynomial
open D5.S3.Analytic.GoldenTomography.FinitePronyHankelReconstruction

universe u

variable {K : Type u} [Field K]

/-- A polynomial recurrence that holds on a full matching observation window
must vanish at every true Prony node. -/
theorem recurrence_window_identifies_node_roots {m : ℕ}
    {nodes weights : Fin m → K} (candidate : K[X])
    (hNodes : Function.Injective nodes)
    (hWeights : ∀ mode, weights mode ≠ 0)
    (hRecurrence : ∀ time : Fin m,
      ∑ degree ∈ candidate.support,
          candidate.coeff degree *
            pronyMoment nodes weights ((time : ℕ) + degree) = 0) :
    ∀ mode, candidate.eval (nodes mode) = 0 := by
  classical
  let residualWeights : Fin m → K :=
    fun mode => weights mode * candidate.eval (nodes mode)
  have hMomentZero (time : Fin m) :
      pronyMoment nodes residualWeights (time : ℕ) = 0 := by
    change
      (∑ mode,
        (weights mode * candidate.eval (nodes mode)) *
          nodes mode ^ (time : ℕ)) = 0
    calc
      (∑ mode,
          (weights mode * candidate.eval (nodes mode)) *
            nodes mode ^ (time : ℕ)) =
          ∑ mode,
            weights mode * nodes mode ^ (time : ℕ) *
              (∑ degree ∈ candidate.support,
                candidate.coeff degree * nodes mode ^ degree) := by
        apply Finset.sum_congr rfl
        intro mode _
        rw [eval_eq_sum, Polynomial.sum_def]
        ring
      _ = ∑ mode, ∑ degree ∈ candidate.support,
            candidate.coeff degree *
              (weights mode *
                nodes mode ^ ((time : ℕ) + degree)) := by
        apply Finset.sum_congr rfl
        intro mode _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro degree _
        rw [pow_add]
        ring
      _ = ∑ degree ∈ candidate.support, ∑ mode,
            candidate.coeff degree *
              (weights mode *
                nodes mode ^ ((time : ℕ) + degree)) := by
        rw [Finset.sum_comm]
      _ = ∑ degree ∈ candidate.support,
            candidate.coeff degree *
              pronyMoment nodes weights ((time : ℕ) + degree) := by
        apply Finset.sum_congr rfl
        intro degree _
        unfold pronyMoment
        rw [Finset.mul_sum]
      _ = 0 := hRecurrence time
  have hResidualZero : residualWeights = fun _ => 0 := by
    apply (first_prony_moments_injective hNodes)
    funext time
    simpa [firstPronyMoments, pronyMoment] using hMomentZero time
  intro mode
  have hProduct : weights mode * candidate.eval (nodes mode) = 0 := by
    simpa [residualWeights] using congrFun hResidualZero mode
  exact (mul_eq_zero.mp hProduct).resolve_left (hWeights mode)

/-- The genuine node-annihilator supplies a nonvacuous recurrence window to
which the converse theorem applies. -/
theorem prony_annihilator_recurrence_window {m : ℕ}
    (nodes weights : Fin m → K) :
    ∀ time : Fin m,
      ∑ degree ∈ (pronyAnnihilator nodes).support,
          (pronyAnnihilator nodes).coeff degree *
            pronyMoment nodes weights ((time : ℕ) + degree) = 0 := by
  intro time
  exact prony_moment_linear_recurrence nodes weights time

/-- Exact finite unknown-node identification consists of a satisfiable
recurrence window and the converse recovery of all true roots. -/
theorem finite_prony_node_identification {m : ℕ}
    {nodes weights : Fin m → K} (candidate : K[X])
    (hNodes : Function.Injective nodes)
    (hWeights : ∀ mode, weights mode ≠ 0)
    (hRecurrence : ∀ time : Fin m,
      ∑ degree ∈ candidate.support,
          candidate.coeff degree *
            pronyMoment nodes weights ((time : ℕ) + degree) = 0) :
    (∀ mode, candidate.eval (nodes mode) = 0) ∧
    (∀ time : Fin m,
      ∑ degree ∈ (pronyAnnihilator nodes).support,
          (pronyAnnihilator nodes).coeff degree *
            pronyMoment nodes weights ((time : ℕ) + degree) = 0) :=
  ⟨recurrence_window_identifies_node_roots candidate hNodes hWeights hRecurrence,
    prony_annihilator_recurrence_window nodes weights⟩

#print axioms recurrence_window_identifies_node_roots
#print axioms prony_annihilator_recurrence_window
#print axioms finite_prony_node_identification

end D5.S3.Analytic.GoldenTomography.FinitePronyNodeIdentification
