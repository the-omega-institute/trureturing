/- GID: D5/S3/Analytic/GoldenTomography/FinitePronyAnnihilatorIdentification
   generality: G
   mirror-B: D5/B/S3/Analytic/GoldenTomography/FinitePronyAnnihilatorIdentification
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A recurrence valid on a full separated Prony window contains every true node, has degree at least the active mode count, and uniquely identifies the bounded monic annihilator. -/

import D5.S3.Analytic.GoldenTomography.FinitePronyAnnihilatorRecurrence
import D5.S3.Analytic.GoldenTomography.FiniteVandermondeTomography
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.RingTheory.Coprime.Lemmas

/-!
# Finite Prony annihilator identification and minimality

The forward theorem supplies a degree-`m` recurrence from the true node
annihilator. This module proves the finite converse. If a candidate polynomial
annihilates the first `m` shifted recurrence equations of an `m`-mode Prony
sequence, then every true node is a root, provided the nodes are distinct and
their weights are nonzero.

Consequently the true annihilator divides every nonzero valid candidate. No
valid recurrence polynomial can have degree below the active mode count. A
monic candidate of degree at most `m` is therefore uniquely equal to the true
annihilator.

This is structural identifiability. It does not solve the recurrence
coefficients numerically or prove stability of roots under noisy moments.
-/

/- Library-search audit trail (2026-09-03):
   * Current-tree searches for recurrence-window node identification, Prony
     annihilator uniqueness, and minimal recurrence degree found no declaration
     on `dev`.
   * The branch already owns the forward recurrence and exact Vandermonde
     injectivity. This module composes those owners rather than adding a second
     moment or reconstruction API.
   * Pinned Mathlib supplies pairwise coprimality of `X - C a`, finite products
     of coprime divisors, polynomial root/divisibility equivalence, and monic
     bounded-degree equality. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Analytic.GoldenTomography.FinitePronyAnnihilatorIdentification

open scoped BigOperators
open Polynomial
open D5.S3.Analytic.GoldenTomography.FiniteVandermondeTomography
open D5.S3.Analytic.GoldenTomography.FinitePronyRationalGeneratingFunction
open D5.S3.Analytic.GoldenTomography.FinitePronyAnnihilatorRecurrence

/-- A candidate polynomial satisfies the first matching window of shifted
Prony recurrence equations. -/
def finitePronyRecurrenceWindow {m : ℕ}
    (candidate : ℂ[X]) (nodes weights : Fin m → ℂ) : Prop :=
  ∀ time : Fin m,
    ∑ degree in candidate.support,
      candidate.coeff degree *
        finitePronyMoment nodes weights ((time : ℕ) + degree) = 0

/-- A polynomial recurrence valid on a full matching window must vanish at
every true node when the nodes are separated and all modal weights are active. -/
theorem finite_prony_recurrence_window_identifies_node_roots {m : ℕ}
    {nodes weights : Fin m → ℂ} (candidate : ℂ[X])
    (hNodes : Function.Injective nodes)
    (hWeights : ∀ mode, weights mode ≠ 0)
    (hRecurrence : finitePronyRecurrenceWindow candidate nodes weights) :
    ∀ mode, candidate.eval (nodes mode) = 0 := by
  classical
  let residualWeights : Fin m → ℂ :=
    fun mode => weights mode * candidate.eval (nodes mode)
  have hMomentZero (time : Fin m) :
      finitePronyMoment nodes residualWeights (time : ℕ) = 0 := by
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
              (∑ degree in candidate.support,
                candidate.coeff degree * nodes mode ^ degree) := by
        apply Finset.sum_congr rfl
        intro mode _
        rw [eval_eq_sum]
        ring
      _ = ∑ mode, ∑ degree in candidate.support,
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
      _ = ∑ degree in candidate.support, ∑ mode,
            candidate.coeff degree *
              (weights mode *
                nodes mode ^ ((time : ℕ) + degree)) := by
        rw [Finset.sum_comm]
      _ = ∑ degree in candidate.support,
            candidate.coeff degree *
              finitePronyMoment nodes weights
                ((time : ℕ) + degree) := by
        apply Finset.sum_congr rfl
        intro degree _
        unfold finitePronyMoment
        rw [Finset.mul_sum]
      _ = 0 := hRecurrence time
  have hResidualZero : residualWeights = fun _ => 0 := by
    apply finite_moment_readout_injective hNodes
    funext time
    rw [finite_moment_readout_apply, finite_moment_readout_apply]
    simpa [finitePronyMoment] using hMomentZero time
  intro mode
  have hProduct : weights mode * candidate.eval (nodes mode) = 0 := by
    simpa [residualWeights] using congrFun hResidualZero mode
  exact (mul_eq_zero.mp hProduct).resolve_left (hWeights mode)

/-- Every nonzero recurrence polynomial valid on a full separated active-mode
window is divisible by the true Prony annihilator. -/
theorem finite_prony_annihilator_dvd_of_recurrence_window {m : ℕ}
    {nodes weights : Fin m → ℂ} (candidate : ℂ[X])
    (hNodes : Function.Injective nodes)
    (hWeights : ∀ mode, weights mode ≠ 0)
    (hRecurrence : finitePronyRecurrenceWindow candidate nodes weights) :
    finitePronyAnnihilator nodes ∣ candidate := by
  classical
  have hRoots :=
    finite_prony_recurrence_window_identifies_node_roots
      candidate hNodes hWeights hRecurrence
  unfold finitePronyAnnihilator
  exact Fintype.prod_dvd_of_coprime
    (Polynomial.pairwise_coprime_X_sub_C hNodes)
    (fun mode => Polynomial.dvd_iff_isRoot.mpr (hRoots mode))

/-- No nonzero recurrence polynomial valid on a full separated active-mode
window can have degree below the number of active modes. -/
theorem finite_prony_recurrence_degree_lower_bound {m : ℕ}
    {nodes weights : Fin m → ℂ} (candidate : ℂ[X])
    (hNodes : Function.Injective nodes)
    (hWeights : ∀ mode, weights mode ≠ 0)
    (hCandidate : candidate ≠ 0)
    (hRecurrence : finitePronyRecurrenceWindow candidate nodes weights) :
    m ≤ candidate.natDegree := by
  rw [← finite_prony_annihilator_natDegree nodes]
  exact Polynomial.natDegree_le_of_dvd
    (finite_prony_annihilator_dvd_of_recurrence_window
      candidate hNodes hWeights hRecurrence)
    hCandidate

/-- The genuine node annihilator satisfies the matching recurrence window. -/
theorem finite_prony_annihilator_recurrence_window {m : ℕ}
    (nodes weights : Fin m → ℂ) :
    finitePronyRecurrenceWindow
      (finitePronyAnnihilator nodes) nodes weights := by
  intro time
  simpa [finitePronyRecurrenceResidual] using
    (finite_prony_moment_annihilator_recurrence
      nodes weights (time : ℕ))

/-- A monic recurrence polynomial of degree at most the mode count, valid on a
full separated active-mode window, is exactly the true Prony annihilator. -/
theorem finite_prony_recurrence_window_identifies_annihilator {m : ℕ}
    {nodes weights : Fin m → ℂ} (candidate : ℂ[X])
    (hNodes : Function.Injective nodes)
    (hWeights : ∀ mode, weights mode ≠ 0)
    (hCandidateMonic : candidate.Monic)
    (hCandidateDegree : candidate.natDegree ≤ m)
    (hRecurrence : finitePronyRecurrenceWindow candidate nodes weights) :
    candidate = finitePronyAnnihilator nodes := by
  have hDivides :=
    finite_prony_annihilator_dvd_of_recurrence_window
      candidate hNodes hWeights hRecurrence
  apply Polynomial.eq_of_monic_of_dvd_of_natDegree_le
    (finite_prony_annihilator_monic nodes)
    hCandidateMonic hDivides
  simpa [finite_prony_annihilator_natDegree nodes] using hCandidateDegree

/-- The true annihilator is the unique monic polynomial of degree at most `m`
whose recurrence holds on the first `m` shifts. -/
theorem existsUnique_finite_prony_annihilator_from_window {m : ℕ}
    {nodes weights : Fin m → ℂ}
    (hNodes : Function.Injective nodes)
    (hWeights : ∀ mode, weights mode ≠ 0) :
    ∃! candidate : ℂ[X],
      candidate.Monic ∧
      candidate.natDegree ≤ m ∧
      finitePronyRecurrenceWindow candidate nodes weights := by
  refine ⟨finitePronyAnnihilator nodes, ?_, ?_⟩
  · exact ⟨finite_prony_annihilator_monic nodes,
      (finite_prony_annihilator_natDegree nodes).le,
      finite_prony_annihilator_recurrence_window nodes weights⟩
  · intro candidate hCandidate
    exact finite_prony_recurrence_window_identifies_annihilator
      candidate hNodes hWeights hCandidate.1 hCandidate.2.1 hCandidate.2.2

-- A one-mode active family inhabits the exact identification regime.
example :
    ∃! candidate : ℂ[X],
      candidate.Monic ∧
      candidate.natDegree ≤ 1 ∧
      finitePronyRecurrenceWindow candidate
        (fun _ : Fin 1 => (2 : ℂ))
        (fun _ : Fin 1 => (3 : ℂ)) := by
  apply existsUnique_finite_prony_annihilator_from_window
  · intro left right h
    exact Subsingleton.elim left right
  · intro mode
    norm_num

#print axioms finite_prony_recurrence_window_identifies_node_roots
#print axioms finite_prony_annihilator_dvd_of_recurrence_window
#print axioms finite_prony_recurrence_degree_lower_bound
#print axioms finite_prony_annihilator_recurrence_window
#print axioms finite_prony_recurrence_window_identifies_annihilator
#print axioms existsUnique_finite_prony_annihilator_from_window

end D5.S3.Analytic.GoldenTomography.FinitePronyAnnihilatorIdentification
