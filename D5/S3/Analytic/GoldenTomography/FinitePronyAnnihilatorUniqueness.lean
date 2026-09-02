/- GID: D5/S3/Analytic/GoldenTomography/FinitePronyAnnihilatorUniqueness
   generality: G
   mirror-B: D5/B/S3/Analytic/GoldenTomography/FinitePronyAnnihilatorUniqueness
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The true node annihilator is the unique monic polynomial of bounded degree whose recurrence holds on a full finite Prony window. -/

import D5.S3.Analytic.GoldenTomography.FinitePronyNodeIdentification
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.RingTheory.Coprime.Lemmas

/-!
# Finite Prony annihilator uniqueness

The finite recurrence-to-root theorem identifies every true mode as a root of a
candidate recurrence polynomial. Distinct nodes make the linear factors
pairwise coprime. Hence their product divides the candidate. If the candidate is
monic and has degree at most the number of modes, degree comparison forces it
to equal the true Prony annihilator.

This supplies exact uniqueness of the annihilator from a matching recurrence
window. It does not select the coefficients computationally or quantify noisy
root perturbations.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped BigOperators Function

namespace D5.S3.Analytic.GoldenTomography.FinitePronyAnnihilatorUniqueness

open Polynomial
open D5.S3.Analytic.GoldenTomography.FinitePronyHankelReconstruction
open D5.S3.Analytic.GoldenTomography.FinitePronyNodeIdentification

universe u

variable {K : Type u} [Field K]

/-- The node annihilator is monic. -/
theorem prony_annihilator_monic {m : ℕ} (nodes : Fin m → K) :
    (pronyAnnihilator nodes).Monic := by
  classical
  unfold pronyAnnihilator
  apply Polynomial.monic_prod_of_monic
  intro mode _
  exact Polynomial.monic_X_sub_C (nodes mode)

/-- The node annihilator has degree equal to the number of indexed modes. -/
theorem prony_annihilator_natDegree {m : ℕ} (nodes : Fin m → K) :
    (pronyAnnihilator nodes).natDegree = m := by
  classical
  unfold pronyAnnihilator
  calc
    (∏ mode : Fin m, (X - C (nodes mode))).natDegree =
        ∑ mode : Fin m, (X - C (nodes mode)).natDegree := by
      apply Polynomial.natDegree_prod_of_monic
      intro mode _
      exact Polynomial.monic_X_sub_C (nodes mode)
    _ = m := by simp

/-- A monic bounded-degree recurrence polynomial valid on a full matching
window is exactly the true node annihilator. -/
theorem recurrence_window_identifies_annihilator {m : ℕ}
    {nodes weights : Fin m → K} (candidate : K[X])
    (hNodes : Function.Injective nodes)
    (hWeights : ∀ mode, weights mode ≠ 0)
    (hCandidateMonic : candidate.Monic)
    (hCandidateDegree : candidate.natDegree ≤ m)
    (hRecurrence : ∀ time : Fin m,
      ∑ degree in candidate.support,
          candidate.coeff degree *
            pronyMoment nodes weights ((time : ℕ) + degree) = 0) :
    candidate = pronyAnnihilator nodes := by
  classical
  have hRoots : ∀ mode, candidate.eval (nodes mode) = 0 :=
    recurrence_window_identifies_node_roots candidate hNodes hWeights hRecurrence
  have hDivides : pronyAnnihilator nodes ∣ candidate := by
    unfold pronyAnnihilator
    exact Fintype.prod_dvd_of_coprime
      (Polynomial.pairwise_coprime_X_sub_C hNodes)
      (fun mode => Polynomial.dvd_iff_isRoot.mpr (hRoots mode))
  apply Polynomial.eq_of_monic_of_dvd_of_natDegree_le
    (prony_annihilator_monic nodes) hCandidateMonic hDivides
  simpa [prony_annihilator_natDegree nodes] using hCandidateDegree

/-- The true annihilator is the unique monic polynomial of degree at most `m`
whose coefficient recurrence holds on the first `m` shifts. -/
theorem existsUnique_prony_annihilator_from_window {m : ℕ}
    {nodes weights : Fin m → K}
    (hNodes : Function.Injective nodes)
    (hWeights : ∀ mode, weights mode ≠ 0) :
    ∃! candidate : K[X],
      candidate.Monic ∧
      candidate.natDegree ≤ m ∧
      ∀ time : Fin m,
        ∑ degree in candidate.support,
            candidate.coeff degree *
              pronyMoment nodes weights ((time : ℕ) + degree) = 0 := by
  refine ⟨pronyAnnihilator nodes, ?_, ?_⟩
  · exact ⟨prony_annihilator_monic nodes,
      (prony_annihilator_natDegree nodes).le,
      prony_annihilator_recurrence_window nodes weights⟩
  · intro candidate hCandidate
    exact recurrence_window_identifies_annihilator candidate hNodes hWeights
      hCandidate.1 hCandidate.2.1 hCandidate.2.2

#print axioms prony_annihilator_monic
#print axioms prony_annihilator_natDegree
#print axioms recurrence_window_identifies_annihilator
#print axioms existsUnique_prony_annihilator_from_window

end D5.S3.Analytic.GoldenTomography.FinitePronyAnnihilatorUniqueness
