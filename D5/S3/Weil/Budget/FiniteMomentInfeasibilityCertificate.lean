/- GID: D5/S3/Weil/Budget/FiniteMomentInfeasibilityCertificate
   generality: G
   mirror-B: D5/B/S3/Weil/Budget/FiniteMomentInfeasibilityCertificate
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Finite SDP infeasibility excludes every compatible positive spectral completion. -/

import Mathlib.LinearAlgebra.Matrix.PosDef

/- Library-search audit trail (2026-08-29):
   * D5 and current-origin searches for finite moment infeasibility, resolvent-budget
     certificates, and Toeplitz feasibility found no exact frozen theorem.
   * Body-shape searches for a completion-to-moment map satisfying interval and
     positive-semidefinite constraints found no canonical D5 feasibility predicate.
   * Pinned Mathlib supplies `Matrix.PosSemidef`, but no packaged implication from
     infeasibility of a finite moment problem to nonexistence of a completion. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Weil.Budget.FiniteMomentInfeasibilityCertificate

/-- If every real-axis even positive completion compatible with the local source and
Cayley compactification constructs an admissible finite moment vector, infeasibility
of that finite semidefinite problem excludes every such completion whose resolvent
budget lies in the prescribed interval. -/
theorem finite_moment_infeasibility_certificate
    (N : Nat) (lower upper : Real)
    (target : Real -> Fin (N + 1) -> Real)
    (tolerance : Fin (N + 1) -> Real)
    (toeplitz : (Fin (N + 1) -> Real) -> Matrix (Fin (N + 1)) (Fin (N + 1)) Real)
    {Completion : Type*}
    (realAxisSpectrum evenSpectrum positiveSpectrum : Completion -> Prop)
    (localWeilSource : Completion -> Prop)
    (resolventBudget : Completion -> Real)
    (cayleyCompactification : Completion -> Prop)
    (moments : Completion -> Fin (N + 1) -> Real)
    (zeroMoment : forall completion,
      moments completion 0 = resolventBudget completion)
    (intervalControl : forall completion,
      realAxisSpectrum completion ->
      evenSpectrum completion ->
      positiveSpectrum completion ->
      localWeilSource completion ->
      cayleyCompactification completion ->
      forall n,
        |moments completion n - target (resolventBudget completion) n| <=
          resolventBudget completion * tolerance n)
    (toeplitzPositive : forall completion,
      realAxisSpectrum completion ->
      evenSpectrum completion ->
      positiveSpectrum completion ->
      cayleyCompactification completion ->
      Matrix.PosSemidef (toeplitz (moments completion)))
    (sdpInfeasible : Not (exists R m,
      lower <= R /\
      R <= upper /\
      m 0 = R /\
      (forall n, |m n - target R n| <= R * tolerance n) /\
      Matrix.PosSemidef (toeplitz m))) :
    Not (exists completion,
      realAxisSpectrum completion /\
      evenSpectrum completion /\
      positiveSpectrum completion /\
      localWeilSource completion /\
      lower <= resolventBudget completion /\
      resolventBudget completion <= upper /\
      cayleyCompactification completion) := by
  rintro ⟨completion, realAxis, even, positive, localSource,
    budgetLower, budgetUpper, compactification⟩
  apply sdpInfeasible
  refine ⟨resolventBudget completion, moments completion,
    budgetLower, budgetUpper, zeroMoment completion, ?_, ?_⟩
  · exact intervalControl completion realAxis even positive localSource compactification
  · exact toeplitzPositive completion realAxis even positive compactification

#print axioms finite_moment_infeasibility_certificate

end D5.S3.Weil.Budget.FiniteMomentInfeasibilityCertificate
