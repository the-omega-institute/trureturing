/- GID: D5/S3/Weil/ZetaBridge/FiniteWeilObservableMixedForm
   generality: I
   mirror-B: D5/B/S3/Weil/ZetaBridge/FiniteWeilObservableMixedForm
   mirror-E: none(waiver:finite-observer-polarization)
   anchors: []
   digest: Reuse the exact observable range and mixed factorization to realize arbitrary reduced pairings and prove representative independence. -/

import D5.S3.Weil.ZetaBridge.WeilEvaluationExactObservableRange

/-!
# Mixed finite factorization on the exact observable range

The first slot of `finiteMirrorReducedForm` is linear; the second is
conjugate-linear. This convention is retained here. The existing full Gram owner
reverses the two basis arguments to obtain the usual `a* H a` convention.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Weil.ZetaBridge.FiniteWeilObservableMixedForm

open D5.S3.Weil.ZeroSum
open D5.S3.Weil.TestFunctions
open D5.S3.Weil.ZetaBridge.WeilEvaluationObservableSubspace
open D5.S3.Weil.ZetaBridge.FiniteMirrorReducedWeilFactorization
open D5.S3.Weil.ZetaBridge.WeilEvaluationExactObservableRange
open scoped BigOperators ComplexConjugate

/-- The reduced form on arbitrary admissible vectors is realized by actual
mixed test functions. Both representatives are constructed by interpolation. -/
theorem every_reduced_mixed_pairing_is_realized
    (Z : ZeroData) (T : ℝ) (v w : FiniteReflectionEvenVector Z T) :
    ∃ g h : WeilTestFunction,
      finiteWeilReducedEvaluation Z T g = v ∧
      finiteWeilReducedEvaluation Z T h = w ∧
      truncatedZeroSum Z (convolve g (involution h)) T =
        finiteMirrorReducedForm Z T v w := by
  obtain ⟨g, hg⟩ := finiteWeilReducedEvaluation_surjective Z T v
  obtain ⟨h, hh⟩ := finiteWeilReducedEvaluation_surjective Z T w
  refine ⟨g, h, hg, hh, ?_⟩
  rw [truncatedZeroSum_mixed_eq_reducedMirrorForm, hg, hh]

/-- The mixed pairing depends only on the two observable vectors. -/
theorem truncated_mixed_pairing_independent_of_representatives
    (Z : ZeroData) (T : ℝ) (g g' h h' : WeilTestFunction)
    (hg : finiteWeilReducedEvaluation Z T g = finiteWeilReducedEvaluation Z T g')
    (hh : finiteWeilReducedEvaluation Z T h = finiteWeilReducedEvaluation Z T h') :
    truncatedZeroSum Z (convolve g (involution h)) T =
      truncatedZeroSum Z (convolve g' (involution h')) T := by
  rw [truncatedZeroSum_mixed_eq_reducedMirrorForm,
    truncatedZeroSum_mixed_eq_reducedMirrorForm, hg, hh]

#print axioms every_reduced_mixed_pairing_is_realized
#print axioms truncated_mixed_pairing_independent_of_representatives

end D5.S3.Weil.ZetaBridge.FiniteWeilObservableMixedForm
