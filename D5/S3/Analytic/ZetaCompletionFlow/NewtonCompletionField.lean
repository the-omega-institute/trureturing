/- GID: D5/S3/Analytic/ZetaCompletionFlow/NewtonCompletionField
   generality: G
   mirror-B: D5/B/S3/Analytic/ZetaCompletionFlow/NewtonCompletionField
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The Newton completion vector is scale invariant, detects roots under a regular derivative, and exactly completes affine zero models in one step. -/

import Mathlib

/-!
The Newton vector is a local predictor, not itself a zero.  All equivalences
between a zero vector and a genuine root carry the regularity hypothesis
`dF s ≠ 0`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Analytic.ZetaCompletionFlow.NewtonCompletionField

universe u

variable {K : Type u} [Field K]

/-- Static Newton completion vector. -/
def newtonCompletionVector (F dF : K → K) (s : K) : K :=
  -F s / dF s

/-- Candidate point after one Newton completion step. -/
def newtonCompletionStep (F dF : K → K) (s : K) : K :=
  s + newtonCompletionVector F dF s

/-- At a regular point, the Newton vector vanishes exactly at a root. -/
theorem newton_completion_vector_eq_zero_iff
    {F dF : K → K} {s : K} (hRegular : dF s ≠ 0) :
    newtonCompletionVector F dF s = 0 ↔ F s = 0 := by
  simp [newtonCompletionVector, hRegular]

/-- Common nonzero rescaling of a function and its derivative field leaves the
Newton vector unchanged. -/
theorem newton_completion_vector_scale_invariant
    (c : K) (F dF : K → K) (s : K)
    (hC : c ≠ 0) (hRegular : dF s ≠ 0) :
    newtonCompletionVector (fun z => c * F z) (fun z => c * dF z) s =
      newtonCompletionVector F dF s := by
  unfold newtonCompletionVector
  field_simp [hC, hRegular]

/-- The Newton vector of an affine simple-zero model points exactly from the
current point to its root. -/
theorem affine_newton_completion_vector
    {a root s : K} (hA : a ≠ 0) :
    newtonCompletionVector (fun z => a * (z - root)) (fun _ => a) s =
      root - s := by
  unfold newtonCompletionVector
  field_simp [hA]
  ring

/-- Consequently, an affine simple-zero model completes in one Newton step. -/
theorem affine_newton_completion_step
    {a root s : K} (hA : a ≠ 0) :
    newtonCompletionStep (fun z => a * (z - root)) (fun _ => a) s =
      root := by
  rw [newtonCompletionStep, affine_newton_completion_vector hA]
  ring

/-- A genuine regular root is fixed by the Newton completion step. -/
theorem root_fixed_by_newton_completion
    {F dF : K → K} {root : K}
    (hRoot : F root = 0) :
    newtonCompletionStep F dF root = root := by
  simp [newtonCompletionStep, newtonCompletionVector, hRoot]

/-- Totalized division at a singular derivative returns zero.  This equality is
recorded only as an algebraic probe and carries no simple-zero interpretation. -/
example (F dF : K → K) (s : K) (hSingular : dF s = 0) :
    newtonCompletionVector F dF s = 0 := by
  simp [newtonCompletionVector, hSingular]

#print axioms newton_completion_vector_eq_zero_iff
#print axioms newton_completion_vector_scale_invariant
#print axioms affine_newton_completion_vector
#print axioms affine_newton_completion_step
#print axioms root_fixed_by_newton_completion

end D5.S3.Analytic.ZetaCompletionFlow.NewtonCompletionField
