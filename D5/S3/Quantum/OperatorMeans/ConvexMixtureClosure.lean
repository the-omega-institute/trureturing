/- GID: D5/S3/Quantum/OperatorMeans/ConvexMixtureClosure
   generality: G
   mirror-B: D5/B/S3/Quantum/OperatorMeans/ConvexMixtureClosure
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A convex family is closed under every binary convex mixture. -/

/- Library-search audit trail (2026-08-17):
   * Pinned Mathlib search found that `Convex` directly supplies binary combination closure.
   * D5 searches found no Kubo--Ando or operator-mean convex-mixture declaration.
   * The theorem below is the thinnest wrapper converting `c in [0, 1]` into Mathlib's
     two nonnegative weights summing to one.
-/

import Mathlib.Analysis.Convex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

namespace D5.S3.Quantum.OperatorMeans.ConvexMixtureClosure

/-- Any convex family, in particular any operator-mean family known to be convex, contains
the mixture of two of its members with a coefficient in the unit interval. -/
theorem convex_mixture_mem
    {E : Type*} [AddCommMonoid E] [Module ℝ E] {family : Set E}
    (hFamily : Convex ℝ family) {first second : E}
    (hFirst : first ∈ family) (hSecond : second ∈ family)
    {coefficient : ℝ} (hCoefficient : coefficient ∈ Set.Icc (0 : ℝ) 1) :
    coefficient • first + (1 - coefficient) • second ∈ family := by
  exact hFamily hFirst hSecond hCoefficient.1 (sub_nonneg.mpr hCoefficient.2) (by ring)

#print axioms convex_mixture_mem

end D5.S3.Quantum.OperatorMeans.ConvexMixtureClosure
