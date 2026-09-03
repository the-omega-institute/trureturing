/- GID: D5/S3/ConceptDynamics/Experiment/FiniteProductAbsoluteContinuity
   generality: I
   mirror-B: D5/B/S3/ConceptDynamics/Experiment/FiniteProductAbsoluteContinuity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Finite products of nondegenerate coordinate laws dominate every product law. -/

import D5.S3.ConceptDynamics.Experiment.InfiniteIdentificationFiniteInexactness
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.MeasureTheory.Measure.MutuallySingular

/- Library-search audit trail (2026-09-03):
   * Repository search for a public form of either statement found none; the only
     occurrences are one `private` copy of each in
     `ConceptDynamics/ExperimentBoundary/FinitePrefixInfiniteCompletionSeparation`
     and in `ConceptDynamics/ExperimentDesign/FinitePrefixInfiniteCompletionSeparation`.
   * Pinned Mathlib was searched by name and, separately, by concept for finite
     product absolute continuity. The relatives found are
     `Measure.AbsolutelyContinuous.prod`, which is the binary product, and
     `Measure.pi_singleton`, which evaluates a singleton of a finite indexed
     product; the latter is used in the proof below. This search found no
     upstream statement of the finite-product domination itself, which is what
     the searches show and no more.
   * No new primitive is introduced. `marginal` is the frozen definition of
     `Experiment.InfiniteIdentificationFiniteInexactness`, used through the
     import above. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Experiment.FiniteProductAbsoluteContinuity

open MeasureTheory ProbabilityTheory Set Finset
open D5.S3.ConceptDynamics.Experiment.InfiniteIdentificationFiniteInexactness

/-- The true outcome carries positive mass as soon as the success probability is
positive; the upper bound is not needed. -/
theorem marginal_true_pos (p : unitInterval) (hp0 : 0 < (p : Real)) :
    0 < marginal p {true} := by
  rw [marginal, bernoulliMeasure_apply_of_mem_of_notMem p
    (measurableSet_singleton true) (by decide) (by decide)]
  rw [ENNReal.coe_pos, ← NNReal.coe_pos]
  exact hp0

/-- The false outcome carries positive mass as soon as the success probability is
below one; the lower bound is not needed. -/
theorem marginal_false_pos (p : unitInterval) (hp1 : (p : Real) < 1) :
    0 < marginal p {false} := by
  rw [marginal, bernoulliMeasure_apply_of_notMem_of_mem p
    (measurableSet_singleton false) (by decide) (by decide)]
  rw [ENNReal.coe_pos, ← NNReal.coe_pos]
  change 0 < 1 - (p : Real)
  linarith

/-- Every outcome of a nondegenerate Boolean coordinate law carries positive
mass.  Both bounds are needed here because the statement ranges over both
outcomes; each single outcome needs only one of them. -/
theorem marginal_singleton_pos
    (p : unitInterval) (hp0 : 0 < (p : Real)) (hp1 : (p : Real) < 1)
    (outcome : Bool) : 0 < marginal p {outcome} := by
  cases outcome with
  | false => exact marginal_false_pos p hp1
  | true => exact marginal_true_pos p hp0

/-- A product of nondegenerate coordinate laws, one per index and not required to
be the same law at each index, dominates every measure on transcripts.  The
proof uses nothing about the dominated measure beyond its value on the empty
set: the reference product charges every singleton, so a reference null set is
empty. -/
theorem absolutelyContinuous_pi_marginal
    {Index : Type*} [Fintype Index]
    (mu : Measure (Index -> Bool)) (q : Index -> unitInterval)
    (hq0 : forall i, 0 < ((q i : Real))) (hq1 : forall i, ((q i : Real)) < 1) :
    mu ≪ Measure.pi (fun i => marginal (q i)) := by
  refine Measure.AbsolutelyContinuous.mk fun event _hmeasurable hzero => ?_
  have hempty : event = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro transcript htranscript
    have hsingletonZero :
        Measure.pi (fun i => marginal (q i)) {transcript} = 0 :=
      measure_mono_null (Set.singleton_subset_iff.mpr htranscript) hzero
    rw [Measure.pi_singleton] at hsingletonZero
    have hnonzero :
        (∏ i, marginal (q i) {transcript i}) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun i _ =>
        (marginal_singleton_pos (q i) (hq0 i) (hq1 i) (transcript i)).ne'
    exact hnonzero hsingletonZero
  simp [hempty]

/-- The identically distributed case, in the shape the repository re-derives:
a finite product of copies of one coordinate law is absolutely continuous with
respect to the product of copies of any nondegenerate reference law. -/
theorem finite_product_absolutelyContinuous
    {Index : Type*} [Fintype Index]
    (p q : unitInterval) (hq0 : 0 < (q : Real)) (hq1 : (q : Real) < 1) :
    Measure.pi (fun _ : Index => marginal p) ≪
      Measure.pi (fun _ : Index => marginal q) :=
  absolutelyContinuous_pi_marginal _ (fun _ => q) (fun _ => hq0) (fun _ => hq1)

end D5.S3.ConceptDynamics.Experiment.FiniteProductAbsoluteContinuity
