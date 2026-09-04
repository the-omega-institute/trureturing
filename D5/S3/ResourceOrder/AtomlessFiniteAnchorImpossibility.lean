/- GID: D5/S3/ResourceOrder/AtomlessFiniteAnchorImpossibility
   generality: G
   mirror-B: D5/B/S3/ResourceOrder/AtomlessFiniteAnchorImpossibility
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Every finite anchor family on an atomless probability space admits an implementation that passes every exposed suite while being wrong almost everywhere. -/

import D5.S3.ResourceOrder.FiniteAnchorCoverage
import Mathlib.MeasureTheory.Measure.NullMeasurable
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/- Library-search audit trail (2026-09-04):
   * Exact keyword and symbol searches over `D5/**/*.lean`, frozen-event selectors,
     Blueprint mirrors, and digestion indices found no theorem combining finite
     anchor-suite agreement with a full-measure error set.
   * `FiniteAnchorCoverage.finite_anchor_coverage_bound_and_evasion` gives the
     finite-union evasion construction, but its own Blueprint explicitly leaves
     the nonatomic-domain clause unresolved. General searches found countable
     naming-tower nullity, but no implementation that passes each supplied suite.
   * The source atom is an orphaned multi-clause fragment. This module formalizes
     its complete information-theoretic nonatomic core; the undefined covering
     number, asymptotic capacity bracket, PRG claim, and random-family Chernoff
     clause are not asserted here.
   * Pinned Mathlib supplies the exact primitives `Set.Countable.measure_zero`
     and `measure_of_measure_compl_eq_zero`. No local null-set lemma is reproved.
   * Searches of current remote math lanes found no in-flight module with this
     theorem shape. The existing `ResourceOrder` domain is registered and has
     capacity for this module. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ResourceOrder.AtomlessFiniteAnchorImpossibility

open MeasureTheory
open D5.S3.ResourceOrder.FiniteAnchorCoverage

universe u v

set_option checkBinderAnnotations false in
/-- On an atomless probability space, finitely many finite suites cannot give
an information-theoretic correctness guarantee: an explicit implementation
passes every exposed test while disagreeing with the truth almost everywhere. -/
theorem atomless_finite_anchor_evasion
    {Anchor : Type u} {Input : Type v} [Fintype Anchor]
    [MeasurableSpace Input] [DecidableEq Input]
    (volume : Measure Input) [NullSingletonClass volume]
    [IsProbabilityMeasure volume]
    (suite : Anchor -> Finset Input) (truth : Input -> Bool) :
    exists implementation : Input -> Bool,
      (forall anchor input, input ∈ suite anchor ->
        implementation input = truth input) /\
      volume {input | implementation input != truth input} = 1 := by
  classical
  let covered : Set Input := (coveredInputs suite : Finset Input)
  let implementation : Input -> Bool := fun input =>
    if input ∈ coveredInputs suite then truth input else !truth input
  refine ⟨implementation, ?_, ?_⟩
  · intro anchor input inputInSuite
    have inputCovered : input ∈ coveredInputs suite :=
      Finset.mem_biUnion.mpr ⟨anchor, Finset.mem_univ _, inputInSuite⟩
    simp [implementation, inputCovered]
  · have coveredCountable : covered.Countable := by
      exact (coveredInputs suite).finite_toSet.countable
    have coveredNull : volume covered = 0 :=
      @Set.Countable.measure_zero Input _ covered coveredCountable volume inferInstance
    have errorSet :
        {input | implementation input != truth input} = coveredᶜ := by
      ext input
      by_cases inputCovered : input ∈ coveredInputs suite
      · simp [implementation, covered, inputCovered]
      · cases truth input <;> simp [implementation, covered, inputCovered]
    rw [errorSet]
    have fullComplement : volume coveredᶜ = volume (Set.univ : Set Input) := by
      apply measure_of_measure_compl_eq_zero
      simpa only [compl_compl] using coveredNull
    rw [fullComplement, IsProbabilityMeasure.measure_univ]

#print axioms atomless_finite_anchor_evasion

end D5.S3.ResourceOrder.AtomlessFiniteAnchorImpossibility
