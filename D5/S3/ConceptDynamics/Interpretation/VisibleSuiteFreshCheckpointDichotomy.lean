/- GID: D5/S3/ConceptDynamics/Interpretation/VisibleSuiteFreshCheckpointDichotomy
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Interpretation/VisibleSuiteFreshCheckpointDichotomy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Visible-suite lookup and fresh product checkpoints have different deployment force. -/

import D5.S0.Computability.DescriptionComplexity.LookupProgramUpperBound
import D5.S3.ConceptDynamics.Interpretation.FreshIndependentCheckpointGuarantee

/- Library-search audit trail (2026-09-04):
   * Repository name and body-shape searches found no theorem combining a
     suite-dependent reward maximizer, its lookup-description bound, its exact
     off-suite loss, and a general fresh-checkpoint guarantee.
   * The exact repository hit `lookup_program_upper_bound` supplies the
     description-complexity step. The exact hit
     `fresh_independent_checkpoint_deployment_guarantee` supplies both the
     product-law identity and its exponential envelope. Both are applied.
   * The existing Boolean joint-law interpretation modules omit the visible
     optimizer and lookup-cost clauses, so none is a whole-statement hit.
   * Pinned Mathlib and the other installed Lean packages have no theorem for
     this combined shape. Mathlib's finite-image, filter-cardinality, and set
     extensionality primitives discharge the construction-specific steps. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.ConceptDynamics.Interpretation.VisibleSuiteFreshCheckpointDichotomy

open MeasureTheory Set
open D5.S0.Computability.DescriptionComplexity.LookupProgramUpperBound
open D5.S3.ConceptDynamics.Interpretation.FreshIndependentCheckpointGuarantee

/-- A lookup program carries the visible suite from which its behavior is selected. -/
structure VisibleSuiteProgram (Input : Type*) (m : Nat) where
  suite : Fin m -> Input

/-- The inputs exposed by the program's visible suite. -/
def VisibleSuiteProgram.observedInputs {Input : Type*} {m : Nat}
    [DecidableEq Input] (program : VisibleSuiteProgram Input m) : Finset Input :=
  Finset.univ.image program.suite

/-- A visible-suite lookup agrees with the expected output on exposed inputs and
uses the supplied alternative output elsewhere. -/
def VisibleSuiteProgram.run {Input Output : Type*} {m : Nat} [DecidableEq Input]
    (expected : Input -> Output) (opposite : Output -> Output)
    (program : VisibleSuiteProgram Input m) : Input -> Output :=
  fun input =>
    if input ∈ program.observedInputs then expected input else opposite (expected input)

/-- The unregularized reward is exactly the number of visible checks passed. -/
def suiteReward {Input Output : Type*} {m : Nat} [DecidableEq Output]
    (expected implementation : Input -> Output) (suite : Fin m -> Input) : Nat :=
  (Finset.univ.filter fun index =>
    implementation (suite index) = expected (suite index)).card

/-- A suite-dependent lookup maximizes the visible reward while its deployment
loss is the unseen mass. In contrast, any implementation fixed before fresh,
deployment-matched product checkpoints receives the exponential guarantee. -/
theorem visible_suite_and_fresh_checkpoint_dichotomy
    {Input Output : Type*}
    [MeasurableSpace Input] [MeasurableSingletonClass Input] [Countable Input]
    [DecidableEq Input] [DecidableEq Output]
    (deployment : PMF Input) (expected : Input -> Output)
    (opposite : Output -> Output) (oppositeNe : forall output, opposite output ≠ output)
    (m : Nat) (trainingSuite : Fin m -> Input)
    (programCost : VisibleSuiteProgram Input m -> Nat)
    (suiteComplexity : (Fin m -> Input) -> Nat) (overhead : Nat)
    (compiler : LookupCompiler (Fin m -> Input) (VisibleSuiteProgram Input m)
      (fun program suite => program.suite = suite)
      programCost suiteComplexity overhead)
    (frozenImplementation : Input -> Output) (epsilon : Real)
    (epsilonNonnegative : 0 <= epsilon) (epsilonAtMostOne : epsilon <= 1)
    (frozenLossAtLeast :
      epsilon <= deployment.toMeasure.real
        {input | frozenImplementation input ≠ expected input}) :
    programCost (VisibleSuiteProgram.mk trainingSuite) <=
        suiteComplexity trainingSuite + overhead /\
      (forall index,
        (VisibleSuiteProgram.mk trainingSuite).run expected opposite
            (trainingSuite index) =
          expected (trainingSuite index)) /\
      suiteReward expected
          ((VisibleSuiteProgram.mk trainingSuite).run expected opposite) trainingSuite = m /\
      (forall candidate : Input -> Output,
        suiteReward expected candidate trainingSuite <=
          suiteReward expected
            ((VisibleSuiteProgram.mk trainingSuite).run expected opposite) trainingSuite) /\
      deployment.toMeasure.real
          {input |
            (VisibleSuiteProgram.mk trainingSuite).run expected opposite input ≠
              expected input} =
        deployment.toMeasure.real
          (VisibleSuiteProgram.observedInputs
            (VisibleSuiteProgram.mk trainingSuite) : Set Input)ᶜ /\
      (Measure.pi (fun _ : Fin m => deployment.toMeasure)).real
          {suite | forall index,
            frozenImplementation (suite index) = expected (suite index)} =
        (deployment.toMeasure.real
          {input | frozenImplementation input = expected input}) ^ m /\
      (Measure.pi (fun _ : Fin m => deployment.toMeasure)).real
          {suite | forall index,
            frozenImplementation (suite index) = expected (suite index)} <=
        Real.exp (-(epsilon * (m : Real))) := by
  classical
  let canonicalProgram : VisibleSuiteProgram Input m :=
    VisibleSuiteProgram.mk trainingSuite
  let coadapted : Input -> Output := canonicalProgram.run expected opposite
  let costExists : exists cost : Nat, exists program : VisibleSuiteProgram Input m,
      program.suite = trainingSuite /\ programCost program = cost :=
    ⟨programCost (compiler.compile trainingSuite), compiler.compile trainingSuite,
      compiler.compile_consistent trainingSuite, rfl⟩
  have bottomEq :
      spectrumBottom compiler trainingSuite = Nat.find costExists := by
    unfold spectrumBottom
    rfl
  obtain ⟨program, programConsistent, programCostEq⟩ := Nat.find_spec costExists
  have programEq : program = canonicalProgram := by
    rcases program with ⟨programSuite⟩
    simp only at programConsistent
    subst programSuite
    rfl
  have canonicalCostEq :
      programCost canonicalProgram = spectrumBottom compiler trainingSuite := by
    rw [bottomEq, <- programCostEq, programEq]
  have complexityBound :
      programCost canonicalProgram <= suiteComplexity trainingSuite + overhead := by
    rw [canonicalCostEq]
    exact lookup_program_upper_bound compiler trainingSuite
  have trainingPasses : forall index,
      coadapted (trainingSuite index) = expected (trainingSuite index) := by
    intro index
    have inputObserved :
        trainingSuite index ∈ canonicalProgram.observedInputs := by
      exact Finset.mem_image.mpr ⟨index, Finset.mem_univ index, rfl⟩
    simp [coadapted, VisibleSuiteProgram.run, inputObserved]
  have fullReward : suiteReward expected coadapted trainingSuite = m := by
    simp [suiteReward, trainingPasses]
  have maximalReward : forall candidate : Input -> Output,
      suiteReward expected candidate trainingSuite <=
        suiteReward expected coadapted trainingSuite := by
    intro candidate
    rw [fullReward]
    simpa [suiteReward] using
      Finset.card_le_card (Finset.filter_subset
        (s := Finset.univ)
        (p := fun index => candidate (trainingSuite index) = expected (trainingSuite index)))
  have coadaptedErrorSet :
      {input | coadapted input ≠ expected input} =
        (canonicalProgram.observedInputs : Set Input)ᶜ := by
    ext input
    by_cases inputObserved : input ∈ canonicalProgram.observedInputs
    · simp [coadapted, VisibleSuiteProgram.run, inputObserved]
    · simp [coadapted, VisibleSuiteProgram.run, inputObserved, oppositeNe]
  have coadaptedLoss :
      deployment.toMeasure.real {input | coadapted input ≠ expected input} =
        deployment.toMeasure.real
          (canonicalProgram.observedInputs : Set Input)ᶜ := by
    rw [coadaptedErrorSet]
  obtain ⟨externalExact, externalBound⟩ :=
    fresh_independent_checkpoint_deployment_guarantee
      deployment frozenImplementation expected m epsilon
        epsilonNonnegative epsilonAtMostOne frozenLossAtLeast
  exact ⟨by simpa [canonicalProgram] using complexityBound,
    by simpa [canonicalProgram, coadapted] using trainingPasses,
    by simpa [canonicalProgram, coadapted] using fullReward,
    by simpa [canonicalProgram, coadapted] using maximalReward,
    by simpa [canonicalProgram, coadapted] using coadaptedLoss,
    externalExact, externalBound⟩

#print axioms visible_suite_and_fresh_checkpoint_dichotomy

end D5.S3.ConceptDynamics.Interpretation.VisibleSuiteFreshCheckpointDichotomy
