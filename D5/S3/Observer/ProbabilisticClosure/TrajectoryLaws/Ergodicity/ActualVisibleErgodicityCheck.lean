import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.Ergodicity.IrreducibleVisibleErgodicity
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.Rectangles.OriginalRectangleOccurrence

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory Matrix
open scoped BigOperators Classical Matrix
open D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws
open MarkedPredictiveQuotient OriginalMarkedLaw OriginalLawTrimming OriginalRectangleOccurrence

universe u
example {H : Type u} [Fintype H] [MeasurableSpace H] [MeasurableSingletonClass H]
    (θ : Presentation H) :
    ∀ (C : FiniteClosedClasses.ClosedClass (θ.matrix false+θ.matrix true))
      (hc : 0 < ∑ i : C.val, θ.initial i.val),
    Ergodic (fun z : ℤ → Bool => fun t => z (1+t))
      (visibleLaw (nativeComponent θ C hc) : Measure (ℤ → Bool)) := by
  classical
  intro C hc
  apply Ergodicity.IrreducibleVisibleErgodicity.actual_output_ergodic
  have hT : θ.matrix false+θ.matrix true ∈ rowStochastic ℝ H :=
    Matrix.mem_rowStochastic_iff_sum.mpr
      ⟨fun i j => add_nonneg (θ.matrix_nonneg false i j)
        (θ.matrix_nonneg true i j), θ.stochastic⟩
  change Matrix.IsIrreducible
    (FiniteClosedClasses.restriction (θ.matrix false+θ.matrix true) C.val)
  exact (FiniteClosedClasses.actual_structure _ hT).class_irreducible C
