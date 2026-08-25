/- GID: D5/S3/ConceptDynamics/ExperimentDesign/WeakestTargetDirectionValue
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/ExperimentDesign/WeakestTargetDirectionValue
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Experiment value improves weakest target directions and covers target-distinct pairs. -/

import D5.S3.ConceptDynamics.Experiments.ExperimentRefinementGainMonotone
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.LinearAlgebra.Matrix.Trace

/- Library-search audit trail (2026-08-25):
   * Repository searches for weakest target directions, projected Gramians,
     minimum eigenvalues, and maximal target-pair cover found no theorem with
     all three public clauses below.
   * Exact family hit `experimentGain` constructs the discrete target-defect
     pairs removed by adjoining an experiment, so that primitive is imported
     rather than redeclared.
   * `TargetRelativePairUniverse.target_relative_pair_universe` is an adjacent
     exact cover characterization for unordered finite-model pairs, but it has
     neither the spectral clause nor a maximal single-experiment selection.
   * Pinned Mathlib's `ContinuousLinearMap.rayleighQuotient_add`, `ciInf_le`,
     `le_ciInf`, `Matrix.trace_add`, and `Finset.exists_max_image` are exact
     proof-level hits. No library theorem packages the combined statement.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.ExperimentDesign.WeakestTargetDirectionValue

open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.ConceptJoinUniversal
open D5.S3.ConceptDynamics.Experiments.ExperimentRefinementGainMonotone

universe u v w z

/-- A uniformly positive added experiment strictly improves the weakest
target-direction Rayleigh score. In contrast, an explicit trace-increasing
two-dimensional experiment leaves the projected target operator unchanged and
fails to identify the target coordinate. On finite discrete carriers, some
candidate maximizes the number of current target-distinct pairs it separates. -/
theorem weakest_target_direction_experiment_value :
    (∀ {𝕜 : Type u} [RCLike 𝕜]
        {V : Type v} [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
        [FiniteDimensional 𝕜 V]
        (P W Wₐ : V →ₗ[𝕜] V)
        (_targetProjection : P.comp P = P)
        (_projectionSymmetric : P.IsSymmetric)
        (_baselineSymmetric : W.IsSymmetric)
        (_addedSymmetric : Wₐ.IsSymmetric)
        (_targetDirections : Nonempty {x : V // x ≠ 0 ∧ P x = x}),
        (∃ ε : ℝ, 0 < ε ∧
          ∀ x : {x : V // x ≠ 0 ∧ P x = x},
            ε ≤ (LinearMap.toContinuousLinearMap (P.comp (Wₐ.comp P))).rayleighQuotient x) →
          (⨅ x : {x : V // x ≠ 0 ∧ P x = x},
              (LinearMap.toContinuousLinearMap (P.comp (W.comp P))).rayleighQuotient x) <
            ⨅ x : {x : V // x ≠ 0 ∧ P x = x},
              (LinearMap.toContinuousLinearMap
                (P.comp ((W + Wₐ).comp P))).rayleighQuotient x) ∧
    (let P : Matrix (Fin 2) (Fin 2) ℝ :=
        Matrix.diagonal fun i => if i = 0 then 1 else 0
      let W : Matrix (Fin 2) (Fin 2) ℝ := 0
      let Wₐ : Matrix (Fin 2) (Fin 2) ℝ :=
        Matrix.diagonal fun i => if i = 1 then 1 else 0
      Matrix.trace W < Matrix.trace (W + Wₐ) ∧
        P * W * P = P * (W + Wₐ) * P ∧
        ∃ x y : Fin 2 → ℝ,
          x 0 ≠ y 0 ∧
            (P * (W + Wₐ) * P).mulVec x =
              (P * (W + Wₐ) * P).mulVec y) ∧
    (∀ {X : Type u} {Current : Type v} {Response : Type w}
        {Target : Type z} {Candidate : Type*}
        [Fintype X] [Fintype Candidate] [Nonempty Candidate]
        (current : Concept X Current) (experiment : Candidate → Concept X Response)
        (target : X → Target),
      ∃ best : Candidate, ∀ candidate : Candidate,
        (experimentGain current (experiment candidate) target).ncard ≤
          (experimentGain current (experiment best) target).ncard) := by
  refine ⟨?_, ?_, ?_⟩
  · intro 𝕜 _ V _ _ _ P W Wₐ _ _ _ _ targetDirections
    rintro ⟨ε, εPositive, addedLowerBound⟩
    let baseline : V →L[𝕜] V :=
      LinearMap.toContinuousLinearMap (P.comp (W.comp P))
    let added : V →L[𝕜] V :=
      LinearMap.toContinuousLinearMap (P.comp (Wₐ.comp P))
    let combined : V →L[𝕜] V :=
      LinearMap.toContinuousLinearMap (P.comp ((W + Wₐ).comp P))
    have baselineBounded :
        BddBelow (Set.range fun x : {x : V // x ≠ 0 ∧ P x = x} =>
          baseline.rayleighQuotient x) := by
      refine ⟨-‖baseline‖, ?_⟩
      rintro value ⟨x, rfl⟩
      exact (abs_le.mp (baseline.rayleighQuotient_le_norm x)).1
    have combinedQuotient (x : {x : V // x ≠ 0 ∧ P x = x}) :
        combined.rayleighQuotient x =
          baseline.rayleighQuotient x + added.rayleighQuotient x := by
      have combinedEq : combined = baseline + added := by
        ext y
        simp [combined, baseline, added]
      rw [combinedEq]
      exact ContinuousLinearMap.rayleighQuotient_add baseline added
    have lowerBound :
        (⨅ x : {x : V // x ≠ 0 ∧ P x = x}, baseline.rayleighQuotient x) + ε ≤
          ⨅ x : {x : V // x ≠ 0 ∧ P x = x}, combined.rayleighQuotient x := by
      letI : Nonempty {x : V // x ≠ 0 ∧ P x = x} := targetDirections
      apply le_ciInf
      intro x
      rw [combinedQuotient x]
      exact add_le_add (ciInf_le baselineBounded x) (addedLowerBound x)
    exact lt_of_lt_of_le (lt_add_of_pos_right _ εPositive) lowerBound
  · dsimp only
    refine ⟨?_, ?_, ?_⟩
    · norm_num [Matrix.trace, Matrix.diagonal]
    · ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [Matrix.mul_apply, Matrix.diagonal]
    · refine ⟨Pi.single 0 1, 0, ?_, ?_⟩
      · simp
      · ext i
        fin_cases i <;>
          norm_num [Matrix.mulVec, Matrix.mul_apply, Matrix.diagonal]
  · intro X Current Response Target Candidate _ _ _ current experiment target
    classical
    obtain ⟨best, _, maximal⟩ :=
      Finset.exists_max_image Finset.univ
        (fun candidate : Candidate =>
          (experimentGain current (experiment candidate) target).ncard)
        Finset.univ_nonempty
    exact ⟨best, fun candidate => maximal candidate (Finset.mem_univ candidate)⟩

#print axioms weakest_target_direction_experiment_value

end D5.S3.ConceptDynamics.ExperimentDesign.WeakestTargetDirectionValue
