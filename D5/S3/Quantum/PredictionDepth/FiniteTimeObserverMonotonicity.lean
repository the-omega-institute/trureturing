/- GID: D5/S3/Quantum/PredictionDepth/FiniteTimeObserverMonotonicity
   generality: G
   mirror-B: D5/B/S3/Quantum/PredictionDepth/FiniteTimeObserverMonotonicity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Heisenberg observation grows the visible span and shrinks its orthogonal residual. -/

import D5.S3.Quantum.Entanglement.BipartiteSectorDecomposition
import D5.S3.Quantum.Measurement.BasisMeasurementProjection
import Mathlib.Logic.Function.Iterate
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

noncomputable section

open scoped ComplexOrder InnerProductSpace Matrix

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.PredictionDepth.FiniteTimeObserverMonotonicity

open D5.S3.Quantum.Measurement.BasisMeasurementProjection
open D5.S3.Quantum.Entanglement.BipartiteSectorDecomposition

variable {d r : Nat}

local instance matrixNormedAddCommGroup :
    NormedAddCommGroup (Matrix (Fin d) (Fin d) ℂ) :=
  Matrix.toMatrixNormedAddCommGroup 1 Matrix.PosDef.one

local instance matrixComplexInnerProductSpace :
    InnerProductSpace ℂ (Matrix (Fin d) (Fin d) ℂ) :=
  Matrix.toMatrixInnerProductSpace 1 Matrix.PosSemidef.one

local instance matrixRealInnerProductSpace :
    InnerProductSpace ℝ (Matrix (Fin d) (Fin d) ℂ) :=
  InnerProductSpace.rclikeToReal ℂ (Matrix (Fin d) (Fin d) ℂ)

local instance hermitianRealInnerProductSpace :
    InnerProductSpace ℝ (HermitianSpace d) :=
  Submodule.innerProductSpace (HermitianSpace d)

/-- The finite visible span is built from the identity and all Heisenberg effect
iterates below the observation horizon; its orthogonal residual refines in the
opposite direction when the horizon is extended. -/
theorem finite_time_observer_monotonicity
    (heisenberg : HermitianSpace d →ₗ[ℝ] HermitianSpace d)
    (effects : Fin (r + 1) → HermitianSpace d) :
    ∀ n : Nat,
      let visible : Submodule ℝ (HermitianSpace d) :=
        Submodule.span ℝ (Set.insert (identityHermitian d)
          {effect | ∃ t : Nat, ∃ i : Fin (r + 1),
            t < n ∧ effect = (heisenberg^[t]) (effects i)})
      let nextVisible : Submodule ℝ (HermitianSpace d) :=
        Submodule.span ℝ (Set.insert (identityHermitian d)
          {effect | ∃ t : Nat, ∃ i : Fin (r + 1),
            t < n + 1 ∧ effect = (heisenberg^[t]) (effects i)})
      visible ≤ nextVisible ∧ nextVisibleᗮ ≤ visibleᗮ := by
  intro n
  dsimp
  have hVisible :
      Submodule.span ℝ (Set.insert (identityHermitian d)
        {effect | ∃ t : Nat, ∃ i : Fin (r + 1),
          t < n ∧ effect = (heisenberg^[t]) (effects i)}) ≤
      Submodule.span ℝ (Set.insert (identityHermitian d)
        {effect | ∃ t : Nat, ∃ i : Fin (r + 1),
          t < n + 1 ∧ effect = (heisenberg^[t]) (effects i)}) := by
    apply Submodule.span_mono
    intro effect heffect
    rcases Set.mem_insert_iff.mp heffect with hidentity | hiterate
    · exact Set.mem_insert_iff.mpr (Or.inl hidentity)
    · apply Set.mem_insert_iff.mpr
      right
      rcases hiterate with ⟨t, i, ht, heffect⟩
      exact ⟨t, i, ht.trans (Nat.lt_succ_self n), heffect⟩
  exact ⟨hVisible, Submodule.orthogonal_le hVisible⟩

#print axioms finite_time_observer_monotonicity

end D5.S3.Quantum.PredictionDepth.FiniteTimeObserverMonotonicity
