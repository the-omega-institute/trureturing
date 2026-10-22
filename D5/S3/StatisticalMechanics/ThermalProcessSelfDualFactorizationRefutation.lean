/- GID: D5/S3/StatisticalMechanics/ThermalProcessSelfDualFactorizationRefutation
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/ThermalProcessSelfDualFactorizationRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/StatisticalMechanics/ThermalProcessSelfDualFactorizationRefutation.claim; result=D5/S3/StatisticalMechanics/ThermalProcessSelfDualFactorizationRefutation.result; claim=D5/S3/StatisticalMechanics/ThermalProcessSelfDualFactorizationRefutation.claim
   digest: A self-dual irreducible extreme thermal process factors on proper sets of levels. -/

import Mathlib.Analysis.Convex.Extreme
import Mathlib.LinearAlgebra.Matrix.Stochastic
import Mathlib.Data.Matrix.Notation
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

set_option autoImplicit false

namespace D5.S3.StatisticalMechanics.ThermalProcessSelfDualFactorizationRefutation

open scoped BigOperators Matrix

noncomputable section

/-- Column-stochastic matrices preserving the Gibbs weights. -/
def thermalProcesses {d : ℕ} (g : Fin d → ℝ) : Set (Matrix (Fin d) (Fin d) ℝ) :=
  {T | T ∈ Matrix.colStochastic ℝ (Fin d) ∧ T *ᵥ g = g}

/-- A process acting trivially on at least one level. -/
def actsOnFewerLevels {d : ℕ} (T : Matrix (Fin d) (Fin d) ℝ) : Prop :=
  ∃ k, T k k = 1

/-- Detailed balance with respect to the Gibbs weights. -/
def selfDual {d : ℕ} (g : Fin d → ℝ) (T : Matrix (Fin d) (Fin d) ℝ) : Prop :=
  ∀ i j, T i j * g j = T j i * g i

/-- No nonempty proper set of levels gives a block diagonal decomposition. -/
def irreducible {d : ℕ} (T : Matrix (Fin d) (Fin d) ℝ) : Prop :=
  ¬ ∃ S : Finset (Fin d), S.Nonempty ∧ Sᶜ.Nonempty ∧
    ∀ i j, ((i ∈ S ∧ j ∉ S) ∨ (i ∉ S ∧ j ∈ S)) → T i j = 0

/-- The non-self-duality conjecture for irreducible extreme thermal products. -/
def claim : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (g : Fin d → ℝ),
    (∀ i, 0 < g i) → Function.Injective g →
    (∀ i, g i ≤ g ⟨0, by omega⟩) →
    ∀ A B C : Matrix (Fin d) (Fin d) ℝ,
      A ∈ Set.extremePoints ℝ (thermalProcesses g) →
      B ∈ Set.extremePoints ℝ (thermalProcesses g) →
      C ∈ Set.extremePoints ℝ (thermalProcesses g) →
      C = A * B → actsOnFewerLevels A → actsOnFewerLevels B →
      irreducible C → ¬ selfDual g C

private def g : Fin 5 → ℝ := ![8, 7, 4, 2, 3]

private def A : Matrix (Fin 5) (Fin 5) ℝ :=
  !![0, 1, 0, 1/2, 0;
     1/4, 0, 1, 1/2, 0;
     1/2, 0, 0, 0, 0;
     1/4, 0, 0, 0, 0;
     0, 0, 0, 0, 1]

private def B : Matrix (Fin 5) (Fin 5) ℝ :=
  !![1, 0, 0, 0, 0;
     0, 1/7, 1, 1, 0;
     0, 1/7, 0, 0, 1;
     0, 2/7, 0, 0, 0;
     0, 3/7, 0, 0, 0]

private def C : Matrix (Fin 5) (Fin 5) ℝ :=
  !![0, 2/7, 1, 1, 0;
     1/4, 2/7, 0, 0, 1;
     1/2, 0, 0, 0, 0;
     1/4, 0, 0, 0, 0;
     0, 3/7, 0, 0, 0]

private theorem weights :
    (∀ i, 0 < g i) ∧ Function.Injective g ∧ (∀ i, g i ≤ g 0) := by
  sorry

private theorem A_thermal : A ∈ thermalProcesses g := by
  sorry

private theorem B_thermal : B ∈ thermalProcesses g := by
  sorry

private theorem C_thermal : C ∈ thermalProcesses g := by
  sorry

private theorem extreme_of_support_unique {d : ℕ} {w : Fin d → ℝ}
    {M : Matrix (Fin d) (Fin d) ℝ} (hM : M ∈ thermalProcesses w)
    (hunique : ∀ X ∈ thermalProcesses w,
      (∀ i j, M i j = 0 → X i j = 0) → X = M) :
    M ∈ Set.extremePoints ℝ (thermalProcesses w) := by
  sorry

private theorem A_support_unique (X : Matrix (Fin 5) (Fin 5) ℝ)
    (hX : X ∈ thermalProcesses g) (hz : ∀ i j, A i j = 0 → X i j = 0) : X = A := by
  sorry

private theorem B_support_unique (X : Matrix (Fin 5) (Fin 5) ℝ)
    (hX : X ∈ thermalProcesses g) (hz : ∀ i j, B i j = 0 → X i j = 0) : X = B := by
  sorry

private theorem C_support_unique (X : Matrix (Fin 5) (Fin 5) ℝ)
    (hX : X ∈ thermalProcesses g) (hz : ∀ i j, C i j = 0 → X i j = 0) : X = C := by
  sorry

private theorem A_extreme : A ∈ Set.extremePoints ℝ (thermalProcesses g) := by
  sorry

private theorem B_extreme : B ∈ Set.extremePoints ℝ (thermalProcesses g) := by
  sorry

private theorem C_extreme : C ∈ Set.extremePoints ℝ (thermalProcesses g) := by
  sorry

private theorem product : C = A * B := by
  sorry

private theorem fewer_levels : actsOnFewerLevels A ∧ actsOnFewerLevels B := by
  sorry

private theorem C_irreducible : irreducible C := by
  sorry

private theorem C_selfDual : selfDual g C := by
  sorry

/-- The thermal-process non-self-duality conjecture fails in dimension five. -/
theorem result : ¬ claim := by
  sorry

end
end D5.S3.StatisticalMechanics.ThermalProcessSelfDualFactorizationRefutation
