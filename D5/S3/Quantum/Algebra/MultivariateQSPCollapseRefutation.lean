/- GID: D5/S3/Quantum/Algebra/MultivariateQSPCollapseRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Algebra/MultivariateQSPCollapseRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Algebra/MultivariateQSPCollapseRefutation.claim; result=D5/S3/Quantum/Algebra/MultivariateQSPCollapseRefutation.result; claim=D5/S3/Quantum/Algebra/MultivariateQSPCollapseRefutation.claim
   digest: A two-step three-level signal protocol refutes Laneve--Wolf Conjecture 8. -/

import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.LinearAlgebra.Eigenspace.Matrix
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Quantum.Algebra.MultivariateQSPCollapseRefutation

open MvPolynomial Matrix
open scoped BigOperators

/-- Polynomial vectors of unit Euclidean norm on the two-dimensional torus. -/
def PolyState := {g : Fin 3 → MvPolynomial (Fin 2) ℂ //
  ∀ a b : ℂ, ‖a‖ = 1 → ‖b‖ = 1 →
    ∑ i, ‖eval ![a, b] (g i)‖ ^ 2 = 1}

/-- Dimension of the span of all coefficient vectors. -/
def effDim (g : Fin 3 → MvPolynomial (Fin 2) ℂ) : ℕ :=
  Module.finrank ℂ (Submodule.span ℂ (Set.range fun s => fun i => (g i).coeff s))

/-- The polynomial signal operator diag(1,a,b). -/
def signalStep (g : Fin 3 → MvPolynomial (Fin 2) ℂ) :
    Fin 3 → MvPolynomial (Fin 2) ℂ := ![g 0, X 0 * g 1, X 1 * g 2]

/-- The first j processing steps, numbered from A_1; stages past m are constant. -/
def stage {m : ℕ} (A : Fin m → specialUnitaryGroup (Fin 3) ℂ)
    (g : Fin 3 → MvPolynomial (Fin 2) ℂ) : ℕ → Fin 3 → MvPolynomial (Fin 2) ℂ
  | 0 => g
  | j + 1 => if hj : j < m then
      fun i => ∑ l, C ((A ⟨j, hj⟩).val i l) * signalStep (stage A g j) l
    else stage A g j

private def transferPrefix {m : ℕ} (A : Fin m → specialUnitaryGroup (Fin 3) ℂ)
    (a b : ℂ) : ℕ → Matrix (Fin 3) (Fin 3) ℂ
  | 0 => 1
  | j + 1 => if hj : j < m then
      (A ⟨j, hj⟩).val * diagonal ![1, a, b] * transferPrefix A a b j
    else transferPrefix A a b j

/-- The evaluated product A_m W ... A_1 W. -/
def transfer {m : ℕ} (A : Fin m → specialUnitaryGroup (Fin 3) ℂ)
    (a b : ℂ) : Matrix (Fin 3) (Fin 3) ℂ := transferPrefix A a b m

/-- The permissive subspace-isometry reading of Laneve--Wolf Conjecture 8. -/
def claim : Prop := ∀ (m : ℕ) (A : Fin m → specialUnitaryGroup (Fin 3) ℂ)
    (g : PolyState),
  effDim g.val ≤ 2 → effDim (stage A g.val m) ≤ 2 →
  (∀ j, 0 < j → j < m → 2 < effDim (stage A g.val j)) →
  ∃ (H H' : Submodule ℂ (Fin 3 → ℂ)) (U : H ≃ₗᵢ[ℂ] H') (k h : ℕ),
    2 ≤ Module.finrank ℂ H ∧
    ∀ a b : ℂ, ‖a‖ = 1 → ‖b‖ = 1 → ∀ x : H,
      transfer A a b *ᵥ (x : Fin 3 → ℂ) =
        (a ^ k * b ^ h) • (U x : Fin 3 → ℂ)

private def cycleOne : specialUnitaryGroup (Fin 3) ℂ :=
  ⟨!![0, 0, 1; 1, 0, 0; 0, 1, 0], by
    rw [mem_specialUnitaryGroup_iff, mem_unitaryGroup_iff]
    constructor
    · ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.star_eq_conjTranspose]
    · norm_num [Matrix.det_fin_three, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two]⟩

private def cycleTwo : specialUnitaryGroup (Fin 3) ℂ :=
  ⟨!![0, 1, 0; 0, 0, 1; 1, 0, 0], by
    rw [mem_specialUnitaryGroup_iff, mem_unitaryGroup_iff]
    constructor
    · ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.star_eq_conjTranspose]
    · norm_num [Matrix.det_fin_three, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two]⟩

private def protocol : Fin 2 → specialUnitaryGroup (Fin 3) ℂ := ![cycleOne, cycleTwo]

private def initial : Fin 3 → MvPolynomial (Fin 2) ℂ :=
  ![C (3 / 13), C (4 / 13), C (12 / 13) * X 0]

private def middle : Fin 3 → MvPolynomial (Fin 2) ℂ :=
  ![C (12 / 13) * (X 0 * X 1), C (3 / 13), C (4 / 13) * X 0]

private def finalState : Fin 3 → MvPolynomial (Fin 2) ℂ :=
  ![C (3 / 13) * X 0, C (4 / 13) * (X 0 * X 1), C (12 / 13) * (X 0 * X 1)]

private theorem initial_normalized (a b : ℂ) (ha : ‖a‖ = 1) (_hb : ‖b‖ = 1) :
    ∑ i, ‖eval ![a, b] (initial i)‖ ^ 2 = 1 := by
  norm_num [initial, Fin.sum_univ_succ, norm_mul, norm_div, ha]

private theorem stages : stage protocol initial 1 = middle ∧
    stage protocol initial 2 = finalState := by
  constructor <;> funext i <;> fin_cases i <;>
    simp [stage, protocol, cycleOne, cycleTwo, signalStep, initial, middle, finalState,
      Fin.sum_univ_succ] <;> ring

private theorem transfer_diagonal (a b : ℂ) :
    transfer protocol a b = diagonal ![a, a * b, b] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [transfer, transferPrefix, protocol, cycleOne, cycleTwo, Matrix.mul_apply,
      Fin.sum_univ_succ, diagonal_apply, Matrix.vecMul, dotProduct] <;> ring

end D5.S3.Quantum.Algebra.MultivariateQSPCollapseRefutation
