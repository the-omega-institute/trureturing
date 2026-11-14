import D5.S3.Quantum.Measurements.RelevantSpaceQuantumKac
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

open Matrix
open scoped BigOperators

private abbrev Mat := Matrix (Fin 3) (Fin 3) ℂ
private def initial : Mat := !![1, 0, 0; 0, 0, 0; 0, 0, 0]
private def relevant : Mat := !![1, 0, 0; 0, 1, 0; 0, 0, 0]
private def branches : Fin 5 → Mat := ![
  !![1/2, 0, 0; 0, 1/2, 0; 0, 0, 0],
  !![1/2, 0, 0; 0, 1/2, 0; 0, 0, 0],
  !![0, 1/2, 0; 1/2, 0, 0; 0, 0, 0],
  !![0, 1/2, 0; 1/2, 0, 0; 0, 0, 0],
  !![0, 0, 1; 0, 0, 0; 0, 0, 0]]
private def channel (X : Mat) : Mat := ∑ a, branches a * X * (branches a)ᴴ
private def noReturn (X : Mat) : Mat := (1 - initial) * channel X * (1 - initial)

example : (∑ a, (branches a)ᴴ * branches a) = (1 : Mat) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [branches, Matrix.mul_apply, Fin.sum_univ_succ]

example : channel relevant = relevant := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [channel, branches, relevant, Matrix.mul_apply, Fin.sum_univ_succ]

example : channel (1 : Mat) ≠ 1 := by
  intro h
  have hz := congrArg (fun X : Mat => X 0 0) h
  norm_num [channel, branches, Matrix.mul_apply, Fin.sum_univ_succ] at hz

example : relevant ≠ (1 : Mat) := by
  intro h
  have hz := congrArg (fun X : Mat => X 2 2) h
  norm_num [relevant] at hz

example : (initial * channel initial).trace = 1 / 2 ∧
    (initial * channel (noReturn initial)).trace = 1 / 4 ∧
    (initial * channel (channel initial)).trace = 1 / 2 := by
  norm_num [initial, noReturn, channel, branches, Matrix.trace,
    Matrix.mul_apply, Fin.sum_univ_succ]
