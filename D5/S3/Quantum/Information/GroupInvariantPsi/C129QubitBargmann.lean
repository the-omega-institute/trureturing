/- GID: D5/S3/Quantum/Information/GroupInvariantPsi/C129QubitBargmann
   generality: G
   mirror-B: D5/B/S3/Quantum/Information/GroupInvariantPsi/C129QubitBargmann
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The ordered qubit Bargmann trace is the Bloch scalar-plus-oriented-volume formula. -/

import Mathlib
import D5.S3.Quantum.PureState.PureStateHandshake

open Matrix
open scoped BigOperators Matrix

namespace D5.S3.Quantum.Information.GroupInvariantPsi.C129QubitBargmann

noncomputable section

def pauliCombination (r : Fin 3 → ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![((r 2 : ℝ) : ℂ), ((r 0 : ℝ) : ℂ) - ((r 1 : ℝ) : ℂ) * Complex.I;
      ((r 0 : ℝ) : ℂ) + ((r 1 : ℝ) : ℂ) * Complex.I, -((r 2 : ℝ) : ℂ)]

def qubitProjector (r : Fin 3 → ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (1 / 2 : ℂ) • (1 + pauliCombination r)

def tripleBargmann (r₁ r₂ r₃ : Fin 3 → ℝ) : ℂ :=
  Matrix.trace (qubitProjector r₁ * qubitProjector r₂ * qubitProjector r₃)

abbrev QubitState := Fin 2 → ℂ

open D5.S3.Quantum.PureState.PureStateHandshake

def stateProjector (v : QubitState) : Matrix (Fin 2) (Fin 2) ℂ :=
  rankOneDensity v

def vZero : QubitState := ![1, 0]

def vPlus : QubitState := ![(1 : ℂ) / Real.sqrt 2, (1 : ℂ) / Real.sqrt 2]

def vYPlus : QubitState := ![(1 : ℂ) / Real.sqrt 2, Complex.I / Real.sqrt 2]

def vYMinus : QubitState := ![(1 : ℂ) / Real.sqrt 2, -Complex.I / Real.sqrt 2]

def stateTripleBargmann (v₁ v₂ v₃ : QubitState) : ℂ :=
  Matrix.trace (stateProjector v₁ * stateProjector v₂ * stateProjector v₃)

theorem triple_bargmann_bloch (r₁ r₂ r₃ : Fin 3 → ℝ) :
    tripleBargmann r₁ r₂ r₃ =
      (((1 + r₁ ⬝ᵥ r₂ + r₂ ⬝ᵥ r₃ + r₃ ⬝ᵥ r₁ : ℝ) : ℂ) / 4) +
        (((r₁ ⬝ᵥ (r₂ ⨯₃ r₃) : ℝ) : ℂ) * Complex.I / 4) := by
  simp [tripleBargmann, qubitProjector, pauliCombination, Matrix.trace,
    Matrix.mul_apply, Fin.sum_univ_two, dotProduct, crossProduct, Fin.sum_univ_three]
  ring_nf
  simp [Complex.I_sq]
  ring

theorem explicit_qubit_orientation :
    tripleBargmann ![(0 : ℝ), 0, 1] ![1, 0, 0] ![0, 1, 0] =
        (1 + Complex.I) / 4 ∧
      tripleBargmann ![(0 : ℝ), 0, 1] ![1, 0, 0] ![0, -1, 0] =
        (1 - Complex.I) / 4 := by
  constructor
  · rw [triple_bargmann_bloch]
    norm_num [dotProduct, crossProduct, Fin.sum_univ_three]
    ring
  · rw [triple_bargmann_bloch]
    norm_num [dotProduct, crossProduct, Fin.sum_univ_three]
    ring

theorem explicit_state_orientation :
    stateTripleBargmann vZero vPlus vYPlus = (1 + Complex.I) / 4 ∧
      stateTripleBargmann vZero vPlus vYMinus = (1 - Complex.I) / 4 := by
  constructor <;>
    simp [stateTripleBargmann, stateProjector, rankOneDensity, Matrix.vecMulVec,
      Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two, Pi.star_apply,
      vZero, vPlus, vYPlus, vYMinus]
  · have hs : (Real.sqrt 2 : ℝ) ^ 2 = 2 := by norm_num
    have hs0 : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (ne_of_gt (Real.sqrt_pos.2 (by norm_num)))
    have hs2 : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
      rw [← Complex.ofReal_pow, hs]
      norm_num
    field_simp [hs0]
    rw [show ((Real.sqrt 2 : ℝ) : ℂ) ^ 4 = 4 by
      calc
        ((Real.sqrt 2 : ℝ) : ℂ) ^ 4 = (((Real.sqrt 2 : ℝ) : ℂ) ^ 2) ^ 2 := by ring
        _ = (2 : ℂ) ^ 2 := by rw [hs2]
        _ = 4 := by norm_num]
    ring
  · have hs : (Real.sqrt 2 : ℝ) ^ 2 = 2 := by norm_num
    have hs0 : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (ne_of_gt (Real.sqrt_pos.2 (by norm_num)))
    have hs2 : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
      rw [← Complex.ofReal_pow, hs]
      norm_num
    field_simp [hs0]
    rw [show ((Real.sqrt 2 : ℝ) : ℂ) ^ 4 = 4 by
      calc
        ((Real.sqrt 2 : ℝ) : ℂ) ^ 4 = (((Real.sqrt 2 : ℝ) : ℂ) ^ 2) ^ 2 := by ring
        _ = (2 : ℂ) ^ 2 := by rw [hs2]
        _ = 4 := by norm_num]
    ring
end
end D5.S3.Quantum.Information.GroupInvariantPsi.C129QubitBargmann
