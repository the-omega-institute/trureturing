/- GID: D5/S3/Quantum/Dynamics/FibonacciModFourClock
   generality: S
   mirror-B: D5/B/S3/Quantum/Dynamics/FibonacciModFourClock
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The literal mod-four digit lift has an exact four-energy clock polynomial. -/

import D5.S3.Quantum.Dynamics.EnergyEigenstateStationarity
import D5.S3.Quantum.Dynamics.ProjectionProbabilityFlow
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open scoped Matrix.Norms.L2Operator

namespace D5.S3.Quantum.Dynamics.FibonacciModFourClock

open D5.S3.Quantum.Dynamics.ProjectionProbabilityFlow
open D5.S3.Quantum.Dynamics.EnergyEigenstateStationarity

local instance : NormedAddCommGroup (Matrix (Fin 4 × Fin 4) (Fin 4 × Fin 4) ℂ) :=
  Matrix.instL2OpNormedAddCommGroup
local instance : NormedSpace ℂ (Matrix (Fin 4 × Fin 4) (Fin 4 × Fin 4) ℂ) :=
  Matrix.instL2OpNormedSpace
local instance : NormedRing (Matrix (Fin 4 × Fin 4) (Fin 4 × Fin 4) ℂ) :=
  Matrix.instL2OpNormedRing
local instance : NormedAlgebra ℂ (Matrix (Fin 4 × Fin 4) (Fin 4 × Fin 4) ℂ) :=
  Matrix.instL2OpNormedAlgebra
local instance : NormedAlgebra ℚ (Matrix (Fin 4 × Fin 4) (Fin 4 × Fin 4) ℂ) :=
  NormedAlgebra.restrictScalars ℚ ℂ _

/-- Each four-label factor encodes a bit pair by the value `2 b₀ + b₁`.
The joint pair is the standard split `a + 2 h` in each mod-four coordinate. -/
def digitMap (z : Fin 4 × Fin 4) : Fin 4 × Fin 4 :=
  (⟨2 * (z.1.val % 2) + ((z.1.val / 2 + z.1.val % 2) % 2), by omega⟩,
   ⟨2 * (z.2.val % 2) +
      ((z.2.val / 2 + z.2.val % 2 + (z.1.val / 2 + z.1.val % 2) / 2) % 2), by omega⟩)

/-- The actual standard-digit permutation, with its inverse given by five steps. -/
def digitPermutation : Equiv.Perm (Fin 4 × Fin 4) where
  toFun := digitMap
  invFun := digitMap^[5]
  left_inv := by
    have h : ∀ z : Fin 4 × Fin 4, digitMap^[5] (digitMap z) = z := by decide
    exact h
  right_inv := by
    have h : ∀ z : Fin 4 × Fin 4, digitMap (digitMap^[5] z) = z := by decide
    exact h

/-- The column-action matrix sends `|a,h⟩` to the literal digit-map output. -/
def U : Matrix (Fin 4 × Fin 4) (Fin 4 × Fin 4) ℂ :=
  (Matrix.permMatrixHom (R := ℂ)) digitPermutation

/-- The source Hamiltonian `2 I - U - U†`. -/
def L : Matrix (Fin 4 × Fin 4) (Fin 4 × Fin 4) ℂ := (2 : ℂ) • 1 - U - star U

/-- The source gate is the existing Hamiltonian exponential, at this one time. -/
def clock (Delta : ℝ) : Matrix (Fin 4 × Fin 4) (Fin 4 × Fin 4) ℂ :=
  hamiltonianPropagator L Delta

/-- The four energy labels are `0,1,3,4`. -/
def energy (r : Fin 4) : ℂ := ![0, 1, 3, 4] r

/-- The four polynomial spectral pieces of the actual digit permutation. -/
def spectralPiece (r : Fin 4) : Matrix (Fin 4 × Fin 4) (Fin 4 × Fin 4) ℂ :=
  (1 / 6 : ℂ) • ![
    1 + U + U ^ 2 + U ^ 3 + U ^ 4 + U ^ 5,
    (2 : ℂ) • 1 + U - U ^ 2 - (2 : ℂ) • U ^ 3 - U ^ 4 + U ^ 5,
    (2 : ℂ) • 1 - U - U ^ 2 + (2 : ℂ) • U ^ 3 - U ^ 4 - U ^ 5,
    1 - U + U ^ 2 - U ^ 3 + U ^ 4 - U ^ 5] r

/-- The exact source exponential is a polynomial in the actual lift.
The spectral construction uses the whole sixteen-dimensional space. -/
theorem fixed_clock_formula (Delta : ℝ) :
    U ^ 6 = 1 ∧
    clock Delta =
      let x := Complex.exp (-Complex.I * (Delta : ℂ))
      let Pplus := (1 / 2 : ℂ) • (1 + U ^ 3)
      let Pminus := (1 / 2 : ℂ) • (1 - U ^ 3)
      let A := (1 + 2 * x ^ 3) / 3
      let B := x * (2 + x ^ 3) / 3
      let C := (1 - x ^ 3) / 3
      A • Pplus + B • Pminus +
        C • (U * (Pplus + x • Pminus)) +
        C • (U ^ 2 * (Pplus - x • Pminus)) := by
  have hp6 : digitPermutation ^ 6 = 1 := by
    apply Equiv.ext
    intro z
    have h : ∀ z : Fin 4 × Fin 4, digitMap^[6] z = z := by decide
    rw [Equiv.Perm.coe_pow]
    change digitMap^[6] z = z
    exact h z
  have h6 : U ^ 6 = 1 := by
    rw [U, ← map_pow, hp6, map_one]
  have hu : star U * U = 1 ∧ U * star U = 1 := by
    change star (digitPermutation⁻¹.permMatrix ℂ) * digitPermutation⁻¹.permMatrix ℂ = 1 ∧
      digitPermutation⁻¹.permMatrix ℂ * star (digitPermutation⁻¹.permMatrix ℂ) = 1
    simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_permMatrix,
      inv_inv, ← Matrix.permMatrix_mul, inv_mul_cancel, mul_inv_cancel,
      Matrix.permMatrix_one, and_self]
  have hstar : star U = U ^ 5 := by
    calc
      star U = star U * U ^ 6 := by rw [h6, mul_one]
      _ = U ^ 5 := by rw [pow_succ', ← mul_assoc, hu.1, one_mul]
  have h7 : U ^ 7 = U := by rw [pow_succ, h6, one_mul]
  have h8 : U ^ 8 = U ^ 2 := by rw [pow_succ, h7, pow_two]
  have h9 : U ^ 9 = U ^ 3 := by rw [pow_succ, h8, ← pow_succ]
  have h10 : U ^ 10 = U ^ 4 := by rw [pow_succ, h9, ← pow_succ]
  have h2 : U * U = U ^ 2 := (pow_two U).symm
  have heigen : ∀ r, L * spectralPiece r = energy r • spectralPiece r := by
    intro r
    fin_cases r <;>
      simp [spectralPiece, energy, L, hstar,
        mul_add, mul_sub, sub_mul,
        one_mul, mul_one, smul_smul, ← pow_add, ← pow_succ', ← pow_succ, h2,
        h6, h7, h8, h9, h10] <;>
      module
  have hsum : ∑ r, spectralPiece r = 1 := by
    simp [Fin.sum_univ_succ, spectralPiece]
    module
  have hexp (r : Fin 4) : clock Delta * spectralPiece r =
      Complex.exp ((-Complex.I * (Delta : ℂ)) * energy r) • spectralPiece r := by
    have hG : (Delta • hamiltonianGenerator L) * spectralPiece r =
        ((-Complex.I * (Delta : ℂ)) * energy r) • spectralPiece r := by
      rw [hamiltonianGenerator, smul_mul_assoc, smul_mul_assoc, heigen]
      ext i j
      simp only [Matrix.smul_apply, Complex.real_smul, smul_eq_mul]
      ring
    ext i j
    exact congrFun (exp_mulVec_of_eigenvector (Delta • hamiltonianGenerator L)
      (fun k => spectralPiece r k j) _
      (congrArg (fun Q => fun k => Q k j) hG)) i
  let x := Complex.exp (-Complex.I * (Delta : ℂ))
  have hphase (r : Fin 4) :
      Complex.exp ((-Complex.I * (Delta : ℂ)) * energy r) = x ^ (![0, 1, 3, 4] r : ℕ) := by
    have hcast : energy r = (((![0, 1, 3, 4] r : ℕ) : ℂ)) := by
      fin_cases r <;> norm_num [energy]
    rw [hcast, mul_comm, Complex.exp_nat_mul]
  have hresolution : clock Delta = ∑ r, (x ^ (![0, 1, 3, 4] r : ℕ)) • spectralPiece r := by
    calc
      clock Delta = clock Delta * (∑ r, spectralPiece r) := by rw [hsum, mul_one]
      _ = _ := by simp only [Finset.mul_sum, hexp, hphase]
  refine ⟨h6, ?_⟩
  rw [hresolution]
  dsimp only
  simp [Fin.sum_univ_succ, spectralPiece, x, pow_zero, pow_one, one_smul, mul_add, mul_sub,
    smul_add, smul_sub, smul_smul, ← pow_add, ← pow_succ',
    mul_one]
  module

#print axioms fixed_clock_formula

end D5.S3.Quantum.Dynamics.FibonacciModFourClock
