/- GID: D5/S3/Quantum/Recovery/BurriReplacementDecoder
   generality: I
   mirror-B: D5/B/S3/Quantum/Recovery/BurriReplacementDecoder
   mirror-E: none(waiver:unfinished-two-direction-comparison)
   anchors: []
   utility: none
   digest: Literal Appendix A objects for a qubit replacement channel and its decoder comparison. -/

import D5.S3.Quantum.Recovery.ReferencePetzChannel
import D5.S3.Quantum.Foundation.FiniteDensityPurification
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Foundation.FiniteKrausChannel

namespace D5.S3.Quantum.Recovery.BurriReplacementDecoder

abbrev A := Fin 2
abbrev B := Fin 1
/-- The source environment is literally A times a copy of B. -/
abbrev E := A × B
abbrev P := A × E

def rho : Matrix A A ℂ := Matrix.diagonal ![2 / 3, 1 / 3]
def weight : A → ℝ := ![Real.sqrt 2 / Real.sqrt 3, 1 / Real.sqrt 3]
/-- The reference purification, also used as the allowed fixed R'A' ancilla. -/
def psi (p : P) : ℂ := if p.1 = p.2.1 then (weight p.1 : ℂ) else 0
def X : Matrix P P ℂ := Matrix.vecMulVec psi (star psi)
def sqrtQ : Matrix P P ℂ := Matrix.diagonal fun p =>
  if p.1 = p.2.1 then (if p.1 = 0 then 2 / 3 else 1 / 3)
  else (Real.sqrt 2 : ℂ) / 3
/-- Appendix A.6, with its transpose in the eigenbases of both marginals. -/
def M : Matrix P P ℂ := (sqrtQ * X).transpose

/-- A source right-polar unitary, identity on the two uncorrelated basis vectors. -/
def U : Matrix P P ℂ := fun p q =>
  if p.1 = p.2.1 ∧ q.1 = q.2.1 then
    if p.1 = q.1 then 5 / (3 * (Real.sqrt 3 : ℂ))
    else if p.1 = 0 then (Real.sqrt 2 : ℂ) / (3 * (Real.sqrt 3 : ℂ))
    else -(Real.sqrt 2 : ℂ) / (3 * (Real.sqrt 3 : ℂ))
  else if p = q then 1 else 0

/-- Replacement-channel Stinespring isometry, with the full source environment. -/
def V : Matrix (B × E) A ℂ := fun p i => if p.2.1 = i then 1 else 0
def noiseKraus (e : E) : Matrix B A ℂ := fun b i => V (b, e) i
/-- D' adjoins the fixed unit ancilla psi; B is one dimensional. -/
def prepare : Matrix P B ℂ := fun p _ => psi p
/-- In these literal coordinates W is the identity. -/
def W : Matrix P P ℂ := 1
/-- Appendix A.11, retaining all source environment labels. -/
def sourceKraus (e : E) : Matrix A P ℂ := fun k p => (U * W) (k, e) p
/-- The actual composite D'' D' Kraus operators, before any fidelity evaluation. -/
def swKraus (e : E) : Matrix A B ℂ := sourceKraus e * prepare
def petzKraus (e : E) : Matrix A B ℂ :=
  Matrix.diagonal (fun i => (weight i : ℂ)) * (noiseKraus e)ᴴ

private theorem sqrt_facts :
    (Real.sqrt 2) ^ 2 = 2 ∧ (Real.sqrt 3) ^ 2 = 3 ∧ Real.sqrt 3 ≠ 0 := by
  exact ⟨Real.sq_sqrt (by norm_num), Real.sq_sqrt (by norm_num),
    ne_of_gt (Real.sqrt_pos.2 (by norm_num))⟩

theorem psi_normalized : (∑ p : P, star (psi p) * psi p) = 1 := by
  obtain ⟨h2, h3, ht⟩ := sqrt_facts
  norm_num [psi, weight, Fintype.sum_prod_type, Fin.sum_univ_two,
    Fin.sum_univ_one, Complex.ext_iff, Complex.div_re, Complex.div_im]
  <;> field_simp <;> nlinarith

theorem source_isometry : Vᴴ * V = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [V, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.one_apply, Fintype.sum_prod_type, Fin.sum_univ_two, Fin.sum_univ_one]

theorem source_unitary : Uᴴ * U = 1 ∧ U * Uᴴ = 1 := by
  obtain ⟨h2, h3, ht⟩ := sqrt_facts
  constructor <;> ext ⟨i, j, b⟩ ⟨k, l, c⟩
  all_goals fin_cases i <;> fin_cases j <;> fin_cases b <;>
    fin_cases k <;> fin_cases l <;> fin_cases c <;>
    norm_num [U, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply,
      Fintype.sum_prod_type, Fin.sum_univ_two, Fin.sum_univ_one,
      Complex.ext_iff, Complex.div_re, Complex.div_im]
  all_goals field_simp <;> nlinarith

theorem source_polar_product : M * U = (1 / (Real.sqrt 3 : ℂ)) • X := by
  obtain ⟨h2, h3, ht⟩ := sqrt_facts
  ext ⟨i, j, b⟩ ⟨k, l, c⟩
  fin_cases i <;> fin_cases j <;> fin_cases b <;>
    fin_cases k <;> fin_cases l <;> fin_cases c <;>
    norm_num [M, sqrtQ, X, psi, weight, U, Matrix.mul_apply,
      Matrix.transpose_apply, Matrix.vecMulVec_apply, Matrix.smul_apply,
      Matrix.diagonal_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
      Fin.sum_univ_one, Complex.ext_iff, Complex.div_re, Complex.div_im]
  all_goals field_simp <;> nlinarith

#print axioms psi_normalized
#print axioms source_isometry
#print axioms source_unitary
#print axioms source_polar_product

end D5.S3.Quantum.Recovery.BurriReplacementDecoder
