/- GID: D5/S3/Quantum/TensorNetworks/InteriorSpectralReduction
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/InteriorSpectralReduction
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: [mathlib/module/Mathlib.Algebra.MvPolynomial.Equiv]
   utility: none
   digest: Finite literal four-coefficient reduction of real spectral monomials. -/

import D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSInteriorSpectralNorm
import Mathlib.Algebra.MvPolynomial.Equiv

/-! The matrices act on monomials only; no noncommutative polynomial evaluation is used. -/
set_option autoImplicit false
noncomputable section
namespace D5.S3.Quantum.TensorNetworks.InteriorSpectralReduction
open Matrix MvPolynomial
open scoped Matrix BigOperators
abbrev R := MvPolynomial (Fin 13) ℝ
abbrev GPoly := MvPolynomial (Fin 2) R

def MX (A B : R) : Matrix (Fin 4) (Fin 4) R :=
  !![0,C (1/2)*A,C (1/2)*B,0;
     1,0,0,A; 0,0,0,B; 0,C (1/2),0,0]

def MY (A B : R) : Matrix (Fin 4) (Fin 4) R :=
  !![0,C (1/2)*B,-(C (1/2)*A),0;
     0,0,0,B; 1,0,0,-A; 0,0,C (1/2),0]

def coefficients (G : GPoly) (A B : R) (j : Fin 4) : R :=
  ∑ m ∈ G.support, G.coeff m *
    ((MX A B ^ (m 0) * MY A B ^ (m 1)) *ᵥ ![1,0,0,0]) j

section Evaluation
variable {T : Type*} [CommRing T]
variable (α : R →+* T) (A B : R) (x y r : T)

private lemma row_X
    (hxx : x*x=α (C (1/2))*(r+α A))
    (hxy : x*y=α (C (1/2))*α B)
    (hrx : r*x=α A*x+α B*y) :
    ![1,x,y,r] ᵥ* (MX A B).map α = x • ![1,x,y,r] := by
  simp only [one_div] at hxx hxy
  ext i
  fin_cases i <;> simp [MX,vecMul,dotProduct,Fin.sum_univ_succ,smul_eq_mul]
  · linear_combination -hxx
  · exact hxy.symm
  · linear_combination -hrx

private lemma row_Y
    (hyy : y*y=α (C (1/2))*(r-α A))
    (hxy : x*y=α (C (1/2))*α B)
    (hry : r*y=α B*x-α A*y) :
    ![1,x,y,r] ᵥ* (MY A B).map α = y • ![1,x,y,r] := by
  simp only [one_div] at hyy hxy
  ext i
  fin_cases i <;> simp [MY,vecMul,dotProduct,Fin.sum_univ_succ,smul_eq_mul]
  · linear_combination -hxy
  · linear_combination -hyy
  · linear_combination -hry

private lemma row_pow (M : Matrix (Fin 4) (Fin 4) T) (z : T)
    (h : ![1,x,y,r] ᵥ* M = z • ![1,x,y,r]) (n : ℕ) :
    ![1,x,y,r] ᵥ* M^n = z^n • ![1,x,y,r] := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ,← vecMul_vecMul,ih,smul_vecMul,h,smul_smul,pow_succ]

/-- Each finite monomial is reduced by the fixed ordered matrix powers. -/
theorem monomial_evaluation
    (hxx : x*x=α (C (1/2))*(r+α A))
    (hyy : y*y=α (C (1/2))*(r-α A))
    (hxy : x*y=α (C (1/2))*α B)
    (hrx : r*x=α A*x+α B*y) (hry : r*y=α B*x-α A*y)
    (i j : ℕ) :
    ![1,x,y,r] ⬝ᵥ ((MX A B ^ i * MY A B ^ j).map α *ᵥ ![1,0,0,0]) = x^i*y^j := by
  have hx := row_pow x y r _ x (row_X α A B x y r hxx hxy hrx) i
  have hy := row_pow x y r _ y (row_Y α A B x y r hyy hxy hry) j
  rw [dotProduct_mulVec,Matrix.map_mul,← vecMul_vecMul,Matrix.map_pow,Matrix.map_pow,
    hx,smul_vecMul,hy,smul_smul]
  simp [dotProduct,Fin.sum_univ_succ,smul_eq_mul]

/-- Finite support summation gives four literal base coefficients. -/
theorem coefficients_evaluation (G : GPoly)
    (hxx : x*x=α (C (1/2))*(r+α A))
    (hyy : y*y=α (C (1/2))*(r-α A))
    (hxy : x*y=α (C (1/2))*α B)
    (hrx : r*x=α A*x+α B*y) (hry : r*y=α B*x-α A*y) :
    eval₂ α ![x,y] G = α (coefficients G A B 0) + α (coefficients G A B 1)*x +
      α (coefficients G A B 2)*y + α (coefficients G A B 3)*r := by
  classical
  rw [eval₂_eq']
  simp only [coefficients,map_sum,map_mul,Finset.sum_mul,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro m hm
  have hh := monomial_evaluation α A B x y r hxx hyy hxy hrx hry (m 0) (m 1)
  simp only [Fin.prod_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  rw [← hh]
  simp only [RingHom.map_mulVec]
  have he0 : (α ∘ (![1,0,0,0] : Fin 4 → R)) = (![1,0,0,0] : Fin 4 → T) := by
    funext i; fin_cases i <;> simp
  rw [he0]
  simp [dotProduct,Fin.sum_univ_succ]
  ring
end Evaluation
end D5.S3.Quantum.TensorNetworks.InteriorSpectralReduction
