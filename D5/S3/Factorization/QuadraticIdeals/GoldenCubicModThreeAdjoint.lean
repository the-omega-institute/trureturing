/- GID: D5/S3/Factorization/QuadraticIdeals/GoldenCubicModThreeAdjoint
   generality: I
   mirror-B: D5/B/S3/Factorization/QuadraticIdeals/GoldenCubicModThreeAdjoint
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: Four explicit special-linear conjugations certify irreducibility of the mod-three adjoint module. -/

import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.FinTwo
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

set_option autoImplicit false

namespace D5.S3.Factorization.QuadraticIdeals.GoldenCubicModThreeAdjoint

abbrev PairMat := Matrix (Fin 2) (Fin 2) (ZMod 3)
abbrev Tangent := ZMod 3 × ZMod 3 × ZMod 3

def slMat (v : Tangent) : PairMat :=
  !![v.1,v.2.1;v.2.2,-v.1]

def traceZeroCoords (A : PairMat) : Tangent :=
  (A 0 0,A 0 1,A 1 0)

def slConj (G X : PairMat) : PairMat :=
  G * X * !![G 1 1,-G 0 1;-G 1 0,G 0 0]

def act (G : PairMat) (v : Tangent) : Tangent := traceZeroCoords (slConj G (slMat v))

def g (i : Fin 4) : PairMat :=
  ![!![1,1;0,1],!![1,0;1,1],!![0,2;1,0],!![2,1;1,1]] i

def rowMat (u v w : Tangent) : Matrix (Fin 3) (Fin 3) (ZMod 3) :=
  !![u.1,u.2.1,u.2.2;v.1,v.2.1,v.2.2;w.1,w.2.1,w.2.2]

def vol (u v w : Tangent) : ZMod 3 :=
  u.1*(v.2.1*w.2.2-v.2.2*w.2.1) -
  u.2.1*(v.1*w.2.2-v.2.2*w.1) +
  u.2.2*(v.1*w.2.1-v.2.1*w.1)

theorem vol_eq_det (u v w : Tangent) : vol u v w = (rowMat u v w).det := by
  simp [vol,rowMat,Matrix.det_fin_three]
  ring

theorem selected_sl (i : Fin 4) : (g i).det = 1 := by
  fin_cases i <;> decide

theorem trace_zero_reconstruction (A : PairMat) (h : A.trace = 0) :
    slMat (traceZeroCoords A) = A := by
  have hd : - A 0 0 = A 1 1 := by have hh := h; rw [Matrix.trace_fin_two] at hh; linear_combination -hh
  ext i j
  fin_cases i <;> fin_cases j <;> simp [slMat, traceZeroCoords, hd]

theorem adjugate_is_inverse (G : PairMat) (h : G.det = 1) :
    G * !![G 1 1,-G 0 1;-G 1 0,G 0 0] = 1 := by
  rw [Matrix.det_fin_two] at h
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply,Fin.sum_univ_two] <;> grind

/-- For every nonzero tangent vector, its own row and two conjugate rows
selected from four fixed SL2 matrices have nonzero determinant. -/
theorem adjoint_nonzero_orbit_basis :
    ∀ v : Tangent, v ≠ (0,0,0) → ∃ i j : Fin 4, (rowMat v (act (g i) v) (act (g j) v)).det ≠ 0 := by
  simp_rw [← vol_eq_det]
  decide

/-- In particular the two elementary conjugations have no common fixed
nonzero trace-zero coordinate vector. -/
theorem adjoint_no_invariants :
    ∀ v : Tangent, act (g 0) v = v → act (g 1) v = v → v = (0,0,0) := by decide

/-- The rank certificate gives actual linear independence of the three
orbit rows, not only a scalar test. Their vectors lie in the 3-dimensional
trace-zero-coordinate module. -/
theorem adjoint_nonzero_orbit_independent (v : Tangent) (hv : v ≠ (0,0,0)) :
    ∃ i j : Fin 4, LinearIndependent (ZMod 3) (rowMat v (act (g i) v) (act (g j) v)) := by
  obtain ⟨i,j,h⟩ := adjoint_nonzero_orbit_basis v hv
  exact ⟨i,j,Matrix.linearIndependent_rows_of_det_ne_zero h⟩

def tangentVector (w : Tangent) : Fin 3 → ZMod 3 := ![w.1,w.2.1,w.2.2]

/-- Invariance under the four explicitly certified determinant-one
conjugations already forces the zero or entire trace-zero subspace. -/
theorem adjoint_irreducible_of_invariant (S : Submodule (ZMod 3) (Fin 3 → ZMod 3))
    (hS : ∀ (i : Fin 4) (w : Tangent), tangentVector w ∈ S → tangentVector (act (g i) w) ∈ S) :
    S = ⊥ ∨ S = ⊤ := by
  by_cases hh : S = ⊥
  · exact Or.inl hh
  right
  obtain ⟨v,hv,hvn⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hh
  let w : Tangent := (v 0,v 1,v 2)
  have hw : tangentVector w = v := by
    ext k
    fin_cases k <;> rfl
  have hwn : w ≠ (0,0,0) := by
    intro h
    apply hvn
    rw [← hw,h]
    ext k
    fin_cases k <;> rfl
  obtain ⟨i,j,hli⟩ := adjoint_nonzero_orbit_independent w hwn
  have hc : Fintype.card (Fin 3) = Module.finrank (ZMod 3) (Fin 3 → ZMod 3) := by
    rw [Module.finrank_fintype_fun_eq_card]
  have hspan := hli.span_eq_top_of_card_eq_finrank hc
  apply top_unique
  rw [← hspan]
  apply Submodule.span_le.mpr
  rintro _ ⟨k,rfl⟩
  have hmem : tangentVector w ∈ S := by rwa [hw]
  fin_cases k
  · exact hmem
  · exact hS i w hmem
  · exact hS j w hmem

end D5.S3.Factorization.QuadraticIdeals.GoldenCubicModThreeAdjoint
