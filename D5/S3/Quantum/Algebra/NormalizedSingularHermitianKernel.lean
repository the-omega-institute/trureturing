/-
  Unfrozen normalized singular-Hermitian coefficient-kernel component.

  This file records the normalized matrix identities used by the width-three
  rank-two kernel classification.  The geometric graph trichotomy is kept as
  the explicit remaining WIP proposition below; the determinant, shear, final
  unitary, and congruence transport identities are kernel checked here.
-/

import Mathlib

/-!
# Normalized singular Hermitian kernel identities

The declaration `normalizedGraphTrichotomy` is the faithful normalized
classification target.  The finite-dimensional graph extraction that proves
it is intentionally left open in this WIP; all displayed algebraic transports
and the primitive zero-graph consumer below are compiled.
-/

noncomputable section

open Matrix
open scoped BigOperators ComplexConjugate

namespace D5.S3.Quantum.Algebra.NormalizedSingularHermitianKernel

abbrev M := Matrix (Fin 3) (Fin 3) ℂ

def D : M := !![(1 : ℂ), 0, 0; 0, -1, 0; 0, 0, 0]

def hermitianMatrix (a b : ℝ) (z u v : ℂ) : M :=
  !![(a : ℂ), z, u; conj z, (b : ℂ), v; conj u, conj v, 0]

def shear (p : ℂ) : M := !![1, 0, 0; 0, 1, 0; 0, -p, 1]

def finalUnitary : M :=
  let r : ℝ := Real.sqrt 2
  !![((r⁻¹ : ℝ) : ℂ), Complex.I * ((r⁻¹ : ℝ) : ℂ), 0;
     ((r⁻¹ : ℝ) : ℂ), -Complex.I * ((r⁻¹ : ℝ) : ℂ), 0;
     0, 0, Complex.I]

def skew3 : Set M :=
  {A | ∃ x y z : ℝ,
      A = !![0, (x : ℂ), (y : ℂ); (-x : ℂ), 0, (z : ℂ);
        (-y : ℂ), (-z : ℂ), 0]}

def iSkew3 : Set M :=
  {A | ∃ x y z : ℝ,
      A = Complex.I • !![0, (x : ℂ), (y : ℂ); (-x : ℂ), 0, (z : ℂ);
        (-y : ℂ), (-z : ℂ), 0]}

def e3 : Fin 3 → ℂ := ![0, 0, 1]

def neutralGenerator (c : ℂ) : Fin 3 → ℂ := ![1, -c, 0]

theorem hermitianMatrix_isHermitian (a b : ℝ) (z u v : ℂ) :
    (hermitianMatrix a b z u v).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [hermitianMatrix, Matrix.conjTranspose_apply]

theorem determinant_pencil (a b : ℝ) (z u v : ℂ) (t : ℝ) :
    (D + (t : ℂ) • hermitianMatrix a b z u v).det =
      -(t : ℂ) * 0 +
        (t : ℂ) ^ 2 *
          ((0 : ℂ) * ((b : ℂ) - (a : ℂ)) + conj u * u - conj v * v) +
        (t : ℂ) ^ 3 *
          ((a : ℂ) * (b : ℂ) * 0 - (a : ℂ) * (conj v * v) -
            (b : ℂ) * (conj u * u) + z * v * conj u +
            conj z * conj v * u - (0 : ℂ) * (z * conj z)) := by
  rw [Matrix.det_fin_three]
  simp [D, hermitianMatrix, Matrix.add_apply, Matrix.smul_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
  ring

theorem shear_identity (a b : ℝ) (p u : ℂ)
    (hsum : (a + b : ℂ) = conj p * u + p * conj u) :
    (shear p)ᴴ * hermitianMatrix a b (p * u) u (conj u) * shear p =
      !![(a : ℂ), 0, u; 0, (-a : ℂ), conj u; conj u, u, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [shear, hermitianMatrix, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fin.sum_univ_three, hsum, mul_add, add_mul,
      sub_eq_add_neg]
  all_goals try ring
  · calc
      (b : ℂ) - conj p * u - conj u * p =
          (b : ℂ) - (conj p * u + p * conj u) := by ring
      _ = -(a : ℂ) := by rw [← hsum]; ring

theorem final_unitary_identity (a : ℝ) (x y : ℝ) :
    (finalUnitary)ᴴ *
        !![(a : ℂ), 0, (x + Complex.I * y : ℂ);
          0, (-a : ℂ), (x - Complex.I * y : ℂ);
          (x - Complex.I * y : ℂ), (x + Complex.I * y : ℂ), 0] *
        finalUnitary =
      Complex.I •
        !![(0 : ℂ), (a : ℂ), (Real.sqrt 2 * x : ℂ);
          (-a : ℂ), 0, (Real.sqrt 2 * y : ℂ);
          (-Real.sqrt 2 * x : ℂ), (-Real.sqrt 2 * y : ℂ), 0] := by
  have hr : (Real.sqrt 2) ^ 2 = (2 : ℝ) := by norm_num
  have hrC : (Real.sqrt 2 : ℂ) ^ 2 = (2 : ℂ) := by exact_mod_cast hr
  have hr0 : Real.sqrt 2 ≠ 0 := by positivity
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [finalUnitary, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fin.sum_univ_three, Complex.conj_ofReal, hr0,
      div_eq_mul_inv, sub_eq_add_neg]
  all_goals field_simp [hr0] <;> ring_nf <;> simp [hrC]

theorem finalUnitary_isUnit : IsUnit (finalUnitary : M) := by
  rw [Matrix.isUnit_iff_isUnit_det]
  apply isUnit_iff_ne_zero.mpr
  have hr0 : Real.sqrt 2 ≠ 0 := by positivity
  simp [finalUnitary, Matrix.det_fin_three, div_eq_mul_inv, hr0]
  field_simp [hr0]
  norm_num

theorem congruence_pairing_transport (C H : M) (w w' : Fin 3 → ℂ) :
    star (C *ᵥ w) ⬝ᵥ (H *ᵥ (C *ᵥ w')) =
      star w ⬝ᵥ ((Cᴴ * H * C) *ᵥ w') := by
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec]
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]

theorem zero_graph_common_kernel
    (K : Submodule ℝ M)
    (hzero : ∀ H ∈ K, H 0 2 = 0 ∧ H 1 2 = 0 ∧ H 2 2 = 0) :
    ∃ v : Fin 3 → ℂ, v ≠ 0 ∧ ∀ H ∈ K, H *ᵥ v = 0 := by
  refine ⟨e3, ?_, ?_⟩
  · intro h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    have h2 := congrFun h 2
    simp [e3] at h0 h1 h2
  · intro H hH
    ext i
    fin_cases i
    · convert (hzero H hH).1 using 1 <;>
        simp [Matrix.mulVec, e3, Fin.sum_univ_three, Matrix.vecHead,
          Matrix.vecTail]
    · convert (hzero H hH).2.1 using 1 <;>
        simp [Matrix.mulVec, e3, Fin.sum_univ_three, Matrix.vecHead,
          Matrix.vecTail]
    · convert (hzero H hH).2.2 using 1 <;>
        simp [Matrix.mulVec, e3, Fin.sum_univ_three, Matrix.vecHead,
          Matrix.vecTail]

def normalizedGraphTrichotomy : Prop :=
  ∀ (K : Submodule ℝ M), D ∈ K →
    (∀ H : M, H ∈ K → H.IsHermitian) →
    (∀ H : M, H ∈ K → H.det = 0) →
    (∃ v : Fin 3 → ℂ, v ≠ 0 ∧ ∀ H ∈ K, H *ᵥ v = 0) ∨
    (∃ W : Submodule ℂ (Fin 3 → ℂ), Module.finrank ℂ W = 2 ∧
      ∀ H ∈ K, ∀ w ∈ W, ∀ w' ∈ W,
        star w ⬝ᵥ (H *ᵥ w') = 0) ∨
    (∃ C : M, IsUnit C ∧
      ∀ H, H ∈ K ↔ Cᴴ * H * C ∈ (iSkew3 : Set M))

end D5.S3.Quantum.Algebra.NormalizedSingularHermitianKernel
