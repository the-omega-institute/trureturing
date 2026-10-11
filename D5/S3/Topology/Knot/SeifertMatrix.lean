/- GID: D5/S3/Topology/Knot/SeifertMatrix
   generality: G
   mirror-B: none
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: reusable algebraic interface for Seifert matrices and Alexander determinants
   digest: A small, executable algebraic layer for knot-theoretic Seifert data.
-/

import Mathlib.Algebra.Polynomial.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Notation

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Topology.Knot

open Matrix Polynomial

/- A Seifert matrix is retained as integer data.  The geometric realization by a
   surface is deliberately a separate layer: this file only exposes the algebra
   that every such realization supplies. -/
abbrev SeifertMatrix (n : ℕ) := Matrix (Fin n) (Fin n) ℤ

def symmetrization {n : ℕ} (V : SeifertMatrix n) : SeifertMatrix n :=
  V + V.transpose

def IsUnimodular {n : ℕ} (V : SeifertMatrix n) : Prop :=
  V.det = 1 ∨ V.det = -1

theorem symmetrization_transpose {n : ℕ} (V : SeifertMatrix n) :
    (symmetrization V).transpose = symmetrization V := by
  ext i j
  simp [symmetrization, add_comm]

theorem symmetrization_symmetric {n : ℕ} (V : SeifertMatrix n) (i j : Fin n) :
    symmetrization V i j = symmetrization V j i := by
  have h := congr_fun (congr_fun (symmetrization_transpose V) i) j
  simpa [Matrix.transpose_apply] using h.symm

theorem isUnimodular_transpose {n : ℕ} {V : SeifertMatrix n} :
    IsUnimodular V.transpose ↔ IsUnimodular V := by
  simp only [IsUnimodular, Matrix.det_transpose]

theorem seifertMatrix_det_transpose {n : ℕ} (V : SeifertMatrix n) :
    V.transpose.det = V.det := by
  exact Matrix.det_transpose V

/- The one-variable Alexander determinant attached to algebraic Seifert data.
   The convention is det(tV - Vᵀ); changing the usual normalization by a unit
   does not affect the intended knot-theoretic invariant. -/
noncomputable def alexanderMatrix {n : ℕ} (V : SeifertMatrix n) :
    Matrix (Fin n) (Fin n) (Polynomial ℤ) :=
  fun i j => Polynomial.X * Polynomial.C (V i j) - Polynomial.C (V j i)

noncomputable def alexanderPolynomial {n : ℕ} (V : SeifertMatrix n) : Polynomial ℤ :=
  (alexanderMatrix V).det

def trefoilSeifert : SeifertMatrix 2 := !![1, 0; -1, 1]

theorem trefoilSeifert_unimodular : IsUnimodular trefoilSeifert := by
  left
  norm_num [trefoilSeifert, Matrix.det_fin_two]

theorem trefoil_alexanderPolynomial :
    alexanderPolynomial trefoilSeifert =
      Polynomial.X ^ 2 - Polynomial.X + 1 := by
  simp [alexanderPolynomial, alexanderMatrix, trefoilSeifert, Matrix.det_fin_two]
  ring

theorem trefoil_symmetrization_symmetric (i j : Fin 2) :
    symmetrization trefoilSeifert i j = symmetrization trefoilSeifert j i := by
  exact symmetrization_symmetric trefoilSeifert i j

#print axioms symmetrization_transpose
#print axioms trefoil_alexanderPolynomial

end D5.S3.Topology.Knot
