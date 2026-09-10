/- GID: D5/S3/Quantum/Information/PartialTraceMutualInformation
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Partial traces preserve density states and determine quantum mutual information. -/

import D5.S3.Quantum.Divergence.VonNeumannEntropyPinching

/- The trace-preservation and positivity proofs below are adapted from
   CsdLean4/Mathlib/LinearAlgebra/Matrix/PartialTrace.lean,
   zblore/csd-lean4 revision 13eda16971c66de4bc9f550e418dd4fdf59a5121.
   Copyright (c) 2026 Zayn Blore. All rights reserved.
   Released under Apache 2.0; full license: docs/reports/qmutualinfo/csd-lean4-LICENSE.txt.
   Changes: specialize to complex matrices and retain the existing partialTrace API.
   Retire these ports when this repository's pinned Mathlib supplies equivalent declarations.
   Search receipts and the revised registration are in docs/reports/qmutualinfo/.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Information.PartialTraceMutualInformation

open scoped BigOperators ComplexOrder Kronecker Matrix
open scoped MatrixOrder
open D5.S3.Quantum.Divergence.QuantumRelativeEntropyDefectComposition
open D5.S3.Quantum.Divergence.VonNeumannEntropyPinching

noncomputable def partialTraceLeft {A B : Type*} [Fintype A]
    (joint : Matrix (A × B) (A × B) ℂ) : Matrix B B ℂ :=
  fun b d => ∑ a, joint (a, b) (a, d)

noncomputable def partialTraceRight {A B : Type*} [Fintype B]
    (joint : Matrix (A × B) (A × B) ℂ) : Matrix A A ℂ :=
  fun a c => ∑ b, joint (a, b) (c, b)

theorem partialTraceLeft_add {A B : Type*} [Fintype A]
    (x y : Matrix (A × B) (A × B) ℂ) :
    partialTraceLeft (x + y) = partialTraceLeft x + partialTraceLeft y := by
  ext b d
  simp [partialTraceLeft, Finset.sum_add_distrib]

theorem partialTraceRight_add {A B : Type*} [Fintype B]
    (x y : Matrix (A × B) (A × B) ℂ) :
    partialTraceRight (x + y) = partialTraceRight x + partialTraceRight y := by
  ext a c
  simp [partialTraceRight, Finset.sum_add_distrib]

theorem partialTraceLeft_kronecker {A B : Type*} [Fintype A]
    (x : Matrix A A ℂ) (y : Matrix B B ℂ) :
    partialTraceLeft (Matrix.kronecker x y) = Matrix.trace x • y := by
  ext b d
  simp [partialTraceLeft, Matrix.trace, Finset.mul_sum, mul_comm]

theorem partialTraceRight_kronecker {A B : Type*} [Fintype B]
    (x : Matrix A A ℂ) (y : Matrix B B ℂ) :
    partialTraceRight (Matrix.kronecker x y) = Matrix.trace y • x := by
  ext a c
  simp [partialTraceRight, Matrix.trace, Finset.mul_sum, mul_comm]

theorem trace_partialTraceLeft {A B : Type*} [Fintype A] [Fintype B]
    (joint : Matrix (A × B) (A × B) ℂ) :
    Matrix.trace (partialTraceLeft joint) = Matrix.trace joint := by
  simp only [Matrix.trace, Matrix.diag_apply, partialTraceLeft]
  exact (Fintype.sum_prod_type_right fun p : A × B => joint p p).symm

theorem trace_partialTraceRight {A B : Type*} [Fintype A] [Fintype B]
    (joint : Matrix (A × B) (A × B) ℂ) :
    Matrix.trace (partialTraceRight joint) = Matrix.trace joint := by
  simp only [Matrix.trace, Matrix.diag_apply, partialTraceRight]
  exact (Fintype.sum_prod_type fun p : A × B => joint p p).symm

theorem partialTraceLeft_posSemidef {A B : Type*} [Fintype A]
    {joint : Matrix (A × B) (A × B) ℂ} (h : joint.PosSemidef) :
    (partialTraceLeft joint).PosSemidef := by
  have heq : partialTraceLeft joint =
      ∑ a : A, joint.submatrix (fun b => (a, b)) (fun b => (a, b)) := by
    ext b d
    simp [partialTraceLeft, Matrix.sum_apply, Matrix.submatrix_apply]
  rw [heq]
  exact Matrix.posSemidef_sum _ (fun a _ => h.submatrix (fun b => (a, b)))

theorem partialTraceRight_posSemidef {A B : Type*} [Fintype B]
    {joint : Matrix (A × B) (A × B) ℂ} (h : joint.PosSemidef) :
    (partialTraceRight joint).PosSemidef := by
  have heq : partialTraceRight joint =
      ∑ b : B, joint.submatrix (fun a => (a, b)) (fun a => (a, b)) := by
    ext a c
    simp [partialTraceRight, Matrix.sum_apply, Matrix.submatrix_apply]
  rw [heq]
  exact Matrix.posSemidef_sum _ (fun b _ => h.submatrix (fun a => (a, b)))

/-- Trace out the left factor, retaining the state on `B`. -/
noncomputable def marginalLeft
    {A B : Type*} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B]
    (rho : DensityState (A × B)) : DensityState B := by
  refine ⟨CStarMatrix.ofMatrix (partialTraceLeft rho.1), ?_, ?_⟩
  · change (partialTraceLeft rho.1 - 0).PosSemidef
    rw [sub_zero]
    apply partialTraceLeft_posSemidef
    simpa only [sub_zero] using rho.2.1
  · exact (trace_partialTraceLeft rho.1).trans rho.2.2

/-- Trace out the right factor, retaining the state on `A`. -/
noncomputable def marginalRight
    {A B : Type*} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B]
    (rho : DensityState (A × B)) : DensityState A := by
  refine ⟨CStarMatrix.ofMatrix (partialTraceRight rho.1), ?_, ?_⟩
  · change (partialTraceRight rho.1 - 0).PosSemidef
    rw [sub_zero]
    apply partialTraceRight_posSemidef
    simpa only [sub_zero] using rho.2.1
  · exact (trace_partialTraceRight rho.1).trans rho.2.2

/-- Mutual information of a joint state, with both marginals obtained by partial trace. -/
noncomputable def quantumMutualInformation
    {A B : Type*} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] (rho : DensityState (A × B)) : ℝ :=
  vonNeumannEntropy (marginalRight rho) + vonNeumannEntropy (marginalLeft rho) -
    vonNeumannEntropy rho

#print axioms partialTraceLeft_posSemidef
#print axioms partialTraceRight_posSemidef
#print axioms marginalLeft
#print axioms marginalRight

end D5.S3.Quantum.Information.PartialTraceMutualInformation
