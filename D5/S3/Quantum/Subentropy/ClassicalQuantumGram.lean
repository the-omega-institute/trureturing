/- GID: D5/S3/Quantum/Subentropy/ClassicalQuantumGram
   generality: G
   mirror-B: D5/B/S3/Quantum/Subentropy/ClassicalQuantumGram
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Rectangular square-root Gram realization of classical-quantum conditional subentropy. -/

import D5.S3.Quantum.Subentropy.Basic
import D5.S3.Quantum.Information.OrthogonalRecordEntropy
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic

/-! Exact rectangular Gram interfaces for canonical c-q states. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder CStarAlgebra Kronecker

namespace D5.S3.Quantum.Subentropy.ClassicalQuantumGram

open _root_.D5.S3.Quantum.Foundation.FiniteStateChannel
open _root_.D5.S3.Quantum.Information.PartialTraceMutualInformation
open _root_.D5.S3.Quantum.Information.OrthogonalRecordEntropy
open _root_.D5.S3.Quantum.Subentropy.Basic

variable {X B : Type*} [Fintype X] [DecidableEq X] [Fintype B] [DecidableEq B]

/-- Erase off-diagonal classical blocks without changing their entries. -/
def blockPinch (A : Matrix (X × B) (X × B) ℂ) : Matrix (X × B) (X × B) ℂ :=
  fun i j => if i.1 = j.1 then A i j else 0

private def weightedRoot (p : X → ℝ) (ρ : X → DensityState B) (x : X) :
    Matrix B B ℂ :=
  CFC.sqrt (p x • CStarMatrix.ofMatrix.symm (ρ x).1)

/-- The rectangular map from the direct sum of the fragment spaces to the fragment space. -/
def cqRowSqrt (p : X → ℝ) (ρ : X → DensityState B) : Matrix B (X × B) ℂ :=
  fun b i => weightedRoot p ρ i.1 b i.2

private theorem root_adjoint (p : X → ℝ) (ρ : X → DensityState B) (x : X) :
    (weightedRoot p ρ x).conjTranspose = weightedRoot p ρ x := by
  simpa only [weightedRoot, Matrix.star_eq_conjTranspose] using
    (CFC.sqrt_nonneg (p x • CStarMatrix.ofMatrix.symm (ρ x).1)).isSelfAdjoint.star_eq

private theorem root_square (p : X → ℝ) (hp : ∀ x, 0 ≤ p x)
    (ρ : X → DensityState B) (x : X) :
    weightedRoot p ρ x * weightedRoot p ρ x =
      p x • CStarMatrix.ofMatrix.symm (ρ x).1 := by
  exact CFC.sqrt_mul_sqrt_self _ ((density_posSemidef (ρ x)).smul (hp x)).nonneg

private theorem row_mul_adjoint (p : X → ℝ) (hp : ∀ x, 0 ≤ p x)
    (ρ : X → DensityState B) :
    cqRowSqrt p ρ * (cqRowSqrt p ρ).conjTranspose =
      ∑ x, p x • CStarMatrix.ofMatrix.symm (ρ x).1 := by
  ext b c
  simp only [Matrix.mul_apply, cqRowSqrt, Matrix.conjTranspose_apply,
    Fintype.sum_prod_type, Matrix.sum_apply]
  calc
    _ = ∑ x, (weightedRoot p ρ x * (weightedRoot p ρ x).conjTranspose) b c := rfl
    _ = _ := by
      apply Finset.sum_congr rfl
      intro x _
      exact congrArg (fun A : Matrix B B ℂ => A b c)
        (by rw [root_adjoint, root_square p hp ρ x])

private theorem record_entries (p : X → ℝ) (hp : ∀ x, 0 ≤ p x)
    (hs : ∑ x, p x = 1) (ρ : X → DensityState B) (i j : X × B) :
    (CStarMatrix.ofMatrix.symm (recordState p hp hs ρ).1) i j =
      if i.1 = j.1 then (p i.1 : ℂ) *
        (CStarMatrix.ofMatrix.symm (ρ i.1).1) i.2 j.2 else 0 := by
  classical
  change (∑ x, p x •
    ((Matrix.diagonal (fun k => if k = x then (1 : ℂ) else 0)) ⊗ₖ
      (CStarMatrix.ofMatrix.symm (ρ x).1))) i j = _
  simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.kronecker_apply,
    Matrix.diagonal, Complex.real_smul]
  by_cases hij : i.1 = j.1
  · simp [hij, eq_comm]
  · simp [hij]

/-- Conditional subentropy uses the canonical record and mixture states. -/
def conditionalSubentropy (p : X → ℝ) (hp : ∀ x, 0 ≤ p x)
    (hs : ∑ x, p x = 1) (ρ : X → DensityState B) : ℝ :=
  subentropy (recordState p hp hs ρ) - subentropy (mixtureState p hp hs ρ)

/-- Conditional subentropy is the block-pinching gap of the rectangular Gram matrix. -/
private theorem cq_conditional_eq_pinchingGap (p : X → ℝ) (hp : ∀ x, 0 ≤ p x)
    (hs : ∑ x, p x = 1) (ρ : X → DensityState B) :
    conditionalSubentropy p hp hs ρ =
      matrixSubentropy (blockPinch ((cqRowSqrt p ρ).conjTranspose * cqRowSqrt p ρ)) -
      matrixSubentropy ((cqRowSqrt p ρ).conjTranspose * cqRowSqrt p ρ) := by
  have hpinch : blockPinch ((cqRowSqrt p ρ).conjTranspose * cqRowSqrt p ρ) =
      CStarMatrix.ofMatrix.symm (recordState p hp hs ρ).1 := by
    ext i j
    rw [record_entries]
    by_cases hij : i.1 = j.1
    · simp only [blockPinch, hij, ite_true]
      change ((weightedRoot p ρ i.1).conjTranspose * weightedRoot p ρ j.1) i.2 j.2 = _
      rw [← hij, root_adjoint, root_square p hp ρ i.1]
      rfl
    · simp [blockPinch, hij]
  have hmix : cqRowSqrt p ρ * (cqRowSqrt p ρ).conjTranspose =
      CStarMatrix.ofMatrix.symm (mixtureState p hp hs ρ).1 := row_mul_adjoint p hp ρ
  rw [hpinch, matrixSubentropy_rectangular_gram, hmix]
  rfl

private theorem pure_block_pinching (v : (X × B) → ℂ)
    (hv : ∑ i, star (v i) * v i = 1) :
    matrixSubentropy (blockPinch (Matrix.vecMulVec v (star v))) -
      matrixSubentropy (Matrix.vecMulVec v (star v)) =
      matrixSubentropy (Matrix.diagonal
        (fun x => ((∑ b, Complex.normSq (v (x,b)) : ℝ) : ℂ))) := by
  classical
  let W : Matrix (X × B) X ℂ := fun i x => if i.1 = x then v i else 0
  have hleft : W.conjTranspose * W = Matrix.diagonal
      (fun x => ((∑ b, Complex.normSq (v (x,b)) : ℝ) : ℂ)) := by
    ext x y
    by_cases hxy : x = y
    · subst y
      simp [W, Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type,
        Complex.normSq_eq_conj_mul_self]
    · simp [W, Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type,
        Matrix.diagonal_apply, hxy, eq_comm]
  have hright : W * W.conjTranspose =
      blockPinch (Matrix.vecMulVec v (star v)) := by
    ext i j
    by_cases hij : i.1 = j.1
    · simp [W, Matrix.mul_apply, Matrix.conjTranspose_apply, blockPinch, hij,
        Matrix.vecMulVec, Pi.star_apply]
    · simp [W, Matrix.mul_apply, Matrix.conjTranspose_apply, blockPinch, hij, eq_comm]
  rw [matrixSubentropy_pure v hv, sub_zero, ← hright,
    ← matrixSubentropy_rectangular_gram W, hleft]

end D5.S3.Quantum.Subentropy.ClassicalQuantumGram
