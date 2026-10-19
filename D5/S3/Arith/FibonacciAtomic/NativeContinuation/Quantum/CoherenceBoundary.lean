/- GID: D5/S3/Arith/FibonacciAtomic/NativeContinuation/Quantum/CoherenceBoundary
   generality: I
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/NativeContinuation/Quantum/CoherenceBoundary
   mirror-E: none(waiver:registration-template-not-established)
   anchors: []
   utility: none
   digest: Positivity bounds the 2-4 coherence while the odd-rejection branch reads only its diagonal source mass. -/

import D5.S3.Arith.FibonacciAtomic.NativeContinuation.Quantum.ReadoutInstrument
import Mathlib.Analysis.Matrix.PosDef

noncomputable section

open Matrix
open scoped BigOperators ComplexOrder

namespace D5.S3.Arith.FibonacciAtomic.NativeContinuation.Quantum.CoherenceBoundary

open D5.S3.Arith.FibonacciAtomic.NativeContinuation.Quantum.ReadoutInstrument
open D5.S3.Quantum.Foundation.FiniteKrausChannel
open PhyslibLeaf

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Positivity bounds the magnitude of the coherence between source coordinates 2 and 4
by their diagonal masses. -/
theorem coherence_radius_bound (rho : Matrix (Fin 5) (Fin 5) ℂ)
    (hρ : rho.PosSemidef) :
    Complex.normSq (rho 2 4) ≤ (rho 2 2).re * (rho 4 4).re := by
  have hq (x : Fin 5 → ℂ) :
      0 ≤ RCLike.re (star x ⬝ᵥ (rho *ᵥ x)) := hρ.re_dotProduct_nonneg x
  have hz : 0 ≤ (rho 2 2).re := by
    have h := hq (fun k : Fin 5 => if k = 2 then 1 else 0)
    norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at h ⊢
    exact h
  have hdiag2 : (rho 2 2).im = 0 := by
    have hh := congrFun (congrFun hρ.isHermitian (2 : Fin 5)) (2 : Fin 5)
    have hi := congrArg Complex.im hh
    simp [Matrix.conjTranspose_apply] at hi
    linarith
  have hdiag4 : (rho 4 4).im = 0 := by
    have hh := congrFun (congrFun hρ.isHermitian (4 : Fin 5)) (4 : Fin 5)
    have hi := congrArg Complex.im hh
    simp [Matrix.conjTranspose_apply] at hi
    linarith
  by_cases hz0 : (rho 2 2).re = 0
  · have hzero : star (fun k : Fin 5 => if k = 2 then (1 : ℂ) else 0) ⬝ᵥ
        (rho *ᵥ (fun k : Fin 5 => if k = 2 then (1 : ℂ) else 0)) = 0 := by
      have h22 : rho 2 2 = 0 := by
        apply Complex.ext <;> simp [hz0, hdiag2]
      norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, h22]
    have hmul := hρ.dotProduct_mulVec_zero_iff.mp hzero
    have hentry := congrFun hmul (4 : Fin 5)
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at hentry
    have h42 : rho 4 2 = 0 := by
      simpa using hentry
    have hherm := congrFun (congrFun hρ.isHermitian (2 : Fin 5)) (4 : Fin 5)
    have hstar := congrArg Complex.im hherm
    have hstarre := congrArg Complex.re hherm
    simp [Matrix.conjTranspose_apply, h42] at hstar hstarre
    have h24re : (rho 2 4).re = 0 := by linarith
    have h24im : (rho 2 4).im = 0 := by linarith
    simp [Complex.normSq_apply, h24re, h24im, hz0]
  · have hzpos : 0 < (rho 2 2).re := lt_of_le_of_ne hz (Ne.symm hz0)
    have hv := hq (fun k : Fin 5 =>
      if k = 2 then rho 2 4 else if k = 4 then -(rho 2 2).re else 0)
    norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, hdiag2, hdiag4,
      Complex.normSq_apply, Complex.star_def] at hv
    have hherm := congrFun (congrFun hρ.isHermitian (2 : Fin 5)) (4 : Fin 5)
    have hre := congrArg Complex.re hherm
    have him := congrArg Complex.im hherm
    simp [Matrix.conjTranspose_apply] at hre him
    have h42im : (rho 4 2).im = -(rho 2 4).im := by linarith [him]
    rw [hre, h42im] at hv
    ring_nf at hv
    have hdet : 0 ≤ (rho 2 2).re * (rho 4 4).re - Complex.normSq (rho 2 4) := by
      rw [Complex.normSq_apply]
      nlinarith [hv]
    nlinarith [hdet]

/-- Even on an arbitrary matrix input, the concrete odd-rejection branch has a single
Kraus column and therefore reads only the source diagonal coordinate 4. -/
theorem arbitrary_branch_trace_reads_diagonal (rho : Matrix (Fin 5) (Fin 5) ℂ) :
    Matrix.trace
        (MatrixMap.of_kraus (K () (7 : Fin 8)) (K () (7 : Fin 8)) rho) = rho 4 4 := by
  simp [MatrixMap.of_kraus, LinearMap.sum_apply, LinearMap.coe_mk,
    AddHom.coe_mk, Matrix.trace, Matrix.sum_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, K, outcomeCode, acquiredParity, replyCode,
    successorCode, Fin.sum_univ_succ]

/-- The diagonal branch mass is the hidden joint coordinate, while positivity leaves only a
coherence-radius bound; the branch itself carries no phase information. -/
theorem hidden_joint_bounds_coherence (rho : Matrix (Fin 5) (Fin 5) ℂ)
    (hρ : rho.PosSemidef) :
    Matrix.trace
        (MatrixMap.of_kraus (K () (7 : Fin 8)) (K () (7 : Fin 8)) rho) = rho 4 4 ∧
      Complex.normSq (rho 2 4) ≤ (rho 2 2).re * (rho 4 4).re := by
  exact ⟨arbitrary_branch_trace_reads_diagonal rho, coherence_radius_bound rho hρ⟩

#print axioms coherence_radius_bound
#print axioms arbitrary_branch_trace_reads_diagonal
#print axioms hidden_joint_bounds_coherence

end D5.S3.Arith.FibonacciAtomic.NativeContinuation.Quantum.CoherenceBoundary
