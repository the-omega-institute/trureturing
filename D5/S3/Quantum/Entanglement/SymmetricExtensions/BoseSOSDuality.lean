/- GID: D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseSOSDuality
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/SymmetricExtensions/BoseSOSDuality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual tensor trace duality from homogeneous native SOS certificates. -/

import D5.S3.Quantum.Entanglement.SymmetricExtensions.BosePPTDuality
import D5.S3.Quantum.Entanglement.SymmetricExtensions.BoseDiagonalSymbol
import D5.S3.Weil.ZetaLinear.RankTrace

/-! The sufficiency direction uses the constructed PSD cut certificates,
as in Gulati--Nechita--Park, Theorem 8.11. Equality of complex coherent
symbols is upgraded to equality of compressed operators before pairing. -/

open scoped BigOperators ComplexOrder RealInnerProductSpace
open Matrix MvPolynomial
open D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPureBound
open D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPermutationFloor
open D5.S3.Quantum.Entanglement.SymmetricExtensions.BoseOccupationTwirl
open D5.S3.Quantum.Entanglement.SymmetricExtensions.BoseCoherentSymbol
open D5.S3.Quantum.Entanglement.SymmetricExtensions.BoseDiagonalSymbol
open D5.S3.Quantum.Entanglement.SymmetricExtensions.BoseSOSCertificates
open D5.S3.Quantum.Entanglement.SymmetricExtensions.BosePPTDuality

namespace D5.S3.Quantum.Entanglement.SymmetricExtensions.BoseSOSDuality

noncomputable section
set_option backward.isDefEq.respectTransparency false

open private tensorPhase_fixed partialTranspose_hermitian trace_partialTranspose_pair from
  D5.S3.Quantum.Entanglement.SymmetricExtensions.BosePPTDuality

variable {r n : ℕ}

private lemma coherent_compress
    (A : Matrix (Fin r → Fin n) (Fin r → Fin n) ℂ) (z : Fin n → ℂ) :
    star (tensorPhase z) ⬝ᵥ ((P (Fin r) (Fin n) * A * P (Fin r) (Fin n)) *ᵥ tensorPhase z) =
      star (tensorPhase z) ⬝ᵥ (A *ᵥ tensorPhase z) := by
  rw [← mulVec_mulVec,tensorPhase_fixed,← mulVec_mulVec,dotProduct_mulVec]
  have he : star (tensorPhase z) ᵥ* P (Fin r) (Fin n) = star (tensorPhase z) := by
    rw [← P_hermitian (Fin r) (Fin n),← star_mulVec,tensorPhase_fixed]
  rw [he]

private lemma trace_compress_supported
    (A E : Matrix (Fin r → Fin n) (Fin r → Fin n) ℂ)
    (hE : P (Fin r) (Fin n) * E * P (Fin r) (Fin n) = E) :
    (P (Fin r) (Fin n) * A * P (Fin r) (Fin n) * E).trace = (A * E).trace := by
  calc
    _ = (A * (P (Fin r) (Fin n) * E * P (Fin r) (Fin n))).trace := by
      simpa only [Matrix.mul_assoc] using
        Matrix.trace_mul_comm (P (Fin r) (Fin n)) (A * P (Fin r) (Fin n) * E)
    _ = _ := by rw [hE]

private lemma trace_eq_of_coherent_eq
    (A B E : Matrix (Fin r → Fin n) (Fin r → Fin n) ℂ)
    (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hE : P (Fin r) (Fin n) * E * P (Fin r) (Fin n) = E)
    (he : ∀ z : Fin n → ℂ, star (tensorPhase z) ⬝ᵥ (A *ᵥ tensorPhase z) =
      star (tensorPhase z) ⬝ᵥ (B *ᵥ tensorPhase z)) : (A * E).trace = (B * E).trace := by
  let Q := P (Fin r) (Fin n)
  have hzero : Q * (A-B) * Q = 0 := by
    apply eq_zero_of_coherent
    · have h := Matrix.isHermitian_conjTranspose_mul_mul Q (hA.sub hB)
      change ((P (Fin r) (Fin n))ᴴ * (A-B) * P (Fin r) (Fin n)).IsHermitian at h
      rw [P_hermitian] at h
      exact h
    · calc
        Q * (Q * (A-B) * Q) * Q = (Q*Q) * (A-B) * (Q*Q) := by
          simp only [Matrix.mul_assoc]
        _ = _ := by simp only [Q,P_idempotent]
    · intro z
      rw [coherent_compress]
      simp only [Matrix.sub_mulVec,dotProduct_sub,he z,sub_self]
  have hz : ((A-B) * E).trace = 0 := by
    rw [← trace_compress_supported (A-B) E hE,hzero]
    simp
  simpa only [Matrix.sub_mul,Matrix.trace_sub,sub_eq_zero] using hz

/-- Every actual homogeneous even SOS certificate pairs nonnegatively with
every fully-PPT Bose operator. This is an operator statement, with no assumed
GNP theorem and no removal of closure from a dual sum. -/
theorem even_sos_nonnegative
    (A : HermitianMat (Fin r → Fin n) ℂ)
    (p : MvPolynomial (Fin n) ℝ) (hp : p.IsHomogeneous r)
    (he : ∀ z : Fin n → ℂ, star (tensorPhase z) ⬝ᵥ (A.mat *ᵥ tensorPhase z) =
      eval₂ Complex.ofRealHom (fun i => star (z i) * z i) p)
    (hs : IsSumSq (expand 2 p)) :
    A ∈ ProperCone.dual (innerₗ (HermitianMat (Fin r → Fin n) ℂ))
      (bosePPT : Set (HermitianMat (Fin r → Fin n) ℂ)) := by
  obtain ⟨m,S,Z,hZ,hz⟩ := even_form_cut_certificates p r hp hs
  let B := ∑ i, partialTransposeOn (S i) (Z i)
  have hB : B.IsHermitian := by
    change (∑ i, partialTransposeOn (S i) (Z i))ᴴ = _
    rw [Matrix.conjTranspose_sum]
    apply Finset.sum_congr rfl
    intro i hi
    exact partialTranspose_hermitian (S i) (Z i) (hZ i).1
  intro E hE
  change 0 ≤ inner ℝ E A
  rw [HermitianMat.inner_eq_re_trace,Matrix.trace_mul_comm]
  change 0 ≤ (A.mat * E.mat).trace.re
  rw [trace_eq_of_coherent_eq A.mat B E.mat A.H hB hE.1 (fun z => (he z).trans (hz z).symm)]
  simp only [B,Matrix.sum_mul,Matrix.trace_sum,Complex.re_sum]
  apply Finset.sum_nonneg
  intro i hi
  rw [trace_partialTranspose_pair]
  simpa only [RCLike.re_to_complex] using
    RHLinalg.trace_mul_nonneg_of_posSemidef (hZ i) (hE.2 (S i))

#print axioms even_sos_nonnegative

/-- Exact native SOS duality for occupation-diagonal Hermitian operators,
including every homogeneous degree and all zero/singular cases. -/
theorem diagonal_dual_iff_sos
    (A : HermitianMat (Fin r → Fin n) ℂ)
    (ht : occupationTwirl A.mat = A.mat)
    (p : MvPolynomial (Fin n) ℝ) (hp : p.IsHomogeneous r)
    (he : realSymbol A.mat = expand 2 p) :
    A ∈ ProperCone.dual (innerₗ (HermitianMat (Fin r → Fin n) ℂ))
      (bosePPT : Set (HermitianMat (Fin r → Fin n) ℂ)) ↔ IsSumSq (expand 2 p) := by
  constructor
  · intro hA
    rw [← he]
    exact dual_bosePPT_real_sos A hA
  · exact even_sos_nonnegative A p hp
      (coherent_of_even_realSymbol A.mat A.H ht p he)

#print axioms diagonal_dual_iff_sos

end
end D5.S3.Quantum.Entanglement.SymmetricExtensions.BoseSOSDuality
