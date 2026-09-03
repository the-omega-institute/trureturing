/- GID: D5/S3/Weil/Pick/InvertibleHermitianInertiaPullback
   generality: G
   mirror-B: D5/B/S3/Weil/Pick/InvertibleHermitianInertiaPullback
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: An invertible square pullback preserves the full positive and negative inertia of a finite Hermitian form. -/

import D5.S3.SpectralTopology.FiniteSpectralLocalizer
import D5.S3.Weil.ZetaLinear.Inertia
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic

/-!
# Invertible Hermitian inertia pullback

The repository already proves that positive index cannot increase under a
Hermitian pullback. It also proves that matrix negation exchanges positive and
negative indices. This node combines those owners with the nonsingular matrix
inverse to obtain exact inertia preservation for an invertible square
congruence.

The theorem is finite-dimensional linear algebra. It assumes neither a Cauchy
full-rank theorem nor any zeta, Stieltjes, Weil, or RH statement.
-/

/- Library-first audit trail (2026-09-03):
   * `RHLinalg.posIndex_conj_le` is reused from
     `D5/S3/Weil/ZetaLinear/Inertia`.
   * `posIndex_neg_eq_negIndex` is reused from
     `D5/S3/SpectralTopology/FiniteSpectralLocalizer`.
   * Pinned Mathlib supplies `Matrix.mul_nonsing_inv`, conjugate-transpose
     multiplication, and the nonsingular matrix inverse.
   * Repository search found no public square-invertible inertia-congruence
     owner. The open draft `FullRankInertiaPullback` uses a longer independent
     negative-subspace proof; this node gives the minimal library-first route. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Matrix
open scoped ComplexOrder

namespace D5.S3.Weil.Pick.InvertibleHermitianInertiaPullback

open RHLinalg
open D5.S3.SpectralTopology.FiniteSpectralLocalizer

universe u

variable {K : Type u} [RCLike K]
variable {n : Type u} [Fintype n] [DecidableEq n]

/-- Pullback by any square matrix cannot increase negative index. -/
private theorem negative_index_pullback_le
    {Q : Matrix n n K} (hQ : Q.IsHermitian) (B : Matrix n n K) :
    negIndex (isHermitian_conjTranspose_mul_mul B hQ) ≤ negIndex hQ := by
  let hPull : (Bᴴ * Q * B).IsHermitian :=
    isHermitian_conjTranspose_mul_mul B hQ
  change negIndex hPull ≤ negIndex hQ
  rw [← posIndex_neg_eq_negIndex hPull,
    ← posIndex_neg_eq_negIndex hQ]
  have hPositive :=
    RHLinalg.posIndex_conj_le hQ.neg B
  convert hPositive using 1 <;> simp

/-- An invertible square congruence preserves positive index exactly. -/
private theorem positive_index_invariant_of_isUnit_det
    {Q : Matrix n n K} (hQ : Q.IsHermitian)
    (B : Matrix n n K) (hB : IsUnit B.det) :
    posIndex (isHermitian_conjTranspose_mul_mul B hQ) = posIndex hQ := by
  let hPull : (Bᴴ * Q * B).IsHermitian :=
    isHermitian_conjTranspose_mul_mul B hQ
  apply Nat.le_antisymm
  · exact RHLinalg.posIndex_conj_le hQ B
  · have hBackRaw :
        posIndex
            (isHermitian_conjTranspose_mul_mul B⁻¹ hPull) ≤
          posIndex hPull :=
      RHLinalg.posIndex_conj_le hPull B⁻¹
    have hRecover :
        (B⁻¹)ᴴ * (Bᴴ * Q * B) * B⁻¹ = Q := by
      calc
        (B⁻¹)ᴴ * (Bᴴ * Q * B) * B⁻¹ =
            (B * B⁻¹)ᴴ * Q * (B * B⁻¹) := by
          rw [Matrix.conjTranspose_mul]
          noncomm_ring
        _ = Q := by
          rw [Matrix.mul_nonsing_inv B hB]
          simp
    have hBack : posIndex hQ ≤ posIndex hPull := by
      convert hBackRaw using 1
      exact hRecover
    exact hBack

/-- An invertible square congruence preserves negative index exactly. -/
private theorem negative_index_invariant_of_isUnit_det
    {Q : Matrix n n K} (hQ : Q.IsHermitian)
    (B : Matrix n n K) (hB : IsUnit B.det) :
    negIndex (isHermitian_conjTranspose_mul_mul B hQ) = negIndex hQ := by
  let hPull : (Bᴴ * Q * B).IsHermitian :=
    isHermitian_conjTranspose_mul_mul B hQ
  change negIndex hPull = negIndex hQ
  rw [← posIndex_neg_eq_negIndex hPull,
    ← posIndex_neg_eq_negIndex hQ]
  have hPositive :=
    positive_index_invariant_of_isUnit_det hQ.neg B hB
  convert hPositive using 1 <;> simp

/-- An invertible square congruence preserves the full inertia pair. -/
theorem inertia_invariant_of_isUnit_det
    {Q : Matrix n n K} (hQ : Q.IsHermitian)
    (B : Matrix n n K) (hB : IsUnit B.det) :
    posIndex (isHermitian_conjTranspose_mul_mul B hQ) = posIndex hQ ∧
      negIndex (isHermitian_conjTranspose_mul_mul B hQ) = negIndex hQ := by
  exact ⟨
    positive_index_invariant_of_isUnit_det hQ B hB,
    negative_index_invariant_of_isUnit_det hQ B hB⟩

#print axioms inertia_invariant_of_isUnit_det

end D5.S3.Weil.Pick.InvertibleHermitianInertiaPullback
