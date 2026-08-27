/- GID: D5/S3/Quantum/PureState/PerfectEffectDiscriminationOrthogonality
   generality: G
   mirror-B: D5/B/S3/Quantum/PureState/PerfectEffectDiscriminationOrthogonality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A positive contraction accepting one state and rejecting another forces orthogonality. -/

import Mathlib.Analysis.Matrix.Order

/- Library-search audit trail (2026-08-27):
   * Repository searches for perfect one-shot discrimination, positive effects,
     and orthogonality found no exact theorem on finite complex pure states.
   * Pinned Mathlib has no exact discrimination theorem. The exact component
     `Matrix.PosSemidef.dotProduct_mulVec_zero_iff` identifies a vector in the
     kernel of a positive matrix from its vanishing quadratic value and is
     applied directly to the effect and its complement below.
   * The matrix identities `Matrix.star_mulVec` and
     `Matrix.dotProduct_mulVec` transport the final overlap through the
     Hermitian effect. -/

namespace D5.S3.Quantum.PureState.PerfectEffectDiscriminationOrthogonality

open scoped ComplexOrder Matrix MatrixOrder

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- A finite-dimensional quantum effect that accepts a normalized state with
probability one and rejects another vector with probability zero makes the two
vectors orthogonal. The rejected vector need not be normalized, which is a
strict strengthening of the pure-state formulation. -/
theorem perfect_effect_discrimination_orthogonal
    {Index : Type*} [Fintype Index] [DecidableEq Index]
    (effect : Matrix Index Index ℂ) (psi phi : Index → ℂ)
    (hEffect : effect.PosSemidef)
    (hComplement : (1 - effect).PosSemidef)
    (hPsiNormalized : star psi ⬝ᵥ psi = 1)
    (hAccept : star psi ⬝ᵥ (effect *ᵥ psi) = 1)
    (hReject : star phi ⬝ᵥ (effect *ᵥ phi) = 0) :
    star phi ⬝ᵥ psi = 0 := by
  have hComplementValue :
      star psi ⬝ᵥ ((1 - effect) *ᵥ psi) = 0 := by
    calc
      star psi ⬝ᵥ ((1 - effect) *ᵥ psi) =
          star psi ⬝ᵥ psi - star psi ⬝ᵥ (effect *ᵥ psi) := by
        simp [Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub]
      _ = 0 := by rw [hPsiNormalized, hAccept, sub_self]
  have hComplementPsi : (1 - effect) *ᵥ psi = 0 :=
    (hComplement.dotProduct_mulVec_zero_iff psi).mp hComplementValue
  have hEffectPsi : effect *ᵥ psi = psi := by
    have hDifference : psi - effect *ᵥ psi = 0 := by
      simpa [Matrix.sub_mulVec, Matrix.one_mulVec] using hComplementPsi
    exact (sub_eq_zero.mp hDifference).symm
  have hEffectPhi : effect *ᵥ phi = 0 :=
    (hEffect.dotProduct_mulVec_zero_iff phi).mp hReject
  calc
    star phi ⬝ᵥ psi = star phi ⬝ᵥ (effect *ᵥ psi) := by rw [hEffectPsi]
    _ = (star phi ᵥ* effect) ⬝ᵥ psi := by rw [Matrix.dotProduct_mulVec]
    _ = star (effect *ᵥ phi) ⬝ᵥ psi := by
      rw [Matrix.star_mulVec, hEffect.isHermitian.eq]
    _ = 0 := by simp [hEffectPhi]

#print axioms perfect_effect_discrimination_orthogonal

end D5.S3.Quantum.PureState.PerfectEffectDiscriminationOrthogonality
