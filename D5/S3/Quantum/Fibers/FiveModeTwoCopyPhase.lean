/- GID: D5/S3/Quantum/Fibers/FiveModeTwoCopyPhase
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A real two-copy Bell effect reads the squared hidden phase magnitude. -/

import D5.S3.Quantum.Fibers.FiveModePhaseLift

/-! A two-copy real joint effect reads the squared hidden phase magnitude. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped BigOperators ComplexOrder Kronecker

namespace D5.S3.Quantum.Fibers.FiveModeTwoCopyPhase

open D5.S3.Quantum.Fibers.FiveModePhaseLift

/-- The real Bell-type ray on two copies, supported on `(2,2)` and `(4,4)`. -/
def bellRay : (Fin 5 × Fin 5) → ℂ :=
  fun k => if k = (2, 2) then 1 else if k = (4, 4) then -1 else 0

/-- The rank-one effect associated with `bellRay`. -/
def bellEffect : Matrix (Fin 5 × Fin 5) (Fin 5 × Fin 5) ℂ :=
  (2 : ℂ)⁻¹ • Matrix.vecMulVec bellRay (star bellRay)

/-- The probability of the Bell-type effect on two independent copies. -/
def twoCopyProbability (q : Set.Icc (0 : ℝ) 1) : ℝ :=
  (Matrix.trace ((Matrix.kronecker (mixture q) (mixture q)) * bellEffect)).re

private theorem bell_effect_certificate :
    bellEffect.PosSemidef ∧ Matrix.trace bellEffect = 1 ∧
    bellEffect * bellEffect = bellEffect := by
  refine ⟨?_, ?_, ?_⟩
  · exact (Matrix.posSemidef_vecMulVec_self_star bellRay).smul
      (Complex.nonneg_iff.mpr ⟨by norm_num, by norm_num⟩)
  · rw [bellEffect, Matrix.trace_smul, Matrix.trace_vecMulVec]
    norm_num [bellRay, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_succ]
  · have hnorm : star bellRay ⬝ᵥ bellRay = 2 := by
      norm_num [bellRay, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_succ]
    rw [bellEffect, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.vecMulVec_mul_vecMulVec, hnorm, Matrix.vecMulVec_smul]
    norm_num [smul_smul]

/-! The normalized real Bell effect is a projective positive readout, and on
the two-copy phase mixture its probability is the square of the hidden real
coherence magnitude. -/
theorem two_copy_bell_readout (q : Set.Icc (0 : ℝ) 1) :
    bellEffect.PosSemidef ∧ Matrix.trace bellEffect = 1 ∧
    bellEffect * bellEffect = bellEffect ∧
    twoCopyProbability q = (1 + (1 - 2 * (q : ℝ)) ^ 2) / 4 := by
  rcases bell_effect_certificate with ⟨hpos, htrace, hproj⟩
  refine ⟨hpos, htrace, hproj, ?_⟩
  norm_num [twoCopyProbability, bellEffect, mixture, phaseState, phaseRay,
    bellRay, Matrix.trace, Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.vecMulVec, Matrix.kronecker, Matrix.kroneckerMap_apply,
    Fintype.sum_prod_type, Fin.sum_univ_succ] <;> ring

end D5.S3.Quantum.Fibers.FiveModeTwoCopyPhase
