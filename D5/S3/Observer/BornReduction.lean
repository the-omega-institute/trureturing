/- GID: D5/S3/Observer/BornReduction
   generality: G
   mirror-B: D5/B/S3/Observer/BornReduction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Reduce rank-one pure-state record weights to squared transition moduli. -/

/- Library-search audit trail (2026-08-10):
   * Local mathlib searches for `vecMulVec`, `inner_mul_conj`, `normSq`, and squared complex norms
     found no single theorem stating this record-weight reduction.
   * The proof reuses `Matrix.vecMulVec_mul_vecMulVec`, `Matrix.trace_vecMulVec`,
     `dotProduct_comm`, `Matrix.star_dotProduct`, `Complex.normSq_eq_conj_mul_self`, and
     `Complex.normSq_eq_norm_sq`; the record-weight interface comes from `Conditioning`.
-/

import D5.S3.Observer.Conditioning

namespace D5.S3.Observer.BornReduction

open D5.S3.Observer.Conditioning
open scoped ComplexOrder

variable {n kappa : Type*} [Fintype n]

/-- A rank-one record branch evaluated on a rank-one pure state is the squared
transition modulus between their normalized vectors. -/
theorem rank_one_pure_state_modulus_square_reduction
    (P : kappa -> Matrix n n ℂ) (rho : Matrix n n ℂ) (k : kappa)
    (phi psi : n -> ℂ)
    (hProjection : P k = Matrix.vecMulVec phi (star phi))
    (hPureState : rho = Matrix.vecMulVec psi (star psi)) :
    recordWeight P rho k = ((‖star phi ⬝ᵥ psi‖ ^ 2 : ℝ) : ℂ) := by
  rw [recordWeight, D5.S3.Quantum.FiniteDimensional.bornProbability,
    hPureState, hProjection, Matrix.vecMulVec_mul_vecMulVec,
    Matrix.trace_vecMulVec, dotProduct_smul, dotProduct_comm psi (star phi),
    Matrix.star_dotProduct, smul_eq_mul]
  simpa only [RCLike.star_def, Complex.normSq_eq_norm_sq] using
    (Complex.normSq_eq_conj_mul_self (z := star phi ⬝ᵥ psi)).symm

end D5.S3.Observer.BornReduction
