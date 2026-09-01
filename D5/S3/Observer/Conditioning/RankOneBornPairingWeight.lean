/- GID: D5/S3/Observer/Conditioning/RankOneBornPairingWeight
   generality: G
   mirror-B: D5/B/S3/Observer/Conditioning/RankOneBornPairingWeight
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Rank-one Born reduction yields a nonnegative state-projection pairing weight. -/

import D5.S3.Observer.BornReduction

/- Library-search audit trail (2026-09-02):
   * Exact repository hit: `rank_one_pure_state_modulus_square_reduction`
     proves the rank-one equality and is applied directly below.
   * The canonical `recordWeight` and `bornProbability` definitions identify the
     weight with `Matrix.trace (rho * P k)`; `born_probability_skeleton` supplies
     nonnegativity for a positive trace-one state and a record projection.
   * Pinned Mathlib supplies the matrix and complex identities used by the frozen
     rank-one theorem. Loogle found no single external theorem for the full result.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.Conditioning.RankOneBornPairingWeight

open D5.S3.Observer.BornReduction
open D5.S3.Observer.Conditioning
open D5.S3.Quantum.FiniteDimensional
open scoped ComplexOrder

/-- Source lines 17495-17510 and 17558-17582: for a finite complete orthogonal
record measurement and a positive trace-one state, rank-one branch and state
representations reduce the canonical state-projection pairing weight to a
squared transition modulus, while retaining its nonnegative scalar type. -/
theorem rank_one_born_pairing_weight
    {n kappa : Type*} [Fintype n] [DecidableEq n]
    [Fintype kappa]
    (P : kappa -> Matrix n n ℂ) (rho : Matrix n n ℂ) (k : kappa)
    (phi psi : n -> ℂ)
    (hP : IsRecordMeasurement P)
    (hRho : rho.PosSemidef)
    (hTrace : Matrix.trace rho = 1)
    (hProjection : P k = Matrix.vecMulVec phi (star phi))
    (hPureState : rho = Matrix.vecMulVec psi (star psi)) :
    recordWeight P rho k = ((‖star phi ⬝ᵥ psi‖ ^ 2 : ℝ) : ℂ) ∧
      0 ≤ recordWeight P rho k := by
  constructor
  · exact rank_one_pure_state_modulus_square_reduction
      P rho k phi psi hProjection hPureState
  · simpa [recordWeight] using
      (born_probability_skeleton rho hRho hTrace).2.2 (P k)
        (hP.selfAdjoint k) (hP.idempotent k)

/- Reverse probe for both boxed assertions: the equality transports the
nonnegative pairing weight to the displayed squared transition modulus. -/
example
    {n kappa : Type*} [Fintype n] [DecidableEq n]
    [Fintype kappa]
    (P : kappa -> Matrix n n ℂ) (rho : Matrix n n ℂ) (k : kappa)
    (phi psi : n -> ℂ)
    (hP : IsRecordMeasurement P)
    (hRho : rho.PosSemidef)
    (hTrace : Matrix.trace rho = 1)
    (hProjection : P k = Matrix.vecMulVec phi (star phi))
    (hPureState : rho = Matrix.vecMulVec psi (star psi)) :
    0 ≤ ((‖star phi ⬝ᵥ psi‖ ^ 2 : ℝ) : ℂ) := by
  rcases rank_one_born_pairing_weight P rho k phi psi hP hRho hTrace
      hProjection hPureState with ⟨hReduction, hWeight⟩
  rw [hReduction] at hWeight
  exact hWeight

/- Trivialization probe: the zero matrix cannot inhabit the source's
positive trace-one state premise, so the global state is not vacuous. -/
example
    {n : Type*} [Fintype n] [DecidableEq n] :
    Matrix.trace (0 : Matrix n n ℂ) ≠ 1 := by
  simp

#print axioms rank_one_born_pairing_weight

end D5.S3.Observer.Conditioning.RankOneBornPairingWeight
