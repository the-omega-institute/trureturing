/- GID: D5/S3/Observer/Conditioning/RankOneBornPairingWeight
   generality: G
   mirror-B: D5/B/S3/Observer/Conditioning/RankOneBornPairingWeight
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Rank-one Born equality, trace pairing role, and unread conditional mixture. -/

import D5.S3.Observer.BornReduction

/- Library-search audit trail (2026-09-02):
   * Exact repository hit: `rank_one_pure_state_modulus_square_reduction`
     proves the rank-one equality and is applied directly below.
   * Exact repository hit: `unread_eq_weighted_ensemble` proves the unread-state
     conditional mixture and is applied directly below.
   * The canonical `recordWeight` and `bornProbability` definitions supply the
     explicit state-projection trace pairing bridge.
   * Pinned Mathlib supplies the matrix and complex identities used by both frozen
     source theorems. Loogle found no single external theorem for the three-part result.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.Conditioning.RankOneBornPairingWeight

open D5.S3.Observer.BornReduction
open D5.S3.Observer.Conditioning
open D5.S3.Quantum.FiniteDimensional
open scoped ComplexOrder

/-- Source lines 17493-17585: for a finite complete orthogonal record measurement
and a positive trace-one state, rank-one branch and state representations reduce
the canonical record weight to a squared transition modulus; the weight is the
state-projection trace pairing, and the unread state is the weighted conditional
ensemble. -/
theorem rank_one_born_pairing_weight
    {n kappa : Type*} [Fintype n] [DecidableEq n]
    [Fintype kappa]
    (P : kappa -> Matrix n n ℂ) (rho : Matrix n n ℂ) (k : kappa)
    (phi psi : n -> ℂ)
    (hP : IsRecordMeasurement P)
    (hState : rho.PosSemidef ∧ Matrix.trace rho = 1)
    (hProjection : P k = Matrix.vecMulVec phi (star phi))
    (hPureState : rho = Matrix.vecMulVec psi (star psi)) :
    recordWeight P rho k = ((‖star phi ⬝ᵥ psi‖ ^ 2 : ℝ) : ℂ) ∧
      recordWeight P rho k = Matrix.trace (rho * P k) ∧
      unreadState P rho =
        ∑ j, recordWeight P rho j • conditionalState P rho j := by
  refine ⟨?_, ?_, ?_⟩
  · exact rank_one_pure_state_modulus_square_reduction
      P rho k phi psi hProjection hPureState
  · rfl
  · exact unread_eq_weighted_ensemble hP hState.1

/- A2 mutation probe (expected red): replacing the structural trace-pairing leaf
with an arbitrary scalar identity or nonnegativity makes this projection ill-typed. -/
example
    {n kappa : Type*} [Fintype n] [DecidableEq n]
    [Fintype kappa]
    (P : kappa -> Matrix n n ℂ) (rho : Matrix n n ℂ) (k : kappa)
    (phi psi : n -> ℂ)
    (hP : IsRecordMeasurement P)
    (hState : rho.PosSemidef ∧ Matrix.trace rho = 1)
    (hProjection : P k = Matrix.vecMulVec phi (star phi))
    (hPureState : rho = Matrix.vecMulVec psi (star psi)) :
    recordWeight P rho k = Matrix.trace (rho * P k) := by
  exact (rank_one_born_pairing_weight P rho k phi psi hP hState
    hProjection hPureState).2.1

/- A3 presence probe (expected red under omission): the public result directly
projects the canonical unread/conditional-state weighted-ensemble identity. -/
example
    {n kappa : Type*} [Fintype n] [DecidableEq n]
    [Fintype kappa]
    (P : kappa -> Matrix n n ℂ) (rho : Matrix n n ℂ) (k : kappa)
    (phi psi : n -> ℂ)
    (hP : IsRecordMeasurement P)
    (hState : rho.PosSemidef ∧ Matrix.trace rho = 1)
    (hProjection : P k = Matrix.vecMulVec phi (star phi))
    (hPureState : rho = Matrix.vecMulVec psi (star psi)) :
    unreadState P rho =
      ∑ j, recordWeight P rho j • conditionalState P rho j := by
  exact (rank_one_born_pairing_weight P rho k phi psi hP hState
    hProjection hPureState).2.2

/- Trivialization probe: the zero matrix cannot inhabit the source's
positive trace-one state premise, so the global state is not vacuous. -/
example
    {n : Type*} [Fintype n] [DecidableEq n] :
    Matrix.trace (0 : Matrix n n ℂ) ≠ 1 := by
  simp

#print axioms rank_one_born_pairing_weight

end D5.S3.Observer.Conditioning.RankOneBornPairingWeight
