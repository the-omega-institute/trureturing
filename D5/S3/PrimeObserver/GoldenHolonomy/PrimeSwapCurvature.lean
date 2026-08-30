/- GID: D5/S3/PrimeObserver/GoldenHolonomy/PrimeSwapCurvature
   generality: G
   mirror-B: D5/B/S3/PrimeObserver/GoldenHolonomy/PrimeSwapCurvature
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Stable prime-memory swap curvature is gauge invariant. -/

import Mathlib.Tactic

/-!
# Prime swap curvature in the stable memory channel

A prime-local update has one memory coordinate and one scalar coordinate.  The
memory coordinate is multiplied by a common stable factor `a`, receives a
prime-dependent scalar injection `b`, and the scalar coordinate is multiplied
by the local factor `lambda`.

Two scalar local factors commute.  Their lifted memory updates need not.  The
result below computes the adjacent-swap defect, proves that it is unchanged by
a common change of memory origin, and factors it through the difference of the
two observer-origin estimates away from resonance.

This theorem is algebraic.  It does not identify the parameters with a zeta
Euler factor, prove decay with extraction depth, or make a zero-location claim.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.PrimeObserver.GoldenHolonomy.PrimeSwapCurvature

universe u

variable {K : Type u} [Field K]

/-- A one-dimensional stable memory update lifted over a scalar local factor. -/
def stablePrimeUpdate (a b localFactor : K) (state : K × K) : K × K :=
  (a * state.1 + b * state.2, localFactor * state.2)

/-- The memory defect produced by exchanging the order of two prime updates. -/
def primeSwapCurvature
    (a bP localFactorP bQ localFactorQ : K) : K :=
  (a - localFactorQ) * bP - (a - localFactorP) * bQ

/-- A common change of memory origin changes every local injection by a coboundary. -/
def memoryGaugeShift (a localFactor originShift b : K) : K :=
  b + (a - localFactor) * originShift

/-- Away from resonance, one local channel estimates the memory origin. -/
def observerOrigin (a localFactor b : K) : K :=
  b / (a - localFactor)

/--
The stable adjacent-swap curvature is the complete order defect of the lifted
updates.  It is antisymmetric and gauge invariant.  Away from resonance, it is
the product of the two resonance gaps with the difference between the local
observer-origin estimates, so vanishing curvature is equivalent to agreement
of those estimates.
-/
theorem prime_swap_curvature_spec
    (a bP localFactorP bQ localFactorQ originShift : K)
    (state : K × K)
    (hP : a - localFactorP ≠ 0)
    (hQ : a - localFactorQ ≠ 0) :
    (stablePrimeUpdate a bQ localFactorQ
          (stablePrimeUpdate a bP localFactorP state)).1 -
        (stablePrimeUpdate a bP localFactorP
          (stablePrimeUpdate a bQ localFactorQ state)).1 =
      primeSwapCurvature a bP localFactorP bQ localFactorQ * state.2 ∧
    (stablePrimeUpdate a bQ localFactorQ
          (stablePrimeUpdate a bP localFactorP state)).2 =
        (stablePrimeUpdate a bP localFactorP
          (stablePrimeUpdate a bQ localFactorQ state)).2 ∧
    primeSwapCurvature a bQ localFactorQ bP localFactorP =
      -primeSwapCurvature a bP localFactorP bQ localFactorQ ∧
    primeSwapCurvature a
        (memoryGaugeShift a localFactorP originShift bP) localFactorP
        (memoryGaugeShift a localFactorQ originShift bQ) localFactorQ =
      primeSwapCurvature a bP localFactorP bQ localFactorQ ∧
    primeSwapCurvature a bP localFactorP bQ localFactorQ =
      (a - localFactorP) * (a - localFactorQ) *
        (observerOrigin a localFactorP bP -
          observerOrigin a localFactorQ bQ) ∧
    (primeSwapCurvature a bP localFactorP bQ localFactorQ = 0 ↔
      observerOrigin a localFactorP bP =
        observerOrigin a localFactorQ bQ) := by
  have hMemory :
      (stablePrimeUpdate a bQ localFactorQ
            (stablePrimeUpdate a bP localFactorP state)).1 -
          (stablePrimeUpdate a bP localFactorP
            (stablePrimeUpdate a bQ localFactorQ state)).1 =
        primeSwapCurvature a bP localFactorP bQ localFactorQ * state.2 := by
    simp only [stablePrimeUpdate, primeSwapCurvature]
    ring
  have hScalar :
      (stablePrimeUpdate a bQ localFactorQ
            (stablePrimeUpdate a bP localFactorP state)).2 =
          (stablePrimeUpdate a bP localFactorP
            (stablePrimeUpdate a bQ localFactorQ state)).2 := by
    simp only [stablePrimeUpdate]
    ring
  have hAntisymmetric :
      primeSwapCurvature a bQ localFactorQ bP localFactorP =
        -primeSwapCurvature a bP localFactorP bQ localFactorQ := by
    unfold primeSwapCurvature
    ring
  have hGaugeInvariant :
      primeSwapCurvature a
          (memoryGaugeShift a localFactorP originShift bP) localFactorP
          (memoryGaugeShift a localFactorQ originShift bQ) localFactorQ =
        primeSwapCurvature a bP localFactorP bQ localFactorQ := by
    unfold primeSwapCurvature memoryGaugeShift
    ring
  have hFactorization :
      primeSwapCurvature a bP localFactorP bQ localFactorQ =
        (a - localFactorP) * (a - localFactorQ) *
          (observerOrigin a localFactorP bP -
            observerOrigin a localFactorQ bQ) := by
    unfold primeSwapCurvature observerOrigin
    field_simp [hP, hQ]
  have hZeroCriterion :
      primeSwapCurvature a bP localFactorP bQ localFactorQ = 0 ↔
        observerOrigin a localFactorP bP =
          observerOrigin a localFactorQ bQ := by
    have hProduct :
        (a - localFactorP) * (a - localFactorQ) ≠ 0 :=
      mul_ne_zero hP hQ
    constructor
    · intro hCurvature
      rw [hFactorization] at hCurvature
      have hDifference :
          observerOrigin a localFactorP bP -
              observerOrigin a localFactorQ bQ = 0 :=
        (mul_eq_zero.mp hCurvature).resolve_left hProduct
      exact sub_eq_zero.mp hDifference
    · intro hOrigins
      rw [hFactorization, hOrigins, sub_self, mul_zero]
  exact ⟨hMemory, hScalar, hAntisymmetric, hGaugeInvariant,
    hFactorization, hZeroCriterion⟩

#print axioms prime_swap_curvature_spec

end D5.S3.PrimeObserver.GoldenHolonomy.PrimeSwapCurvature
