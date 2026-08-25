/- GID: D5/S3/PrimeForms/PellFamilies/IntegralGeneralLinearLocalPeriodicity
   generality: G
   mirror-B: D5/B/S3/PrimeForms/PellFamilies/IntegralGeneralLinearLocalPeriodicity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Integral general-linear updates are pure-periodic modulo every prime power. -/

import D5.S3.PrimeForms.PellFamilies.LocalPellPeriodicity
import Mathlib.Dynamics.PeriodicPts.Lemmas
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/- Library-search audit trail (2026-08-25):
   * Body-shape searches for entrywise integer-to-`ZMod` matrix reduction found
     `LocalPellPeriodicity`, but its theorem is restricted to dimension two,
     determinant `1` or `-1`, and reductions of integer seeds; it also does not
     state that the local update is a permutation. It is therefore not an exact
     bind target for an arbitrary integral general-linear update.
   * Repository searches for `GeneralLinearGroup.map`, mapped general-linear
     `mulVec`, and pure periodicity found no D5 theorem on the general carrier.
     The related Pell-family module is imported as the existing family source.
   * Pinned Mathlib exact hits `Matrix.GeneralLinearGroup.map` and
     `Matrix.GeneralLinearGroup.toLin` construct the reduced invertible update.
     `Function.Injective.mem_periodicPts` supplies pure periodicity of every
     point on the resulting finite carrier. These declarations are applied
     directly below. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Matrix

namespace D5.S3.PrimeForms.PellFamilies.IntegralGeneralLinearLocalPeriodicity

/-- Reducing an integral general-linear matrix modulo a prime power gives a
permutation of the local vector states, and every orbit has a positive period
valid from time zero. -/
theorem integral_general_linear_update_is_prime_power_pure_periodic
    (dimension prime exponent : Nat)
    (integerUpdate : GL (Fin dimension) Int)
    (prime_is_prime : Nat.Prime prime) :
    let modulus := prime ^ exponent
    let reducedUpdate :=
      Matrix.GeneralLinearGroup.map (Int.castRingHom (ZMod modulus)) integerUpdate
    let update := fun state : Fin dimension -> ZMod modulus =>
      reducedUpdate.val.mulVec state
    Function.Bijective update /\
      forall initial,
        exists period, 0 < period /\
          Function.Periodic (fun time => (update^[time]) initial) period := by
  dsimp only
  let modulus := prime ^ exponent
  letI : NeZero modulus :=
    ⟨pow_ne_zero exponent prime_is_prime.ne_zero⟩
  let reducedUpdate :=
    Matrix.GeneralLinearGroup.map (Int.castRingHom (ZMod modulus)) integerUpdate
  let update := fun state : Fin dimension -> ZMod modulus =>
    reducedUpdate.val.mulVec state
  have update_bijective : Function.Bijective update := by
    let linearUnit := Matrix.GeneralLinearGroup.toLin reducedUpdate
    have update_eq :
        update =
          (LinearMap.GeneralLinearGroup.toLinearEquiv linearUnit :
            (Fin dimension -> ZMod modulus) -> Fin dimension -> ZMod modulus) := by
      funext state
      rfl
    rw [update_eq]
    exact (LinearMap.GeneralLinearGroup.toLinearEquiv linearUnit).bijective
  refine ⟨update_bijective, ?_⟩
  intro initial
  have initial_periodic : initial ∈ Function.periodicPts update :=
    update_bijective.1.mem_periodicPts initial
  rw [Function.mem_periodicPts] at initial_periodic
  obtain ⟨period, period_pos, returns⟩ := initial_periodic
  exact ⟨period, period_pos, returns.periodic_iterate⟩

#print axioms integral_general_linear_update_is_prime_power_pure_periodic

end D5.S3.PrimeForms.PellFamilies.IntegralGeneralLinearLocalPeriodicity
