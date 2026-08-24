/- GID: D5/S3/Arith/Congruence/PrimePowerTowerInjective
   generality: G
   mirror-B: D5/B/S3/Arith/Congruence/PrimePowerTowerInjective
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Reduction of an integer in every positive prime-power quotient is injective, with equality characterized componentwise; indexing by k + 1 omits the trivial quotient at exponent zero. -/

import Mathlib.Data.ZMod.Basic
import D5.S3.Arith.Congruence.PadicPrecisionBlindSpot

/- Library-search audit trail (2026-08-24):
   * `rg -n -F 'precision_tower_injective' D5 Golden/Frozen/accepted` returned no
     matches. Broader searches for `precisionTower`, `precision_tower`, and tower
     injectivity found only `first_distinguishing_precision` in
     `PadicPrecisionBlindSpot`; no private declaration covered the product map.
   * All nine existing modules in `D5/S3/Arith/Congruence/` were read by digest.
     `PadicPrecisionBlindSpot` supplies the least distinguishing precision, but no
     module defines the dependent product of positive prime-power quotients or proves
     its injectivity.
   * Pinned Mathlib contains `ZMod.intCast_zmod_eq_zero_iff_dvd`,
     `Int.eq_zero_of_abs_lt_dvd`, and `Nat.lt_pow_self`; the requested search for
     `ZMod.natCast_self_eq_zero` found no declaration under that exact name. Searches
     for an integer-to-prime-power-tower injectivity theorem found no exact match.
   * The proof reuses `first_distinguishing_precision`; it does not reprove any
     valuation or divisibility result.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.Congruence.PrimePowerTowerInjective

open D5.S3.Arith.Congruence.PadicPrecisionBlindSpot

/-- The compatible family of reductions of an integer modulo `p ^ (k + 1)`.
The shifted index records exactly the positive precisions from the source theorem. -/
noncomputable def precisionTower (p : Nat) (x : Int) :
    (k : Nat) -> ZMod (p ^ (k + 1)) :=
  fun _ => x

/-- An integer is determined by all of its positive prime-power reductions. -/
theorem precision_tower_injective (p : Nat) (hp : p.Prime) :
    Function.Injective (precisionTower p) := by
  intro x y htower
  by_contra hxy
  let v := padicValInt p (x - y)
  have hcomponent :
      (x : ZMod (p ^ (v + 1))) = (y : ZMod (p ^ (v + 1))) := by
    simpa [precisionTower, v] using congrFun htower v
  have hreading : precisionReading p (v + 1) x = precisionReading p (v + 1) y := by
    simpa [precisionReading, Int.natCast_pow] using
      (ZMod.intCast_eq_intCast_iff' x y (p ^ (v + 1))).mp hcomponent
  exact (first_distinguishing_precision p x y hp hxy).1 hreading

/-- Equality in the prime-power precision tower is equivalent to integer equality. -/
theorem precision_tower_eq_iff (p : Nat) (hp : p.Prime) (x y : Int) :
    precisionTower p x = precisionTower p y <-> x = y := by
  constructor
  · intro htower
    exact precision_tower_injective p hp htower
  · exact congrArg (precisionTower p)

example : Function.Injective (precisionTower 2) :=
  precision_tower_injective 2 (by decide)

#print axioms precision_tower_injective

end D5.S3.Arith.Congruence.PrimePowerTowerInjective
