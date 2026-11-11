/- GID: D5/S3/Arith/Congruence/NonunitMultiplicationPeriod
   generality: G
   mirror-B: none(waiver:no-separate-boolean-mirror-claimed)
   mirror-E: none(waiver:symbolic-proof-no-numeric-artifact)
   anchors: [mathlib/module/Mathlib.Data.Nat.ModEq, mathlib/module/Mathlib.Data.ZMod.Basic, mathlib/module/Mathlib.GroupTheory.OrderOfElement]
   utility: none
   digest: Actual multiplication returns and minimal periods at arbitrary nonunit seeds. -/
module

public import Mathlib.Data.Nat.ModEq
public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.OrderOfElement

/-!
# Multiplication periods at nonunit modular seeds

The effective modulus of the seed `t` modulo positive `M` is `M / gcd t M`.
Mathlib's gcd cancellation gives the forward return implication; multiplication
by the removed gcd restores the reverse implication. We use congruences rather
than natural subtraction, so `u = 0` and exponent zero need no exceptions.

The return theorem is consumed by the minimal-period theorem. RadixFourNonunitZeroSubsets consumes that theorem in its full physical
separation conjunction. These are consumed bridges to pinned upstream results,
not a claim of a new order formula. The accepted PowerQuotientOrder is reused.

The centered integer doubleStep dynamics are a separate interface: no equality
with TwoRunSource.period follows without a centered-return bridge. The owning
prepared exposition is Blueprint/D5/S3/Arith/Congruence/
NonunitMultiplicationPeriod.scribe.cs; its projector/emit and Reg acceptance are
separate from the mathematical kernel check.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section

namespace D5.S3.Arith.Congruence.NonunitMultiplicationPeriod

private theorem mul_modEq_iff (M t a b : ℕ) (hM : 0 < M) :
    a * t ≡ b * t [MOD M] ↔ a ≡ b [MOD M / Nat.gcd t M] := by
  constructor
  · intro h
    simpa only [Nat.gcd_comm M t] using h.cancel_right_div_gcd hM
  · intro h
    have ht : Nat.gcd t M * (t / Nat.gcd t M) = t :=
      Nat.mul_div_cancel' (Nat.gcd_dvd_left t M)
    have hmod : M / Nat.gcd t M * Nat.gcd t M = M :=
      Nat.div_mul_cancel (Nat.gcd_dvd_right t M)
    simpa only [Nat.mul_assoc, ht, hmod] using
      ((h.mul_right' (Nat.gcd t M)).mul_right (t / Nat.gcd t M))

/-- An actual return of multiplication by `u` at seed `t` is exactly a power
return of `u` modulo the effective modulus. No unit or positivity assumption on
`u` or `t` is imposed; exponent zero and effective modulus one are included. -/
theorem isPeriodicPt_mul_natCast_iff (M u t e : ℕ) (hM : 0 < M) :
    Function.IsPeriodicPt (fun x : ZMod M => (u : ZMod M) * x) e (t : ZMod M) ↔
      (u : ZMod (M / Nat.gcd t M)) ^ e = 1 := by
  rw [Function.IsPeriodicPt, Function.IsFixedPt, mul_left_iterate_apply]
  have hcastM :
      ((u : ZMod M) ^ e * (t : ZMod M) = (t : ZMod M)) ↔
        u ^ e * t ≡ 1 * t [MOD M] := by
    simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_one, one_mul] using
      (ZMod.natCast_eq_natCast_iff (u ^ e * t) (1 * t) M)
  have hcastQ :
      (u : ZMod (M / Nat.gcd t M)) ^ e = 1 ↔
        u ^ e ≡ 1 [MOD M / Nat.gcd t M] := by
    simpa only [Nat.cast_pow, Nat.cast_one] using
      (ZMod.natCast_eq_natCast_iff (u ^ e) 1 (M / Nat.gcd t M))
  exact hcastM.trans ((mul_modEq_iff M t (u ^ e) 1 hM).trans hcastQ.symm)

/-- The actual seed minimal period equals the multiplicative order on the
effective modulus. Both sides use zero when there is no positive return; when
the effective modulus is one, both are one. -/
theorem minimalPeriod_mul_natCast (M u t : ℕ) (hM : 0 < M) :
    Function.minimalPeriod (fun x : ZMod M => (u : ZMod M) * x) (t : ZMod M) =
      orderOf (u : ZMod (M / Nat.gcd t M)) := by
  change Function.minimalPeriod
      (fun x : ZMod M => (u : ZMod M) * x) (t : ZMod M) =
    Function.minimalPeriod
      (fun x : ZMod (M / Nat.gcd t M) => (u : ZMod (M / Nat.gcd t M)) * x) 1
  apply Function.minimalPeriod_eq_minimalPeriod_iff.mpr
  intro e
  exact (isPeriodicPt_mul_natCast_iff M u t e hM).trans
    (isPeriodicPt_mul_iff_pow_eq_one (u : ZMod (M / Nat.gcd t M))).symm

end D5.S3.Arith.Congruence.NonunitMultiplicationPeriod
