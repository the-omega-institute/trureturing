/- GID: D5/S3/Factorization/PrimePowers/PrimeBudgetReadoutDichotomy
   generality: G
   mirror-B: D5/B/S3/Factorization/PrimePowers/PrimeBudgetReadoutDichotomy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Positive prime budgets split by CRT and compatible maps, including degeneracies. -/

/- Library-search audit trail (2026-08-25):
   * Current-tree hit `finite_crt_join` gives the horizontal CRT equivalence and is
     applied directly; no CRT argument is reproved here.
   * Current-tree hit `primePowerResidueReading` is checked pointwise against the new
     single-coordinate readout in the degenerate audit.
   * Pinned Mathlib hits `ZMod.castHom`, `ZMod.castHom_self`, `ZMod.castHom_comp`,
     `ZMod.cast_intCast`, and the generic `pow_dvd_pow`; all are used below.
   * The searched name `ZMod.natCast_self_eq_zero` was not present. The nearby
     `ZMod.natCast_eq_zero_iff` was not needed because `castHom` supplies the maps.
   * No packaged inverse-limit object is needed: identity, composition, and readout
     compatibility give exactly the requested inverse-system data. -/

import D5.S3.Factorization.PrimePowers.FiniteCrtJoin
import D5.S3.Factorization.PrimePowers.BoundedIntegerCrtCompleteness

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Factorization.PrimePowers.PrimeBudgetReadoutDichotomy

open D5.S3.Factorization.PrimePowers.FiniteCrtJoin
open D5.S3.Factorization.PrimePowers.BoundedIntegerCrtCompleteness

/-!
`PrimeBudget` requires positive exponents, as in the source's `Nat_{> 0}`.
The imported `primePowerProduct` is deliberately more general and permits zero
exponents; it must not be confused with the budget data itself.
-/

/-- A finite support of primes together with a positive exponent at every supported prime. -/
structure PrimeBudget where
  support : Finset Nat
  exponent : Nat -> Nat
  support_prime : forall p, p ∈ support -> Nat.Prime p
  exponent_pos : forall p, p ∈ support -> 0 < exponent p

/-- The single-coordinate reading of an integer modulo one prime power. -/
def primePowerReadout (p k : Nat) : Int -> ZMod (p ^ k) :=
  fun x => (x : ZMod (p ^ k))

/-- The natural reduction from precision `k'` to precision `k`, when `k <= k'`. -/
def primePowerProjection (p : Nat) {k k' : Nat} (hkk' : k <= k') :
    ZMod (p ^ k') →+* ZMod (p ^ k) :=
  ZMod.castHom (pow_dvd_pow p hkk') (ZMod (p ^ k))

/-- The horizontal CRT assertion attached to a positive prime budget. -/
def horizontalPrimeDecomposition (budget : PrimeBudget) : Prop :=
  Nonempty
    (ZMod (primePowerProduct budget.support budget.exponent) ≃+*
      forall p : budget.support, ZMod ((p : Nat) ^ budget.exponent p))

/-- Identity, composition, and readout compatibility for the precision projections. -/
def verticalPrimeInverseSystem (p : Nat) : Prop :=
  (forall k : Nat,
    primePowerProjection p (le_refl k) = RingHom.id (ZMod (p ^ k))) ∧
  (forall (k k' k'' : Nat) (hkk' : k <= k') (hk'k'' : k' <= k''),
    (primePowerProjection p hkk').comp (primePowerProjection p hk'k'') =
      primePowerProjection p (hkk'.trans hk'k'')) ∧
  (forall (k k' : Nat) (hkk' : k <= k') (x : Int),
    primePowerProjection p hkk' (primePowerReadout p k' x) =
      primePowerReadout p k x)

/-- The horizontal and vertical assertions packaged as one dichotomy. -/
def horizontalVerticalDichotomy (budget : PrimeBudget) : Prop :=
  horizontalPrimeDecomposition budget ∧
    forall p : budget.support, verticalPrimeInverseSystem p

/-- Distinct supported primes split as the existing dependent CRT product. -/
theorem horizontal_prime_decomposition (budget : PrimeBudget) :
    horizontalPrimeDecomposition budget := by
  exact finite_crt_join budget.support budget.exponent budget.support_prime

#print axioms horizontal_prime_decomposition

/-- At one prime, the precision reductions form a compatible inverse system of readouts. -/
theorem vertical_prime_inverse_system (p : Nat) :
    verticalPrimeInverseSystem p := by
  refine ⟨?_, ?_, ?_⟩
  · intro k
    exact ZMod.castHom_self
  · intro k k' k'' hkk' hk'k''
    exact ZMod.castHom_comp (pow_dvd_pow p hkk') (pow_dvd_pow p hk'k'')
  · intro k k' hkk' x
    exact ZMod.cast_intCast (pow_dvd_pow p hkk') x

#print axioms vertical_prime_inverse_system

/-- A positive prime budget has both its horizontal CRT and every vertical filtration. -/
theorem horizontal_vertical_dichotomy (budget : PrimeBudget) :
    horizontalVerticalDichotomy budget := by
  refine ⟨horizontal_prime_decomposition budget, ?_⟩
  intro p
  exact vertical_prime_inverse_system p

#print axioms horizontal_vertical_dichotomy

/-- Reversing the precision order can destroy the existence of a unital projection. -/
theorem precision_order_is_necessary :
    ¬Nonempty (ZMod (2 ^ 1) →+* ZMod (2 ^ 2)) := by
  rintro ⟨f⟩
  have hsource : (2 : ZMod (2 ^ 1)) = 0 := by decide
  have htarget : (2 : ZMod (2 ^ 2)) = 0 := by
    calc
      (2 : ZMod (2 ^ 2)) = f (2 : ZMod (2 ^ 1)) := by rw [map_ofNat]
      _ = f 0 := congrArg f hsource
      _ = 0 := map_zero f
  exact (by decide : (2 : ZMod (2 ^ 2)) ≠ 0) htarget

#print axioms precision_order_is_necessary

section DegenerateAudit

-- Empty support is a valid positive budget and its horizontal product is trivial.
example :
    horizontalPrimeDecomposition
      ({ support := ∅
         exponent := fun _ => 1
         support_prime := by simp
         exponent_pos := by simp } : PrimeBudget) := by
  apply horizontal_prime_decomposition

-- A singleton support is also covered without any pairwise side condition to discharge.
example :
    horizontalPrimeDecomposition
      ({ support := {2}
         exponent := fun _ => 1
         support_prime := by
           intro p hp
           have hp_two : p = 2 := Finset.mem_singleton.mp hp
           simpa [hp_two] using Nat.prime_two
         exponent_pos := by simp } : PrimeBudget) := by
  apply horizontal_prime_decomposition

-- At the first positive precision, readout commutes with its identity projection.
example (p : Nat) (x : Int) :
    primePowerProjection p (le_refl 1) (primePowerReadout p 1 x) =
      primePowerReadout p 1 x := by
  exact (vertical_prime_inverse_system p).2.2 1 1 (le_refl 1) x

-- Equal source and target precision gives the identity ring homomorphism.
example (p k : Nat) :
    primePowerProjection p (le_refl k) = RingHom.id (ZMod (p ^ k)) := by
  exact (vertical_prime_inverse_system p).1 k

-- Precision zero has modulus one, so its readout is constant.
example (p : Nat) (x y : Int) :
    primePowerReadout p 0 x = primePowerReadout p 0 y := by
  change (x : ZMod 1) = (y : ZMod 1)
  subsingleton

-- The zero integer reads as zero at every prime and every precision.
example (p k : Nat) : primePowerReadout p k 0 = 0 := by
  simp [primePowerReadout]

-- The existing joint readout is pointwise assembled from the new single-coordinate one.
example (N : Nat) (S : Finset Nat) (kappa : Nat -> Nat)
    (x : boundedIntegerWindow N) (p : S) :
    primePowerResidueReading N S kappa x p =
      primePowerReadout p (kappa p) x.val := by
  simp [primePowerResidueReading, primePowerReadout]

end DegenerateAudit

end D5.S3.Factorization.PrimePowers.PrimeBudgetReadoutDichotomy
