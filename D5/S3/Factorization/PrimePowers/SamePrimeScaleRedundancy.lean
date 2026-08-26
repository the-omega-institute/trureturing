/- GID: D5/S3/Factorization/PrimePowers/SamePrimeScaleRedundancy
   generality: G
   mirror-B: D5/B/S3/Factorization/PrimePowers/SamePrimeScaleRedundancy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Adjacent same-base fibers coincide; zero depth and the 2/3 contrast are audited. -/

/- Library-search audit trail (2026-08-26):
   * The requested D5 search for p-adic, valuation, residue, and local-observation
     terms found `PadicPrecisionBlindSpot.precisionReading` and the exact ZMod
     interface in `PrimeBudgetReadoutDichotomy`; the latter is reused here.
   * `primePowerReadout` is the canonical integer-to-ZMod reading, while
     `primePowerProjection` is already defined by Mathlib's `ZMod.castHom`.
     Its public `vertical_prime_inverse_system` theorem supplies compatibility.
   * `CompatiblePrecisionTowerMonotonicity` proves abstract refinement and kernel
     inclusion, but not equality of the adjacent joint and high-level fibers.
   * Repository and digest searches found no theorem supplying that fiber equality
     together with a strict two-prime counterexample. Mathlib's
     `Set.ssubset_iff_exists` packages the latter as strict kernel containment.
-/

import D5.S3.Factorization.PrimePowers.PrimeBudgetReadoutDichotomy
import Mathlib.Data.Set.Basic
import Mathlib.Data.Setoid.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Factorization.PrimePowers.SamePrimeScaleRedundancy

open D5.S3.Factorization.PrimePowers.PrimeBudgetReadoutDichotomy

/-- The joint interface formed from two adjacent precision readings at one base. -/
def adjacentPrimePowerReadout (p k : Nat) :
    Int -> ZMod (p ^ k) × ZMod (p ^ (k + 1)) :=
  fun x => (primePowerReadout p k x, primePowerReadout p (k + 1) x)

/-- The joint interface formed from two bases at the same precision. -/
def sameLevelPrimePairReadout (p q k : Nat) :
    Int -> ZMod (p ^ k) × ZMod (q ^ k) :=
  fun x => (primePowerReadout p k x, primePowerReadout q k x)

/-- The old layer is the explicit `ZMod.castHom` projection of the new layer.
No primality or lower-bound assumption on `p` is needed. -/
theorem old_layer_factors_through_new (p k : Nat) :
    primePowerReadout p k =
      primePowerProjection p (Nat.le_succ k) ∘ primePowerReadout p (k + 1) := by
  funext x
  symm
  exact (vertical_prime_inverse_system p).2.2 k (k + 1) (Nat.le_succ k) x
#print axioms old_layer_factors_through_new

/-- Adding the old layer to the new one leaves the equality fiber unchanged. -/
theorem adjacent_joint_same_fiber (p k : Nat) (x y : Int) :
    adjacentPrimePowerReadout p k x = adjacentPrimePowerReadout p k y <->
      primePowerReadout p (k + 1) x = primePowerReadout p (k + 1) y := by
  constructor
  · exact fun sameJoint => congrArg Prod.snd sameJoint
  · intro sameNew
    apply Prod.ext
    · change primePowerReadout p k x = primePowerReadout p k y
      rw [old_layer_factors_through_new p k]
      exact congrArg (primePowerProjection p (Nat.le_succ k)) sameNew
    · exact sameNew
#print axioms adjacent_joint_same_fiber

/-- Precision zero has modulus one, hence one fiber for every base. -/
theorem zero_precision_readout_is_constant (p : Nat) (x y : Int) :
    primePowerReadout p 0 x = primePowerReadout p 0 y := by
  change (x : ZMod 1) = (y : ZMod 1)
  subsingleton
#print axioms zero_precision_readout_is_constant

/-- At base two, precisions one and two are exactly congruence modulo two and four. -/
theorem two_adjacent_precision_fibers (x y : Int) :
    (primePowerReadout 2 1 x = primePowerReadout 2 1 y <-> (2 : Int) ∣ y - x) ∧
      (primePowerReadout 2 2 x = primePowerReadout 2 2 y <-> (4 : Int) ∣ y - x) := by
  constructor
  · change ((x : ZMod 2) = (y : ZMod 2) <-> (2 : Int) ∣ y - x)
    exact ZMod.intCast_eq_intCast_iff_dvd_sub x y 2
  · change ((x : ZMod 4) = (y : ZMod 4) <-> (4 : Int) ∣ y - x)
    exact ZMod.intCast_eq_intCast_iff_dvd_sub x y 4
#print axioms two_adjacent_precision_fibers

/-- Repeating one prime at one level is a redundant diagonal pair. -/
theorem repeated_prime_pair_same_fiber (p k : Nat) (x y : Int) :
    sameLevelPrimePairReadout p p k x = sameLevelPrimePairReadout p p k y <->
      primePowerReadout p k x = primePowerReadout p k y := by
  simp [sameLevelPrimePairReadout]
#print axioms repeated_prime_pair_same_fiber

/-- At precision one, the joint readings at two and three strictly refine each
single reading: zero versus two witnesses strictness over two, and zero versus
three witnesses strictness over three. -/
theorem different_prime_joint_strictly_finer :
    {pair : Int × Int |
        Setoid.ker (sameLevelPrimePairReadout 2 3 1) pair.1 pair.2} ⊂
      {pair : Int × Int | Setoid.ker (primePowerReadout 2 1) pair.1 pair.2} ∧
    {pair : Int × Int |
        Setoid.ker (sameLevelPrimePairReadout 2 3 1) pair.1 pair.2} ⊂
      {pair : Int × Int | Setoid.ker (primePowerReadout 3 1) pair.1 pair.2} := by
  constructor
  · apply Set.ssubset_iff_exists.mpr
    constructor
    · intro pair sameJoint
      exact congrArg Prod.fst sameJoint
    · refine ⟨(0, 2), ?_, ?_⟩
      · change (0 : ZMod 2) = (2 : ZMod 2)
        decide
      · change ((0 : ZMod 2), (0 : ZMod 3)) ≠
          ((2 : ZMod 2), (2 : ZMod 3))
        decide
  · apply Set.ssubset_iff_exists.mpr
    constructor
    · intro pair sameJoint
      exact congrArg Prod.snd sameJoint
    · refine ⟨(0, 3), ?_, ?_⟩
      · change (0 : ZMod 3) = (3 : ZMod 3)
        decide
      · change ((0 : ZMod 2), (0 : ZMod 3)) ≠
          ((3 : ZMod 2), (3 : ZMod 3))
        decide
#print axioms different_prime_joint_strictly_finer

section DegenerateAudit

-- Empty carriers make both pulled-back fiber relations vacuous.
example (p k : Nat) :
    adjacentPrimePowerReadout p k ∘ (Empty.elim : Empty -> Int) =
      fun x : Empty => x.elim := by
  funext x
  exact x.elim

-- A singleton carrier gives one fiber for both the joint and high readouts.
example (p k : Nat) (x y : Unit) :
    adjacentPrimePowerReadout p k ((fun _ : Unit => (0 : Int)) x) =
        adjacentPrimePowerReadout p k ((fun _ : Unit => (0 : Int)) y) <->
      primePowerReadout p (k + 1) ((fun _ : Unit => (0 : Int)) x) =
        primePowerReadout p (k + 1) ((fun _ : Unit => (0 : Int)) y) := by
  exact adjacent_joint_same_fiber p k _ _

-- Base one is a constant readout at every precision.
example (k : Nat) (x y : Int) :
    primePowerReadout 1 k x = primePowerReadout 1 k y := by
  unfold primePowerReadout
  rw [one_pow]
  subsingleton

-- Equal precision gives the identity projection.
example (p k : Nat) :
    primePowerProjection p (le_refl k) = RingHom.id (ZMod (p ^ k)) := by
  exact (vertical_prime_inverse_system p).1 k

-- Zero reads as zero for every base and precision.
example (p k : Nat) : primePowerReadout p k 0 = 0 := by
  simp [primePowerReadout]

end DegenerateAudit

end D5.S3.Factorization.PrimePowers.SamePrimeScaleRedundancy
