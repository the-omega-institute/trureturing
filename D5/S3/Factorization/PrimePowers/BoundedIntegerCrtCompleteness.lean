/- GID: D5/S3/Factorization/PrimePowers/BoundedIntegerCrtCompleteness
   generality: G
   mirror-B: D5/B/S3/Factorization/PrimePowers/BoundedIntegerCrtCompleteness
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Bounded CRT is exact, including zero N, empty support, and zero exponents. -/

/- Library-search audit trail (2026-08-25):
   * Exact current-tree hit `retained_residue_recovery_iff_product_capacity`
     supplies the pigeonhole direction for arbitrary positive pairwise-coprime
     moduli and is applied directly after specializing to prime powers.
   * Required current-tree hit `finite_crt_join` supplies the reverse CRT
     reconstruction and retains zero-exponent `ZMod 1` coordinates.
   * `residue_reading_injOn_iff_primorial_gt` instead uses the inclusive window
     `[0, N]`, the first primes, and exponent one, so it is not a covering result.
   * Pinned Mathlib hits `Fintype.card_le_of_injective` inside the retained-moduli
     theorem; the searched `Finset.card_le_card_of_injOn` and
     `Finset.exists_ne_map_eq_of_card_lt_of_maps_to` were not needed here. -/

import D5.S3.ConceptDynamics.ResidueCoding.RetainedResidueRecoveryCriterion
import D5.S3.Factorization.PrimePowers.FiniteCrtJoin

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Factorization.PrimePowers.BoundedIntegerCrtCompleteness

open D5.S3.ConceptDynamics.Faithfulness.JointFaithfulnessLeibnizCriterion
open D5.S3.ConceptDynamics.ResidueCoding.RetainedResidueRecoveryCriterion
open D5.S3.Factorization.PrimePowers.FiniteCrtJoin
open scoped Function

/-!
We represent the source's `X_N` by `Fin N`, the type of the `N` integers
`0, ..., N - 1`. This is the typed form of `Finset.range N`, not the inclusive
interval `[0, N]`; consequently the exact capacity condition is `N <= M`.

The degenerate cases are part of the same convention: `X_0` is empty, `X_1`
is a singleton, empty prime support has product one, and zero exponents retain
only trivial `ZMod 1` coordinates.
-/

/-- The bounded integer window `X_N = {0, ..., N - 1}`, represented as a finite type. -/
def boundedIntegerWindow (N : Nat) : Type :=
  Fin N

/-- The joint residue readout on `X_N` for the supplied prime-power coordinates. -/
def primePowerResidueReading (N : Nat) (S : Finset Nat) (kappa : Nat -> Nat) :
    boundedIntegerWindow N -> forall p : S, ZMod ((p : Nat) ^ kappa p) :=
  fun x _p => x.val

/-- Prime-power residues separate `0, ..., N - 1` exactly when their product
has at least `N` residue classes. -/
theorem bounded_integer_crt_complete_iff
    (N : Nat) (S : Finset Nat) (kappa : Nat -> Nat)
    (hS : forall p, p ∈ S -> Nat.Prime p) :
    Function.Injective (primePowerResidueReading N S kappa) ↔
      N ≤ primePowerProduct S kappa := by
  classical
  have hpositive : forall p : S, 0 < (p : Nat) ^ kappa p := by
    intro p
    exact pow_pos (hS p p.property).pos _
  have hcoprime :
      Pairwise (Nat.Coprime on fun p : S => (p : Nat) ^ kappa p) := by
    intro p q hpq
    exact Nat.coprime_pow_primes (kappa p) (kappa q)
      (hS p p.property) (hS q q.property) (Subtype.coe_ne_coe.mpr hpq)
  have hproduct :
      primePowerProduct S kappa = ∏ p : S, (p : Nat) ^ kappa p := by
    exact Finset.prod_subtype S (fun _ => Iff.rfl) (fun p => p ^ kappa p)
  constructor
  · intro hinjective
    have hretained :
        Function.Injective
          (jointReadout (fun p : S =>
            fun x : Fin N => (x.val : ZMod ((p : Nat) ^ kappa p)))) := by
      intro x y hsame
      apply hinjective
      funext p
      simp only [primePowerResidueReading]
      simpa [jointReadout] using congrFun hsame p
    have hcapacity : N ≤ ∏ p : S, (p : Nat) ^ kappa p :=
      (retained_residue_recovery_iff_product_capacity
        (fun p : S => (p : Nat) ^ kappa p) N hpositive hcoprime).1 hretained
    simpa only [hproduct] using hcapacity
  · intro hcapacity x y hsame
    rcases finite_crt_join S kappa hS with ⟨crt⟩
    apply Fin.ext
    have hmod :
        (x.val : ZMod (primePowerProduct S kappa)) =
          (y.val : ZMod (primePowerProduct S kappa)) := by
      apply crt.injective
      funext p
      simpa [primePowerResidueReading, boundedIntegerWindow] using congrFun hsame p
    have hmodeq : x.val ≡ y.val [MOD primePowerProduct S kappa] :=
      (ZMod.natCast_eq_natCast_iff x.val y.val (primePowerProduct S kappa)).mp hmod
    exact hmodeq.eq_of_lt_of_lt
      (x.isLt.trans_le hcapacity) (y.isLt.trans_le hcapacity)

#print axioms bounded_integer_crt_complete_iff

/-- Dropping the prime-support restriction admits overlapping moduli and invalidates
the product-capacity criterion. -/
theorem prime_support_condition_is_necessary :
    ¬(Function.Injective
        (primePowerResidueReading 5 {2, 4} (fun _ => 1)) ↔
      5 ≤ primePowerProduct {2, 4} (fun _ => 1)) := by
  intro hcriterion
  have hcapacity : 5 ≤ primePowerProduct {2, 4} (fun _ => 1) := by
    norm_num [primePowerProduct]
  have hinjective := hcriterion.mpr hcapacity
  let x : boundedIntegerWindow 5 := ⟨0, by decide⟩
  let y : boundedIntegerWindow 5 := ⟨4, by decide⟩
  have hsame :
      primePowerResidueReading 5 {2, 4} (fun _ => 1) x =
        primePowerResidueReading 5 {2, 4} (fun _ => 1) y := by
    funext p
    dsimp [primePowerResidueReading, x, y]
    have hp : (p : Nat) = 2 ∨ (p : Nat) = 4 := by
      simpa only [Finset.mem_insert, Finset.mem_singleton] using p.property
    rcases hp with hp | hp
    · rw [hp, pow_one]
      decide
    · rw [hp, pow_one]
      decide
  have hxy : x = y := hinjective hsame
  have hval := congrArg Fin.val hxy
  norm_num [x, y] at hval

#print axioms prime_support_condition_is_necessary

-- Degenerate audit: `X_0` is empty, so every readout from it is injective.
example (S : Finset Nat) (kappa : Nat -> Nat) :
    Function.Injective (primePowerResidueReading 0 S kappa) := by
  intro x
  exact Fin.elim0 x

-- Empty support gives a constant readout into the one-element empty product.
example (N : Nat) (kappa : Nat -> Nat) :
    Function.Injective (primePowerResidueReading N ∅ kappa) ↔ N ≤ 1 := by
  simpa [primePowerProduct] using
    bounded_integer_crt_complete_iff N ∅ kappa (by simp)

-- Hence the constant empty-support readout is injective on the singleton window.
example (kappa : Nat -> Nat) :
    Function.Injective (primePowerResidueReading 1 ∅ kappa) := by
  exact (bounded_integer_crt_complete_iff 1 ∅ kappa (by simp)).2 (by
    simp [primePowerProduct])

-- The same constant readout is not injective once the window has two elements.
example (kappa : Nat -> Nat) :
    ¬Function.Injective (primePowerResidueReading 2 ∅ kappa) := by
  rw [bounded_integer_crt_complete_iff 2 ∅ kappa (by simp)]
  simp [primePowerProduct]

-- All-zero exponents likewise leave only trivial coordinates and capacity one.
example (N : Nat) :
    Function.Injective
        (primePowerResidueReading N {2, 3} (fun _ => 0)) ↔ N ≤ 1 := by
  simpa [primePowerProduct] using
    bounded_integer_crt_complete_iff N {2, 3} (fun _ => 0) (by
      intro p hp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl
      · exact Nat.prime_two
      · exact Nat.prime_three)

-- Primality is not pointwise necessary: one positive composite modulus is faithful below it.
example :
    Function.Injective (primePowerResidueReading 4 {4} (fun _ => 1)) := by
  intro x y hsame
  apply Fin.ext
  have hmod : (x.val : ZMod 4) = (y.val : ZMod 4) := by
    simpa [primePowerResidueReading] using congrFun hsame ⟨4, by simp⟩
  exact ((ZMod.natCast_eq_natCast_iff x.val y.val 4).mp hmod).eq_of_lt_of_lt
    x.isLt y.isLt

end D5.S3.Factorization.PrimePowers.BoundedIntegerCrtCompleteness
