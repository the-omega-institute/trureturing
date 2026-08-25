/- GID: D5/S3/Factorization/PrimePowers/CrtNilpotentAbelianVictory
   generality: G
   mirror-B: D5/B/S3/Factorization/PrimePowers/CrtNilpotentAbelianVictory
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Positive ZMod splits into Sylow factors; A5 blocks an unrestricted lift. -/

import D5.S3.Factorization.PrimePowers.FinitePrimePowerQuotientCompleteness
import D5.S3.Factorization.PrimePowers.SimpleToPGroupTrivial

/- Library-search audit trail (2026-08-25):
   * Current-tree exact hits `finite_prime_power_quotient_completeness_tfae` and
     `primePowerQuotientObserver` supply the Sylow clause and the observer.
   * Current-tree exact hit `alternating_five_hom_to_pgroup_trivial` supplies the A5
     obstruction; this module does not reprove its simplicity or p-group argument.
   * Pinned Mathlib exact hits `CommGroup.isNilpotent`, `ZMod.infinite`,
     `Nat.card_eq_zero_of_infinite`, `Nat.primeFactors_zero`, and
     `alternatingGroup.isMulCommutative_iff_card_le_three` close the glue and audits.
   * No current-tree declaration connects these hits specifically to additive `ZMod n`. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Factorization.PrimePowers.CrtNilpotentAbelianVictory

open D5.S3.Factorization.PrimePowers.FinitePrimePowerQuotientCompleteness
open D5.S3.Factorization.PrimePowers.SimpleToPGroupTrivial

universe u

/-- A group is the direct product of all of its Sylow subgroups. -/
def SylowPrimePowerDecomposable (G : Type u) [Group G] : Prop :=
  Nonempty
    ((∀ p : (Nat.card G).primeFactors,
      ∀ P : Sylow p G, (P : Subgroup G)) ≃* G)

/-- Every homomorphism from the group to a finite p-group is trivial. -/
def AllPrimePrimaryHomomorphismsTrivial (G : Type u) [Group G] : Prop :=
  ∀ (P : Type u) [Group P] [Finite P] (p : Nat),
    p.Prime → IsPGroup p P → ∀ phi : G →* P, IsTrivialHom phi

/-- A prime-primary decomposition counterexample is noncommutative, invisible to
all finite p-group homomorphisms, and not separated by the canonical observer. -/
def PrimePrimaryDecompositionCounterexample (G : Type u) [Group G] : Prop :=
  (¬ ∀ x y : G, x * y = y * x) ∧
    AllPrimePrimaryHomomorphismsTrivial G ∧
      ¬ Function.Injective (primePowerQuotientObserver G)

/-- `Multiplicative (ZMod n)` is the multiplicative wrapper for the additive group of
`ZMod n`; its multiplication is the original addition, not multiplication in the ring. -/
theorem zmod_additive_group_is_prime_power_decomposable (n : Nat) [NeZero n] :
    SylowPrimePowerDecomposable (Multiplicative (ZMod n)) := by
  exact
    ((finite_prime_power_quotient_completeness_tfae
      (G := Multiplicative (ZMod n))).out 3 4 rfl rfl).mp
      (inferInstance : Group.IsNilpotent (Multiplicative (ZMod n)))

#print axioms zmod_additive_group_is_prime_power_decomposable

/-- `NeZero n` is necessary: at `n = 0`, the Sylow product has empty prime index,
whereas the additive group of `ZMod 0 = Int` is nontrivial. -/
theorem ne_zero_is_necessary_for_zmod_sylow_decomposition :
    ¬ SylowPrimePowerDecomposable (Multiplicative (ZMod 0)) := by
  rintro ⟨sylowProduct⟩
  haveI : IsEmpty (Nat.card (Multiplicative (ZMod 0))).primeFactors := by
    constructor
    intro primeIndex
    simpa [Nat.card_eq_zero_of_infinite] using primeIndex.2
  exact
    not_subsingleton (Multiplicative (ZMod 0))
      sylowProduct.symm.injective.subsingleton

#print axioms ne_zero_is_necessary_for_zmod_sylow_decomposition

-- Degenerate audit: the trivial modulus, a prime modulus, and a prime-power modulus.
example : SylowPrimePowerDecomposable (Multiplicative (ZMod 1)) :=
  zmod_additive_group_is_prime_power_decomposable 1

example : SylowPrimePowerDecomposable (Multiplicative (ZMod 2)) :=
  zmod_additive_group_is_prime_power_decomposable 2

example : SylowPrimePowerDecomposable (Multiplicative (ZMod 4)) :=
  zmod_additive_group_is_prime_power_decomposable 4

-- Empty source types are excluded definitionally: a group supplies an identity element.
example : ¬ Nonempty (Group Empty) := by
  rintro ⟨emptyGroup⟩
  letI : Group Empty := emptyGroup
  exact Empty.elim (1 : Empty)

/-- An existential counterexample, not a claim about every noncommutative group: `A5`
has only trivial maps to finite p-groups, so its prime-power observer is not injective. -/
theorem prime_primary_decomposition_does_not_lift :
    ∃ (G : Type) (_ : Group G) (_ : Finite G),
      PrimePrimaryDecompositionCounterexample G := by
  let A5 := alternatingGroup (Fin 5)
  have allTrivial : AllPrimePrimaryHomomorphismsTrivial A5 := by
    intro P _ _ p hp hP phi
    exact alternating_five_hom_to_pgroup_trivial hp hP phi
  have noncommutative : ¬ ∀ x y : A5, x * y = y * x := by
    intro commutes
    have small : Nat.card (Fin 5) ≤ 3 :=
      alternatingGroup.isMulCommutative_iff_card_le_three.mp
        (isMulCommutative_iff.mpr commutes)
    norm_num at small
  refine ⟨A5, inferInstance, inferInstance, noncommutative, allTrivial, ?_⟩
  intro observerInjective
  obtain ⟨x, y, different⟩ := exists_pair_ne A5
  apply different
  apply observerInjective
  funext quotientIndex
  rcases quotientIndex.2 with ⟨p, hp, hP⟩
  change
    (QuotientGroup.mk' quotientIndex.1.toSubgroup) x =
      (QuotientGroup.mk' quotientIndex.1.toSubgroup) y
  have quotientMapTrivial :=
    allTrivial (A5 ⧸ quotientIndex.1.toSubgroup) p hp hP
      (QuotientGroup.mk' quotientIndex.1.toSubgroup)
  exact (quotientMapTrivial x).trans (quotientMapTrivial y).symm

#print axioms prime_primary_decomposition_does_not_lift

-- The identity map on A5 is nontrivial, so it cannot be among the finite p-group targets.
example :
    ¬ IsTrivialHom
      (MonoidHom.id (alternatingGroup (Fin 5))) := by
  intro identityTrivial
  obtain ⟨x, y, different⟩ := exists_pair_ne (alternatingGroup (Fin 5))
  apply different
  exact (identityTrivial x).trans (identityTrivial y).symm

-- The constant map to the trivial p-group is covered by the imported A5 theorem.
example :
    IsTrivialHom
      (1 : alternatingGroup (Fin 5) →* (⊥ : Subgroup (alternatingGroup (Fin 5)))) :=
  alternating_five_hom_to_pgroup_trivial Nat.prime_two IsPGroup.of_bot 1

/-- The finite additive CRT side and the noncommutative obstruction packaged together. -/
theorem crt_is_a_nilpotent_abelian_victory (n : Nat) [NeZero n] :
    SylowPrimePowerDecomposable (Multiplicative (ZMod n)) ∧
      ∃ (G : Type) (_ : Group G) (_ : Finite G),
        PrimePrimaryDecompositionCounterexample G :=
  ⟨zmod_additive_group_is_prime_power_decomposable n,
    prime_primary_decomposition_does_not_lift⟩

#print axioms crt_is_a_nilpotent_abelian_victory

#print axioms SylowPrimePowerDecomposable
#print axioms AllPrimePrimaryHomomorphismsTrivial
#print axioms PrimePrimaryDecompositionCounterexample

end D5.S3.Factorization.PrimePowers.CrtNilpotentAbelianVictory
