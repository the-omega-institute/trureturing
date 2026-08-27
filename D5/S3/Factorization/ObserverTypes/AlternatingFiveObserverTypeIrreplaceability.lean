/- GID: D5/S3/Factorization/ObserverTypes/AlternatingFiveObserverTypeIrreplaceability
   generality: G
   mirror-B: D5/B/S3/Factorization/ObserverTypes/AlternatingFiveObserverTypeIrreplaceability
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A5 defeats every finite p-group observer but has a faithful mod-5 linear observer. -/

import D5.S3.Factorization.PrimePowers.SimpleToPGroupTrivial
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic
import Mathlib.RepresentationTheory.Basic

/- Library-search audit trail (2026-08-28):
   * The exact repository hit `alternating_five_hom_to_pgroup_trivial` supplies
     the universal prime-power quotient clause and is applied below rather than
     reproved. `alternating_five_residual_separation` corroborates the canonical
     joint-observer formulation but has no residue-linear witness.
   * Pinned Mathlib supplies `Representation.leftRegular`,
     `MonoidHom.toHomUnits`, and
     `LinearMap.GeneralLinearGroup.generalLinearEquiv`. These are composed
     directly; the only local fact is that the resulting observer recovers a
     group element from its action on the basis vector at the identity.
   * Loogle and LeanSearch returned the same left-regular family but no
     faithfulness theorem. GitHub code search found no exact external theorem
     packaging either the injectivity fact or this two-observer statement. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Factorization.ObserverTypes.AlternatingFiveObserverTypeIrreplaceability

open D5.S3.Factorization.PrimePowers.SimpleToPGroupTrivial

universe u v

/-- The two observer kinds compared at a fixed prime. -/
inductive LocalObserverKind where
  | primePowerQuotient
  | residueLinear
  deriving DecidableEq

/-- A common category for the two notions of observation at the same prime:
an object is either a homomorphism to a finite p-group or a residue-linear
representation over `ZMod p`. The constructors retain the target data that
certifies membership in the corresponding observer kind. -/
inductive LocalObserverAtPrime (p : Nat) (G : Type) [Group G] where
  | primePowerQuotient (P : Type) [Group P] [Finite P]
      (hP : IsPGroup p P) (observer : G →* P)
  | residueLinear (V : Type) [AddCommGroup V] [Module (ZMod p) V]
      (observer : G →* (V ≃ₗ[ZMod p] V))

namespace LocalObserverAtPrime

/-- Which of the two fixed-prime observer constructions produced an object. -/
def kind {p : Nat} {G : Type} [Group G] :
    LocalObserverAtPrime p G → LocalObserverKind
  | @LocalObserverAtPrime.primePowerQuotient _ _ _ _ _ _ _ _ =>
      .primePowerQuotient
  | @LocalObserverAtPrime.residueLinear _ _ _ _ _ _ _ => .residueLinear

/-- Faithfulness is injectivity of the underlying observer, uniformly across
the two constructors of `LocalObserverAtPrime`. -/
def Faithful {p : Nat} {G : Type} [Group G] :
    LocalObserverAtPrime p G → Prop
  | @LocalObserverAtPrime.primePowerQuotient _ _ _ _ _ _ _ observer =>
      Function.Injective observer
  | @LocalObserverAtPrime.residueLinear _ _ _ _ _ _ observer =>
      Function.Injective observer

end LocalObserverAtPrime

/-- The left regular representation, promoted through the units of the linear
endomorphism monoid to an observer valued in the general linear group. -/
noncomputable def leftRegularLinearObserver
    (k : Type u) [CommSemiring k] (G : Type v) [Group G] :
    G →* ((G →₀ k) ≃ₗ[k] (G →₀ k)) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv k (G →₀ k)).toMonoidHom.comp
    (Representation.leftRegular k G).toHomUnits

/-- A nontrivial coefficient semiring makes the left regular linear observer
faithful: its value on the basis vector at `1` records the acting group element. -/
theorem leftRegularLinearObserver_injective
    (k : Type u) [CommSemiring k] [Nontrivial k] (G : Type v) [Group G] :
    Function.Injective (leftRegularLinearObserver k G) := by
  intro g h observersEqual
  have basisImagesEqual :
      Finsupp.single g (1 : k) = Finsupp.single h (1 : k) := by
    simpa [leftRegularLinearObserver] using congrArg
      (fun observer : (G →₀ k) ≃ₗ[k] (G →₀ k) =>
        observer (Finsupp.single 1 (1 : k))) observersEqual
  exact Finsupp.single_left_injective one_ne_zero basisImagesEqual

/-- Every homomorphism from `A5` to a finite p-group is nonfaithful. This is
the observer-level consequence of the repository's exact triviality theorem. -/
theorem alternating_five_prime_power_observer_not_injective
    {p : Nat} (hp : p.Prime) {P : Type*} [Group P] [Finite P]
    (hP : IsPGroup p P) (observer : alternatingGroup (Fin 5) →* P) :
    ¬Function.Injective observer := by
  intro observerInjective
  have observerTrivial : IsTrivialHom observer :=
    alternating_five_hom_to_pgroup_trivial hp hP observer
  have sourceSubsingleton : Subsingleton (alternatingGroup (Fin 5)) :=
    ⟨fun g h => observerInjective ((observerTrivial g).trans (observerTrivial h).symm)⟩
  have sourceCardOne : Nat.card (alternatingGroup (Fin 5)) = 1 :=
    Nat.card_eq_one_iff_unique.mpr ⟨sourceSubsingleton, inferInstance⟩
  rw [nat_card_alternatingGroup] at sourceCardOne
  norm_num [Nat.factorial] at sourceCardOne

/-- Observer type irreplaceability for `A5`: every observer landing in any
finite p-group is nonfaithful, while a characteristic-five residue-linear
observer is faithful. Moreover, both are exhibited inside the common category
`LocalObserverAtPrime 5 G`, with distinct kinds and opposite fidelity. The
coefficient type `ZMod 5` records the characteristic, and linear equivalences
are the general linear group of the displayed module. -/
theorem alternating_five_observer_type_irreplaceability :
    ∃ (G : Type) (_ : Group G) (_ : Finite G),
      Nonempty (G ≃* alternatingGroup (Fin 5)) ∧
        (∀ (p : Nat), p.Prime →
          ∀ (P : Type) (_ : Group P) (_ : Finite P),
            IsPGroup p P →
              ∀ observer : G →* P, ¬Function.Injective observer) ∧
        (∃ (V : Type) (_ : AddCommGroup V) (_ : Module (ZMod 5) V),
          ∃ observer : G →* (V ≃ₗ[ZMod 5] V),
            Function.Injective observer) ∧
        ∃ blind faithful : LocalObserverAtPrime 5 G,
          blind.kind = .primePowerQuotient ∧
            faithful.kind = .residueLinear ∧
            blind.kind ≠ faithful.kind ∧
            ¬blind.Faithful ∧ faithful.Faithful := by
  letI : Fact (1 < (5 : Nat)) := ⟨by norm_num⟩
  let residueObserver :=
    leftRegularLinearObserver (ZMod 5) (alternatingGroup (Fin 5))
  have residueFaithful : Function.Injective residueObserver :=
    leftRegularLinearObserver_injective (ZMod 5) (alternatingGroup (Fin 5))
  have allPrimePowerBlind :
      ∀ (p : Nat), p.Prime →
        ∀ (P : Type) (_ : Group P) (_ : Finite P),
          IsPGroup p P →
            ∀ observer : alternatingGroup (Fin 5) →* P,
              ¬Function.Injective observer := by
    intro p hp P groupP finiteP hP observer
    letI : Group P := groupP
    letI : Finite P := finiteP
    exact alternating_five_prime_power_observer_not_injective hp hP observer
  refine ⟨alternatingGroup (Fin 5), inferInstance, inferInstance,
    ⟨MulEquiv.refl _⟩, allPrimePowerBlind, ?_, ?_⟩
  · exact ⟨alternatingGroup (Fin 5) →₀ ZMod 5, inferInstance,
      inferInstance, residueObserver, residueFaithful⟩
  · let blind : LocalObserverAtPrime 5 (alternatingGroup (Fin 5)) :=
      .primePowerQuotient (⊥ : Subgroup (alternatingGroup (Fin 5)))
        IsPGroup.of_bot 1
    let faithful : LocalObserverAtPrime 5 (alternatingGroup (Fin 5)) :=
      .residueLinear (alternatingGroup (Fin 5) →₀ ZMod 5) residueObserver
    refine ⟨blind, faithful, rfl, rfl, ?_, ?_, ?_⟩
    · simp [blind, faithful, LocalObserverAtPrime.kind]
    · simpa [blind, LocalObserverAtPrime.Faithful] using
        allPrimePowerBlind 5 Nat.prime_five
          (⊥ : Subgroup (alternatingGroup (Fin 5))) inferInstance inferInstance
          IsPGroup.of_bot 1
    · simpa [faithful, LocalObserverAtPrime.Faithful] using residueFaithful

/- Reverse probe: the public theorem alone yields a concrete nonfaithful
prime-power observer and, simultaneously, a faithful characteristic-five
linear observer on the same finite group identified with A5. -/
example :
    ∃ (G : Type) (_ : Group G) (_ : Finite G),
      Nonempty (G ≃* alternatingGroup (Fin 5)) ∧
        ¬Function.Injective (1 : G →* (⊥ : Subgroup G)) ∧
        ∃ (V : Type) (_ : AddCommGroup V) (_ : Module (ZMod 5) V),
          ∃ observer : G →* (V ≃ₗ[ZMod 5] V),
            Function.Injective observer := by
  rcases alternating_five_observer_type_irreplaceability with
    ⟨G, groupG, finiteG, identified, allPrimePowerBlind,
      ⟨V, addV, moduleV, residueObserver, residueFaithful⟩,
      _localObservationNotSingle⟩
  letI : Group G := groupG
  letI : Finite G := finiteG
  refine ⟨G, groupG, finiteG, identified, ?_, V, addV, moduleV,
    residueObserver, residueFaithful⟩
  exact allPrimePowerBlind 5 (by decide) (⊥ : Subgroup G) inferInstance
    inferInstance IsPGroup.of_bot 1

/- Trivialization probe: a one-element group cannot replace the existential
witness, because the public proposition identifies that witness with A5. -/
example : ¬Nonempty ((⊥ : Subgroup (alternatingGroup (Fin 5))) ≃*
    alternatingGroup (Fin 5)) := by
  rintro ⟨identified⟩
  have cardsEqual := Nat.card_congr identified.toEquiv
  have bottomCardOne : Nat.card (⊥ : Subgroup (alternatingGroup (Fin 5))) = 1 :=
    Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, inferInstance⟩
  rw [bottomCardOne, nat_card_alternatingGroup] at cardsEqual
  norm_num [Nat.factorial] at cardsEqual

/- The existential linear observer also cannot be replaced by the constant
observer: injectivity would again force A5 to be a singleton. -/
example : ¬Function.Injective
    (1 : alternatingGroup (Fin 5) →*
      ((alternatingGroup (Fin 5) →₀ ZMod 5) ≃ₗ[ZMod 5]
        (alternatingGroup (Fin 5) →₀ ZMod 5))) := by
  intro observerInjective
  have sourceSubsingleton : Subsingleton (alternatingGroup (Fin 5)) :=
    ⟨fun g h => observerInjective (by simp)⟩
  have sourceCardOne : Nat.card (alternatingGroup (Fin 5)) = 1 :=
    Nat.card_eq_one_iff_unique.mpr ⟨sourceSubsingleton, inferInstance⟩
  rw [nat_card_alternatingGroup] at sourceCardOne
  norm_num [Nat.factorial] at sourceCardOne

#print axioms leftRegularLinearObserver
#print axioms leftRegularLinearObserver_injective
#print axioms alternating_five_prime_power_observer_not_injective
#print axioms alternating_five_observer_type_irreplaceability

end D5.S3.Factorization.ObserverTypes.AlternatingFiveObserverTypeIrreplaceability
