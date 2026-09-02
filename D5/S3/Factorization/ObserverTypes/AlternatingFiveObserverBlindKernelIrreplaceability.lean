/- GID: D5/S3/Factorization/ObserverTypes/AlternatingFiveObserverBlindKernelIrreplaceability
   generality: G
   mirror-B: D5/B/S3/Factorization/ObserverTypes/AlternatingFiveObserverBlindKernelIrreplaceability
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A5 has a full prime-power blind kernel and a faithful mod-five linear observer. -/

import D5.S3.Factorization.ObserverTypes.AlternatingFiveObserverTypeIrreplaceability
import D5.S3.Factorization.PrimePowers.AlternatingFiveResidualSeparation

/- Library-search audit trail (2026-09-02):
   * The frozen owner `alternating_five_observer_type_irreplaceability` supplies
     the finite A5 witness, universal noninjectivity, faithful characteristic-five
     linear observer, and the same-prime observer-kind contrast.
   * Exact repository hits `alternating_five_hom_to_pgroup_trivial`,
     `primePowerResidual`, and `primePowerQuotientObserver` supply the missing
     full-blind-kernel formulation; no second observer or residual is defined here.
   * Searches of the current D5 tree and pinned Mathlib found no single theorem
     combining the full blind kernel with the faithful residue-linear witness. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Factorization.ObserverTypes.AlternatingFiveObserverBlindKernelIrreplaceability

open D5.S3.Factorization.ObserverTypes.AlternatingFiveObserverTypeIrreplaceability
open D5.S3.Factorization.PrimePowers.FinitePrimePowerQuotientCompleteness
open D5.S3.Factorization.PrimePowers.SimpleToPGroupTrivial

/-- Observer-type irreplaceability with the blind residual made public: every
finite p-group observer of the displayed A5 model is the trivial homomorphism,
so their canonical joint observer is constant and its kernel is the whole group.
In contrast, a characteristic-five linear observer is injective and has trivial
kernel; the two observer kinds also have opposite fidelity at the same prime. -/
theorem alternating_five_observer_blind_kernel_irreplaceability :
    ∃ (G : Type) (_ : Group G) (_ : Finite G),
      Nonempty (G ≃* alternatingGroup (Fin 5)) ∧
        (∀ (p : Nat), p.Prime →
          ∀ (P : Type) (_ : Group P) (_ : Finite P),
            IsPGroup p P →
              ∀ observer : G →* P,
                ¬Function.Injective observer ∧ IsTrivialHom observer) ∧
        primePowerResidual G = ⊤ ∧
        primePowerQuotientObserver G = 1 ∧
        (∃ (V : Type) (_ : AddCommGroup V) (_ : Module (ZMod 5) V),
          ∃ observer : G →* (V ≃ₗ[ZMod 5] V),
            Function.Injective observer ∧ observer.ker = ⊥) ∧
        ∃ blind faithful : LocalObserverAtPrime 5 G,
          blind.kind = .primePowerQuotient ∧
            faithful.kind = .residueLinear ∧
            blind.kind ≠ faithful.kind ∧
            ¬blind.Faithful ∧ faithful.Faithful := by
  rcases alternating_five_observer_type_irreplaceability with
    ⟨G, groupG, finiteG, ⟨identified⟩, allPrimePowerNonfaithful,
      ⟨V, addV, moduleV, residueObserver, residueFaithful⟩, localContrast⟩
  letI : Group G := groupG
  letI : Finite G := finiteG
  have allPrimePowerTrivial :
      ∀ (p : Nat), p.Prime →
        ∀ (P : Type) (_ : Group P) (_ : Finite P),
          IsPGroup p P → ∀ observer : G →* P, IsTrivialHom observer := by
    intro p hp P groupP finiteP hP observer g
    letI : Group P := groupP
    letI : Finite P := finiteP
    have transported := alternating_five_hom_to_pgroup_trivial hp hP
      (observer.comp identified.symm.toMonoidHom) (identified g)
    simpa using transported
  have allPrimePowerBlind :
      ∀ (p : Nat), p.Prime →
        ∀ (P : Type) (_ : Group P) (_ : Finite P),
          IsPGroup p P →
            ∀ observer : G →* P,
              ¬Function.Injective observer ∧ IsTrivialHom observer := by
    intro p hp P groupP finiteP hP observer
    exact ⟨allPrimePowerNonfaithful p hp P groupP finiteP hP observer,
      allPrimePowerTrivial p hp P groupP finiteP hP observer⟩
  have residualTop : primePowerResidual G = ⊤ := by
    apply top_unique
    rw [primePowerResidual]
    refine le_iInf fun H => ?_
    intro g _
    apply (QuotientGroup.eq_one_iff g).mp
    rcases H.2 with ⟨p, hp, hP⟩
    exact allPrimePowerTrivial p hp _ inferInstance inferInstance hP
      (QuotientGroup.mk' H.1.toSubgroup) g
  have jointObserverTrivial : primePowerQuotientObserver G = 1 := by
    ext g H
    rcases H.2 with ⟨p, hp, hP⟩
    exact allPrimePowerTrivial p hp _ inferInstance inferInstance hP
      (QuotientGroup.mk' H.1.toSubgroup) g
  have residueKernelTrivial : residueObserver.ker = ⊥ :=
    (MonoidHom.ker_eq_bot_iff residueObserver).mpr residueFaithful
  exact ⟨G, groupG, finiteG, ⟨identified⟩, allPrimePowerBlind,
    residualTop, jointObserverTrivial,
    ⟨V, addV, moduleV, residueObserver, residueFaithful, residueKernelTrivial⟩,
    localContrast⟩

#print axioms alternating_five_observer_blind_kernel_irreplaceability

end D5.S3.Factorization.ObserverTypes.AlternatingFiveObserverBlindKernelIrreplaceability
