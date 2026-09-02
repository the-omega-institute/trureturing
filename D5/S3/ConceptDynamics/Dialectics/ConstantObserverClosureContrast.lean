/- GID: D5/S3/ConceptDynamics/Dialectics/ConstantObserverClosureContrast
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Dialectics/ConstantObserverClosureContrast
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A constant observer closes every dynamics while losing state and nonconstant targets. -/

/- Library-search audit trail (2026-09-03):
   * The frozen `deterministic_interface_sixfold_equivalence` is the exact owner
     of effective descent, interface congruence, and absence of carry; it is
     applied directly to the constant interface.
   * Repository body-shape searches for constant `InterfaceCongruence`,
     `IsCarryWitness`, injectivity, and target factorization found adjacent
     examples but no theorem combining all four public clauses.
   * Pinned Mathlib supplies `Function.FactorsThrough` and the nontrivial-carrier
     witness used below, but no constant-observer whole statement. Public Lean
     ecosystem searches found no exact result.
-/

import D5.S3.ConceptDynamics.Dialectics.DeterministicInterfaceEquivalence

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Dialectics.ConstantObserverClosureContrast

open D5.S3.ConceptDynamics.Dialectics.MinimalDialecticalRepair
open D5.S3.ConceptDynamics.Dialectics.DeterministicInterfaceEquivalence

/-- On every nontrivial state carrier, the constant observer has exact dynamic
closure and no carry for arbitrary dynamics, but it neither separates states
nor suffices for any target that distinguishes at least one state pair. -/
theorem constant_observer_closure_can_be_coarse
    {X : Type*} [Nontrivial X] (dynamics : X → X) :
    EffectiveDescent (fun _ : X => ()) dynamics ∧
      (∀ left right : X,
        ¬IsCarryWitness (fun _ : X => ()) dynamics (fun _ : X => ()) left right) ∧
      ¬Function.Injective (fun _ : X => ()) ∧
      (∀ {Target : Type*} (target : X → Target),
        (∃ left right, target left ≠ target right) →
          ¬Function.FactorsThrough target (fun _ : X => ())) := by
  have congruence : InterfaceCongruence (fun _ : X => ()) dynamics := by
    intro left right sameReadout
    rfl
  have closure : EffectiveDescent (fun _ : X => ()) dynamics :=
    ((deterministic_interface_sixfold_equivalence
      (fun _ : X => ()) dynamics).out 1 0).mp congruence
  have noCarry : ∀ left right : X,
      ¬IsCarryWitness (fun _ : X => ()) dynamics (fun _ : X => ()) left right :=
    ((deterministic_interface_sixfold_equivalence
      (fun _ : X => ()) dynamics).out 1 2).mp congruence
  have notFaithful : ¬Function.Injective (fun _ : X => ()) := by
    obtain ⟨left, right, different⟩ := exists_pair_ne X
    intro injective
    exact different (injective rfl)
  refine ⟨closure, noCarry, notFaithful, ?_⟩
  intro Target target separated sufficient
  obtain ⟨left, right, differentTarget⟩ := separated
  exact differentTarget (sufficient rfl)

#print axioms constant_observer_closure_can_be_coarse

end D5.S3.ConceptDynamics.Dialectics.ConstantObserverClosureContrast

