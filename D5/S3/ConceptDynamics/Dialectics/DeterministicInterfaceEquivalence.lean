/- GID: D5/S3/ConceptDynamics/Dialectics/DeterministicInterfaceEquivalence
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Dialectics/DeterministicInterfaceEquivalence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Six interface descent criteria are equivalent without a finiteness assumption. -/

import D5.S0.Rewriting.Quotients.DynamicsDescent
import D5.S3.ConceptDynamics.Dialectics.ExactDescentNoCarry
import Mathlib.Data.Set.Operations
import Mathlib.Tactic.TFAE

/- Library-search audit trail (2026-08-22):
   * `rg -n -F 'deterministic_interface_sixfold_equivalence' D5
     Golden/Frozen/accepted` returned no matches.
   * Public repository hits were `dynamics_descends_iff`, which is reused after
     restricting the readout codomain to its range, and `exact_descent_has_no_carry`,
     which supplies the factorization-to-no-carry implication.
   * `factor_iff_observable_invariance` quantifies every value type and uses a
     generator presentation, rather than the fixed `Prop`-valued set below; it is
     adjacent but not an exact statement match.
   * The private-declaration search found no relevant descent, carry, factor, or
     depth-zero/depth-one equivalence; its hits concern unrelated algorithms.
   * Both existing modules in this directory were read: one defines carry and
     minimal repair, while the other proves only exact descent implies no carry.
   * Pinned Mathlib exactly supplies `Function.FactorsThrough`, `Function.extend`,
     `List.TFAE`, `tfae_have`, and `tfae_finish`, but no sixfold equivalence.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Dialectics.DeterministicInterfaceEquivalence

open D5.S0.Rewriting.Quotients.DynamicsDescent
open D5.S3.ConceptDynamics.Dialectics.MinimalDialecticalRepair
open D5.S3.ConceptDynamics.Dialectics.ExactDescentNoCarry

/-- The canonical surjection from states onto the realized interface image. -/
def realizedReadout {X B : Type*} (q : X → B) : X → Set.range q :=
  fun x ↦ ⟨q x, ⟨x, rfl⟩⟩

/-- Effective descent is unique only on the realized image of the interface. -/
def EffectiveDescent {X B : Type*} (q : X → B) (F : X → X) : Prop :=
  ∃! descended : Set.range q → Set.range q,
    realizedReadout q ∘ F = descended ∘ realizedReadout q

/-- The interface kernel is a congruence when the update preserves every fiber. -/
def InterfaceCongruence {X B : Type*} (q : X → B) (F : X → X) : Prop :=
  ∀ x y, q x = q y → q (F x) = q (F y)

/-- The pullback algebra consists of proposition-valued observables constant on fibers. -/
def PullbackAlgebra {X B : Type*} (q : X → B) : Set (X → Prop) :=
  {observable | Function.FactorsThrough observable q}

/-- Pullback by the update preserves every fiber-measurable proposition. -/
def PullbackInvariant {X B : Type*} (q : X → B) (F : X → X) : Prop :=
  ∀ observable ∈ PullbackAlgebra q, observable ∘ F ∈ PullbackAlgebra q

/-- The depth-zero kernel records equality of current interface readouts. -/
def depthZeroKernel {X B : Type*} (q : X → B) : X → X → Prop :=
  fun x y ↦ q x = q y

/-- The depth-one kernel additionally records equality after one update. -/
def depthOneKernel {X B : Type*} (q : X → B) (F : X → X) : X → X → Prop :=
  fun x y ↦ q x = q y ∧ q (F x) = q (F y)

/-- Effective image descent, kernel congruence, absence of carry, factorization,
pullback-algebra invariance, and equality of the first two kernels are equivalent.
No finiteness hypothesis is needed for any implication. -/
theorem deterministic_interface_sixfold_equivalence {X B : Type*}
    (q : X → B) (F : X → X) :
    List.TFAE [
      EffectiveDescent q F,
      InterfaceCongruence q F,
      ∀ x y, ¬IsCarryWitness q F q x y,
      Function.FactorsThrough (q ∘ F) q,
      PullbackInvariant q F,
      depthZeroKernel q = depthOneKernel q F] := by
  tfae_have 1 ↔ 2 := by
    have hSurjective : Function.Surjective (realizedReadout q) := by
      intro value
      obtain ⟨x, hx⟩ := value.property
      exact ⟨x, Subtype.ext hx⟩
    have hDescent := dynamics_descends_iff (realizedReadout q) F hSurjective
    constructor
    · intro hEffective
      have hPreserves := hDescent.mp hEffective
      intro x y hxy
      have hInput : realizedReadout q x = realizedReadout q y := Subtype.ext hxy
      exact congrArg Subtype.val (hPreserves x y hInput)
    · intro hCongruence
      apply hDescent.mpr
      intro x y hxy
      apply Subtype.ext
      exact hCongruence x y (congrArg Subtype.val hxy)
  tfae_have 2 → 4 := by
    intro hCongruence x y hxy
    exact hCongruence x y hxy
  tfae_have 4 → 3 := by
    intro hFactors x y witness
    let descended : B → B := Function.extend q (q ∘ F) id
    have hDescent : q ∘ F = descended ∘ q :=
      (hFactors.extend_comp id).symm
    apply exact_descent_has_no_carry q q F descended hDescent
    simpa only [IsCarryWitness, Function.comp_apply, id_eq] using witness
  tfae_have 3 → 2 := by
    intro hNoCarry x y hxy
    by_contra hne
    exact hNoCarry x y ⟨hxy, hne⟩
  tfae_have 2 → 5 := by
    intro hCongruence observable hObservable
    change Function.FactorsThrough (observable ∘ F) q
    intro x y hxy
    exact hObservable (hCongruence x y hxy)
  tfae_have 5 → 2 := by
    intro hInvariant x y hxy
    let observable : X → Prop := fun z ↦ q z = q (F x)
    have hObservable : observable ∈ PullbackAlgebra q := by
      change Function.FactorsThrough observable q
      intro z w hzw
      change (q z = q (F x)) = (q w = q (F x))
      exact propext (by rw [hzw])
    have hPulled := hInvariant observable hObservable
    change Function.FactorsThrough (observable ∘ F) q at hPulled
    have hProp := hPulled hxy
    change (q (F x) = q (F x)) = (q (F y) = q (F x)) at hProp
    exact (Eq.mp hProp rfl).symm
  tfae_have 2 → 6 := by
    intro hCongruence
    funext x y
    apply propext
    constructor
    · intro hxy
      exact ⟨hxy, hCongruence x y hxy⟩
    · exact fun hxy ↦ hxy.1
  tfae_have 6 → 2 := by
    intro hKernels x y hxy
    have hAtPair : depthZeroKernel q x y = depthOneKernel q F x y :=
      congrFun (congrFun hKernels x) y
    exact (Eq.mp hAtPair hxy).2
  tfae_finish

example : EffectiveDescent (id : Bool → Bool) Bool.not := by
  apply ((deterministic_interface_sixfold_equivalence id Bool.not).out 1 0).mp
  intro x y hxy
  exact congrArg Bool.not hxy

#print axioms deterministic_interface_sixfold_equivalence

end D5.S3.ConceptDynamics.Dialectics.DeterministicInterfaceEquivalence
