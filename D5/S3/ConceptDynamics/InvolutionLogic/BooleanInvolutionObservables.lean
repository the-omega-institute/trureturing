/- GID: D5/S3/ConceptDynamics/InvolutionLogic/BooleanInvolutionObservables
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/InvolutionLogic/BooleanInvolutionObservables
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Boolean observables split into flip and invariant parity sectors under an involution. -/

import D5.S3.ConceptDynamics.InvolutionLogic.InvolutionTransversal
import Mathlib.Tactic

/- Library-search audit trail (2026-08-25):
   * Pinned Mathlib supplies propositional XOR and tautology checking.
   * Repository searches found no accepted parity package for observables acted on
     by an involution.
   * The set-transversal characterization is imported rather than redeclared. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.InvolutionLogic.BooleanInvolutionObservables

open D5.S3.ConceptDynamics.InvolutionLogic.InvolutionTransversal

/-- A proposition-valued observable flips under a transformation. -/
def PropFlip {X : Type*} (involution : X → X) (observable : X → Prop) : Prop :=
  ∀ x, observable (involution x) ↔ ¬ observable x

/-- A proposition-valued observable is invariant under a transformation. -/
def PropInvariant {X : Type*} (involution : X → X)
    (observable : X → Prop) : Prop :=
  ∀ x, observable (involution x) ↔ observable x

/-- Pointwise exclusive-or of two proposition-valued observables. -/
def xorObservable {X : Type*} (first second : X → Prop) : X → Prop :=
  fun x => Xor (first x) (second x)

/-- Flip observables are exactly orbit transversals of their truth sets. -/
theorem propFlip_iff_orbitTransversal
    {X : Type*} (involution : X → X) (observable : X → Prop) :
    PropFlip involution observable ↔
      OrbitTransversal involution {x | observable x} := by
  rfl

/-- A flipping observable witnesses fixed-point freeness. -/
theorem fixedPointFree_of_propFlip
    {X : Type*} {involution : X → X} {observable : X → Prop}
    (flip : PropFlip involution observable) :
    ∀ x, involution x ≠ x :=
  fixedPointFree_of_orbitTransversal
    ((propFlip_iff_orbitTransversal involution observable).1 flip)

/-- On an inhabited space, one observable cannot be both flip and invariant. -/
theorem not_flip_and_invariant
    {X : Type*} [Nonempty X] {involution : X → X} {observable : X → Prop} :
    ¬(PropFlip involution observable ∧
      PropInvariant involution observable) := by
  rintro ⟨flip, invariant⟩
  let x : X := Classical.choice (inferInstance : Nonempty X)
  have hFlip := flip x
  have hInvariant := invariant x
  tauto

/-- XOR of two flip observables is invariant. -/
theorem xor_invariant_of_flips
    {X : Type*} {involution : X → X} {first second : X → Prop}
    (firstFlip : PropFlip involution first)
    (secondFlip : PropFlip involution second) :
    PropInvariant involution (xorObservable first second) := by
  intro x
  have hFirst := firstFlip x
  have hSecond := secondFlip x
  unfold xorObservable
  rw [hFirst, hSecond]
  exact xor_not_not

/-- Equivalence of two flip observables is invariant. -/
theorem iff_invariant_of_flips
    {X : Type*} {involution : X → X} {first second : X → Prop}
    (firstFlip : PropFlip involution first)
    (secondFlip : PropFlip involution second) :
    ∀ x, (first (involution x) ↔ second (involution x)) ↔
      (first x ↔ second x) := by
  intro x
  have hFirst := firstFlip x
  have hSecond := secondFlip x
  tauto

/-- XOR of one flip observable and one invariant observable is again flip. -/
theorem xor_flip_of_flip_invariant
    {X : Type*} {involution : X → X} {first second : X → Prop}
    (firstFlip : PropFlip involution first)
    (secondInvariant : PropInvariant involution second) :
    PropFlip involution (xorObservable first second) := by
  intro x
  have hFirst := firstFlip x
  have hSecond := secondInvariant x
  unfold xorObservable
  rw [hFirst, hSecond, xor_not_left, not_xor]

#print axioms not_flip_and_invariant
#print axioms xor_invariant_of_flips
#print axioms xor_flip_of_flip_invariant

end D5.S3.ConceptDynamics.InvolutionLogic.BooleanInvolutionObservables
