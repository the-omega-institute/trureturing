/- GID: D5/S3/ObserverMemory/Refinement/JointReadoutSupremum
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/Refinement/JointReadoutSupremum
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A paired readout has the intersection kernel and is the least common
     refinement of its two coordinates. -/

import D5.S3.ObserverMemory.Refinement.FactorizationCategory
import Mathlib.Data.Setoid.Basic

/- Library-search audit trail (2026-08-29):
   * Pinned Mathlib supplies products and the infimum of setoids.
   * The repository `Refines` structure supplies the canonical factorization
     order and is reused without introducing a parallel interface preorder.
   * Repository search found specialized joint-faithfulness results, but no
     exact binary supremum package for arbitrary readout codomains.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ObserverMemory.Refinement.JointReadoutSupremum

open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ObserverMemory.Refinement.FactorizationCategory

universe u v w z

/-- The joint readout that records both coordinates. -/
def pairReadout
    {X : Type u} {Y : Type v} {Z : Type w}
    (first : Concept X Y) (second : Concept X Z) : Concept X (Y × Z) :=
  fun x => (first x, second x)

/-- Equality under the joint readout is exactly equality under both component
readouts. -/
theorem pair_readout_kernel
    {X : Type u} {Y : Type v} {Z : Type w}
    (first : Concept X Y) (second : Concept X Z) :
    Setoid.ker (pairReadout first second) =
      Setoid.ker first ⊓ Setoid.ker second := by
  apply Setoid.ext
  intro x y
  constructor
  · intro samePair
    exact ⟨congrArg Prod.fst samePair, congrArg Prod.snd samePair⟩
  · rintro ⟨sameFirst, sameSecond⟩
    exact Prod.ext sameFirst sameSecond

/-- The pair readout refines its first coordinate by projection. -/
def pair_readout_refines_first
    {X : Type u} {Y : Type v} {Z : Type w}
    (first : Concept X Y) (second : Concept X Z) :
    Refines (pairReadout first second) first :=
  ⟨Prod.fst, fun _ => rfl⟩

/-- The pair readout refines its second coordinate by projection. -/
def pair_readout_refines_second
    {X : Type u} {Y : Type v} {Z : Type w}
    (first : Concept X Y) (second : Concept X Z) :
    Refines (pairReadout first second) second :=
  ⟨Prod.snd, fun _ => rfl⟩

/-- Any readout that refines both coordinates also refines their pair. Hence
pairing is the supremum in the factorization preorder. -/
def pair_readout_least_common_refinement
    {X : Type u} {Y : Type v} {Z : Type w} {W : Type z}
    (first : Concept X Y) (second : Concept X Z) (jointSource : Concept X W)
    (refinesFirst : Refines jointSource first)
    (refinesSecond : Refines jointSource second) :
    Refines jointSource (pairReadout first second) :=
  ⟨fun value =>
      (refinesFirst.factor value, refinesSecond.factor value),
    fun x => Prod.ext (refinesFirst.commutes x) (refinesSecond.commutes x)⟩

/-- A Boolean identity paired with a constant coordinate still has the identity
kernel. -/
example :
    Setoid.ker (pairReadout (fun x : Bool => x)
      (fun _ : Bool => PUnit.unit)) = Setoid.ker (fun x : Bool => x) := by
  apply le_antisymm
  · intro x y samePair
    exact congrArg Prod.fst samePair
  · intro x y sameValue
    exact Prod.ext sameValue rfl

#print axioms pair_readout_kernel
#print axioms pair_readout_least_common_refinement

end D5.S3.ObserverMemory.Refinement.JointReadoutSupremum
