/- GID: D5/S3/ConceptDynamics/Sufficiency/GlobalProfileQuotientUniversality
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Sufficiency/GlobalProfileQuotientUniversality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A dependent family of local readouts has a simultaneous-kernel quotient that recovers every component and, under the necessary nonempty-state hypothesis, factors through every interface recovering all components; Refines coarse fine means that coarse factors through fine, recovery on every finite subfamily suffices by singleton tests, and an empty index type gives the total relation and a singleton quotient when the state type is nonempty. -/

import D5.S3.ConceptDynamics.Sufficiency.MinimalPredictiveCompletionQuotient
import Mathlib.Data.Fintype.Basic
import Mathlib.Logic.Function.Basic

/- Library-search audit trail (2026-08-25):
   * `rg -n -F 'global_profile_quotient_universality' D5 Golden/Frozen/accepted`
     returned no hit.
   * All five existing `ConceptDynamics/Sufficiency` digests were read. The closest,
     `minimal_predictive_completion_quotient`, concerns one readout plus dynamics,
     not a family of readouts without dynamics.
   * Repository searches for profile and quotient factorization found the public
     `control_quotient_universal_minimality`, which requires a monoid action, and
     `conditional_probability_profile_is_minimal`, which concerns one PMF-valued
     readout on realized images; neither covers this dependent family theorem.
   * The only private profile hits were unrelated separation lemmas in
     `RootPulseRefinementDepth`; no private family-quotient factorization was found.
   * Pinned Mathlib supplies `Setoid.ker`, `Quotient.lift`, `Function.extend`,
     `Function.FactorsThrough.extend_apply`, and the `Fintype Unit` instance; these
     are reused below, while the family assembly and empty-state obstruction are local.
   -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Sufficiency.GlobalProfileQuotientUniversality

open D5.S3.ConceptDynamics.ConceptJoinUniversal
open D5.S3.ConceptDynamics.Sufficiency.MinimalPredictiveCompletionQuotient

universe u

/-- The global profile records every local readout, allowing its output type to depend
on the index. -/
def globalProfile {P X : Type u} {O : P -> Type u} (q : (p : P) -> X -> O p) :
    X -> ((p : P) -> O p) :=
  fun x p => q p x

/-- Two states are globally profile-equivalent when every local readout agrees. -/
def globalProfileRelation {P X : Type u} {O : P -> Type u}
    (q : (p : P) -> X -> O p) : Set (X × X) :=
  readoutRelation (globalProfile q)

/-- Membership in the global profile relation is agreement at every index. -/
theorem global_profile_relation_iff {P X : Type u} {O : P -> Type u}
    (q : (p : P) -> X -> O p) (x y : X) :
    (x, y) ∈ globalProfileRelation q ↔ forall p, q p x = q p y := by
  change globalProfile q x = globalProfile q y ↔ _
  constructor
  · intro sameProfile p
    exact congrFun sameProfile p
  · intro sameLocals
    funext p
    exact sameLocals p

/-- The simultaneous kernel setoid of the local readout family. -/
def globalProfileSetoid {P X : Type u} {O : P -> Type u}
    (q : (p : P) -> X -> O p) : Setoid X :=
  Setoid.ker (globalProfile q)

/-- States modulo simultaneous agreement of every local readout. -/
abbrev GlobalProfileQuotient {P X : Type u} {O : P -> Type u}
    (q : (p : P) -> X -> O p) :=
  Quotient (globalProfileSetoid q)

/-- The canonical projection to the global profile quotient. -/
def globalProfileProjection {P X : Type u} {O : P -> Type u}
    (q : (p : P) -> X -> O p) : X -> GlobalProfileQuotient q :=
  Quotient.mk _

/-- Recover the local readout at one index from the global quotient. -/
def localProfileReadout {P X : Type u} {O : P -> Type u}
    (q : (p : P) -> X -> O p) (p : P) : GlobalProfileQuotient q -> O p :=
  Quotient.lift (q p) (by
    intro x y hxy
    exact congrFun hxy p)

/-- The canonical projection recovers every local readout, without any nonemptiness
assumption on states or indices. -/
theorem local_readouts_factor_through_global_profile
    {P X : Type u} {O : P -> Type u} (q : (p : P) -> X -> O p) :
    forall p, Refines (q p) (globalProfileProjection q) := by
  intro p
  refine ⟨localProfileReadout q p, ?_⟩
  funext x
  rfl

/-- An interface recovers every finite local subfamily when every finite indexed
selection has a simultaneous dependent family of decoders. -/
def RecoversFiniteSubfamilies {P X R : Type u} {O : P -> Type u}
    (q : (p : P) -> X -> O p) (r : X -> R) : Prop :=
  forall (S : Type) [Fintype S] (index : S -> P),
    exists recover : (s : S) -> R -> O (index s),
      forall s, q (index s) = recover s ∘ r

/-- The global profile quotient recovers every local readout and is coarsest among
interfaces doing so. Recovery on all finite subfamilies gives the same conclusion. -/
theorem global_profile_quotient_universality
    {P X : Type u} {O : P -> Type u} [Nonempty X]
    (q : (p : P) -> X -> O p) :
    (forall p, Refines (q p) (globalProfileProjection q)) ∧
      (forall {R : Type u} (r : X -> R),
        (forall p, Refines (q p) r) -> Refines (globalProfileProjection q) r) ∧
      (forall {R : Type u} (r : X -> R),
        RecoversFiniteSubfamilies q r -> Refines (globalProfileProjection q) r) := by
  have localRecovery := local_readouts_factor_through_global_profile q
  have universal : forall {R : Type u} (r : X -> R),
      (forall p, Refines (q p) r) -> Refines (globalProfileProjection q) r := by
    intro R r recovers
    have fiberConstant : (globalProfileProjection q).FactorsThrough r := by
      intro x y sameInterface
      apply Quotient.sound
      change globalProfile q x = globalProfile q y
      funext p
      obtain ⟨factor, factors⟩ := recovers p
      calc
        q p x = factor (r x) := congrFun factors x
        _ = factor (r y) := congrArg factor sameInterface
        _ = q p y := (congrFun factors y).symm
    let factor : R -> GlobalProfileQuotient q :=
      Function.extend r (globalProfileProjection q)
        (Function.const R (globalProfileProjection q (Classical.arbitrary X)))
    refine ⟨factor, ?_⟩
    funext x
    change globalProfileProjection q x = factor (r x)
    exact (fiberConstant.extend_apply _ x).symm
  refine ⟨localRecovery, universal, ?_⟩
  intro R r recoversFinite
  apply universal r
  intro p
  obtain ⟨recover, factors⟩ := recoversFinite Unit (fun _ => p)
  exact ⟨recover (), factors ()⟩

/-- Empty states show why total factorization through an arbitrary interface needs a
nonempty-state hypothesis, even when the local family itself is empty. -/
theorem empty_state_obstruction :
    let q : (p : Empty) -> Empty -> Unit := fun p => p.elim
    let r : Empty -> Unit := fun x => x.elim
    (forall p, Refines (q p) r) ∧
      ¬Refines (globalProfileProjection q) r := by
  dsimp
  constructor
  · intro p
    exact p.elim
  · rintro ⟨factor, _factors⟩
    exact Quotient.inductionOn (factor ()) (fun x => x.elim)

example :
    let q : (p : Unit) -> Bool -> Bool := fun _ b => b
    Refines (globalProfileProjection q) (fun b : Bool => b) := by
  dsimp
  apply (global_profile_quotient_universality
    (q := fun (_ : Unit) (b : Bool) => b)).2.1 (fun b : Bool => b)
  intro _p
  exact ⟨id, rfl⟩

example :
    let q : (p : Empty) -> Bool -> Unit := fun p => p.elim
    Refines (globalProfileProjection q) (fun _ : Bool => ()) := by
  dsimp
  apply (global_profile_quotient_universality
    (q := fun (p : Empty) (_ : Bool) => (p.elim : Unit))).2.1
    (fun _ : Bool => ())
  intro p
  exact p.elim

#print axioms global_profile_quotient_universality

end D5.S3.ConceptDynamics.Sufficiency.GlobalProfileQuotientUniversality
