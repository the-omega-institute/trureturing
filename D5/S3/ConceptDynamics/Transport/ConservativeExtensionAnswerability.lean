/- GID: D5/S3/ConceptDynamics/Transport/ConservativeExtensionAnswerability
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Transport/ConservativeExtensionAnswerability
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Answerability of old questions is reflected and preserved by surjective pullback. -/

module
prelude
public import OmegaInit.Data.Function

namespace D5.S3.ConceptDynamics.Transport.ConservativeExtensionAnswerability

open Omega

/-- The target factors pointwise through the concept. -/
public def StrictRefines {X : Sort u} {Cval : Sort v} {Tval : Sort w}
    (target : X → Tval) (concept : X → Cval) : Prop :=
  Exists (fun factor : Cval → Tval => ∀ x, Eq (target x) (factor (concept x)))

/-- The singleton state and concept space in the Boolean example. -/
public inductive SingleState where
  | sole

/-- A one-state extension sees only the old Boolean state `false`. -/
public noncomputable def nonSurjectiveProjection : SingleState → Bool := fun _ => .false

/-- The old concept in the counterexample identifies both Boolean states. -/
public noncomputable def constantOldConcept : Bool → SingleState := fun _ => .sole

/-- Surjective pullback preserves and reflects factorization of the target. -/
public theorem answerability_transports_along_surjection
    {X : Sort u₁} {Y : Sort u₂} {Cval : Sort v₁} {Tval : Sort v₂}
    (p : Y → X) (surjective : Omega.Function.Surjective p) (C : X → Cval) (T : X → Tval) :
    Iff (StrictRefines T C) (StrictRefines (fun y => T (p y)) (fun y => C (p y))) :=
  Iff.intro
    (fun h => h.elim (fun factor agrees => Exists.intro factor (fun y => agrees (p y))))
    (fun h => h.elim (fun factor agrees => Exists.intro factor (fun x =>
      (surjective x).elim (fun y preimage =>
        Eq.subst (fun state => Eq (T state) (factor (C state))) preimage (agrees y)))))

/-- The one-state pullback hides the conflict between two states with the same
concept value and distinct Boolean targets. -/
public theorem nonsurjective_pullback_can_hide_unanswerability :
    And (Not (Omega.Function.Surjective nonSurjectiveProjection))
      (And (StrictRefines nonSurjectiveProjection
          (fun state => constantOldConcept (nonSurjectiveProjection state)))
        (Not (StrictRefines (fun x : Bool => x) constantOldConcept))) :=
  have falseNeTrue : Not (Eq Bool.false Bool.true) :=
    fun h => Eq.subst (Bool.rec (motive := fun _ => Prop) True False) h True.intro
  And.intro
    (fun surjective => (surjective Bool.true).elim (fun _ atTrue => falseNeTrue atTrue))
    (And.intro (Exists.intro (fun _ => Bool.false) (fun _ => Eq.refl))
      (fun h => h.elim (fun _ agrees =>
        falseNeTrue ((agrees Bool.false).trans (agrees Bool.true).symm))))

example : Iff (StrictRefines (fun x : Bool => x) (fun x => x))
    (StrictRefines (fun x : Bool => x) (fun x => x)) :=
  answerability_transports_along_surjection (fun x : Bool => x)
    (fun x => Exists.intro x Eq.refl) (fun x => x) (fun x => x)

end D5.S3.ConceptDynamics.Transport.ConservativeExtensionAnswerability
