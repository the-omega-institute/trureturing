/- GID: D5/S3/ConceptDynamics/Secrecy/SubthresholdCoalitionLearnsNothing
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Secrecy/SubthresholdCoalitionLearnsNothing
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Structural zero leakage makes every coalition-determined secret function constant. -/

import D5.S3.ConceptDynamics.Disclosure.ExactTargetForcedLeak
import D5.S3.ConceptDynamics.Sufficiency.UniversalSufficiencyFactorization

/- Library-search audit trail (2026-08-22):
   * `rg -n -F 'subthreshold_coalition_learns_nothing' D5 Golden/Frozen/accepted`
     found no repository declaration or accepted duplicate.
   * The required `secret|coalition|threshold|leak|zero.*leak` scan found
     `KnowledgePolicyThreshold`, whose injective-policy theorem equates full-secret and
     policy thresholds rather than proving zero-leak constancy. The `DecisionValue`
     threshold hits are contribution/public-good games and are unrelated.
   * Exact reusable hits are `IsConceptMeet`, `ConceptEquivalent`, `Refines`,
     `refinement_transitive`, `canonicalTargetReadout`, and
     `universal_sufficiency_factorization`; they are imported and applied below.
   * Searches for constant refinement and `FactorsThrough` a constant readout found no
     stronger repository or pinned-Mathlib theorem. The final step uses only the
     factorization equality and equality of the unique constant coordinate. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Secrecy.SubthresholdCoalitionLearnsNothing

open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.ConceptJoinUniversal
open D5.S3.ConceptDynamics.Disclosure.ExactTargetForcedLeak
open D5.S3.ConceptDynamics.Interventions.RedundantAppealDefectPersistence
open D5.S3.ConceptDynamics.Refinement.RefinementTransitivity
open D5.S3.ConceptDynamics.Sufficiency.UniversalSufficiencyFactorization

universe u v

/-- The bottom concept has one readout value and therefore distinguishes no states. -/
def constantConcept (X : Type u) : Concept X Unit :=
  fun _ => ()

/-- Under structural zero leakage, any coalition-determined function of the secret is
constant on all states. -/
theorem subthreshold_coalition_learns_nothing
    {X : Type u} {C S M Y : Type v} [Nonempty X]
    (coalition : Concept X C) (secret : Concept X S) (common : Concept X M)
    (target : X -> Y) (secretFunction : S -> Y)
    (commonIsMeet : IsConceptMeet coalition secret common)
    (zeroLeak : ConceptEquivalent common (constantConcept X))
    (targetFromSecret : target = secretFunction ∘ secret)
    (coalitionDeterminesTarget : Refines (canonicalTargetReadout target) coalition) :
    ∀ x y, target x = target y := by
  have targetConstantOnSecretFibers :
      ∀ ⦃x y : X⦄, secret x = secret y -> target x = target y := by
    intro x y hxy
    rw [targetFromSecret]
    exact congrArg secretFunction hxy
  have targetFactorThroughSecret :
      ∃ factor : S -> TargetImage target,
        canonicalTargetReadout target = factor ∘ secret :=
    (universal_sufficiency_factorization secret target).2.mpr
      targetConstantOnSecretFibers
  have targetRefinesSecret : Refines (canonicalTargetReadout target) secret :=
    (universal_sufficiency_factorization secret target).1.mpr
      targetFactorThroughSecret
  have targetRefinesCommon : Refines (canonicalTargetReadout target) common :=
    commonIsMeet.greatest (canonicalTargetReadout target)
      coalitionDeterminesTarget targetRefinesSecret
  have targetRefinesBottom :
      Refines (canonicalTargetReadout target) (constantConcept X) :=
    refinement_transitive (canonicalTargetReadout target) common (constantConcept X)
      zeroLeak.1 targetRefinesCommon
  rcases targetRefinesBottom with ⟨factor, hfactor⟩
  intro x y
  have hreadout :
      canonicalTargetReadout target x = canonicalTargetReadout target y := by
    rw [hfactor]
    rfl
  exact congrArg (fun value : TargetImage target => value.1) hreadout

/-- A two-bit secret shows that failure to recover the whole secret does not imply that
the coalition learned no nonconstant secret function. -/
theorem ignorance_does_not_imply_zero_information :
    let secret : Concept (Bool × Bool) (Bool × Bool) := id
    let coalition : Concept (Bool × Bool) Bool := Prod.fst
    ¬Refines (canonicalTargetReadout secret) coalition ∧
      ∃ (target : Bool × Bool -> Bool) (secretFunction : Bool × Bool -> Bool),
        target = secretFunction ∘ secret ∧
          Refines (canonicalTargetReadout target) coalition ∧
          ∃ x y, target x ≠ target y := by
  dsimp
  constructor
  · rintro ⟨factor, hfactor⟩
    have hreadout :
        canonicalTargetReadout (id : Bool × Bool -> Bool × Bool) (false, false) =
          canonicalTargetReadout (id : Bool × Bool -> Bool × Bool) (false, true) := by
      rw [hfactor]
      rfl
    have hpairs := congrArg
      (fun value : TargetImage (id : Bool × Bool -> Bool × Bool) => value.1) hreadout
    exact Bool.false_ne_true (congrArg Prod.snd hpairs)
  · refine ⟨Prod.fst, Prod.fst, rfl, ?_, ?_⟩
    · refine ⟨fun b => ⟨b, (b, false), rfl⟩, ?_⟩
      funext p
      apply Subtype.ext
      rfl
    · exact ⟨(false, false), (true, false), Bool.false_ne_true⟩

example : ∀ x y : Bool, (fun _ : Bool => false) x = (fun _ : Bool => false) y := by
  apply subthreshold_coalition_learns_nothing
    (constantConcept Bool) (id : Concept Bool Bool) (constantConcept Bool)
    (fun _ => false) (fun _ => false)
  · refine ⟨⟨id, rfl⟩, ⟨fun _ => (), rfl⟩, ?_⟩
    intro L lower lowerRefinesCoalition _
    exact lowerRefinesCoalition
  · exact ⟨⟨id, rfl⟩, ⟨id, rfl⟩⟩
  · rfl
  · refine ⟨fun _ => ⟨false, false, rfl⟩, ?_⟩
    funext x
    apply Subtype.ext
    rfl

#print axioms subthreshold_coalition_learns_nothing

end D5.S3.ConceptDynamics.Secrecy.SubthresholdCoalitionLearnsNothing
