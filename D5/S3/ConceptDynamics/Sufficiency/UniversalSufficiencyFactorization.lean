/- GID: D5/S3/ConceptDynamics/Sufficiency/UniversalSufficiencyFactorization
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Sufficiency/UniversalSufficiencyFactorization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Universal sufficiency is target factorization, equivalently constancy on fibers. -/

import Mathlib.Data.Set.Basic
import Mathlib.Logic.Function.Basic
import D5.S3.ConceptDynamics.ConceptJoinUniversal

/- Library-search audit trail (2026-08-22):
   * `rg -n -F 'universal_sufficiency_factorization' D5 Golden/Frozen/accepted`
     returned no hit, so there is no repository or accepted duplicate.
   * Searches for `universal_sufficiency`, `factorization`, `factors_through`, and
     `fiber.*constant` found the adjacent repository theorem
     `AnswerabilityCriterion.answerability_criterion`, but no theorem combining
     canonical target-image refinement with the requested factorization criterion.
   * The pinned Mathlib exact hits are `Function.FactorsThrough`, `Function.extend`,
     `Function.FactorsThrough.extend_apply`, and `Function.factorsThrough_iff` in
     `Mathlib.Logic.Function.Basic`; all four are reused below.
   * `Concept` and `Refines` are reused from `ConceptFiberDecomposition` and
     `ConceptJoinUniversal`; the local proof only adds the target-image model and its
     explicit choice-based extension to coordinates outside the range of the concept. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Sufficiency.UniversalSufficiencyFactorization

open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.ConceptJoinUniversal

/-- The image coordinate type of a target, modeling the `Im T` in the canonical target concept. -/
def TargetImage {X Y : Type _} (T : X → Y) := Set.range T

/-- The canonical target concept sends each state to its target value together with image
membership. -/
def canonicalTargetReadout {X Y : Type _} (T : X → Y) : Concept X (TargetImage T) :=
  fun x ↦ ⟨T x, x, rfl⟩

/-- Extend a fiber-constant target to every concept coordinate. The state type is assumed
nonempty so that `Im T` supplies a value for coordinates outside the range of the concept. -/
noncomputable def targetFactor
    {X B Y : Type _} [Nonempty X] (q_C : Concept X B) (T : X → Y)
    (_h : ∀ ⦃x y : X⦄, q_C x = q_C y → T x = T y) : B → TargetImage T :=
  Function.extend q_C (canonicalTargetReadout T)
    (Function.const B (canonicalTargetReadout T (Classical.arbitrary X)))

/-- The choice-based extension agrees with the canonical target on every represented
concept coordinate. -/
theorem targetFactor_apply
    {X B Y : Type _} [Nonempty X] (q_C : Concept X B) (T : X → Y)
    (h : ∀ ⦃x y : X⦄, q_C x = q_C y → T x = T y) (x : X) :
    targetFactor q_C T h (q_C x) = canonicalTargetReadout T x := by
  apply Function.FactorsThrough.extend_apply
  intro a b hab
  exact Subtype.ext (h hab)

/-- Universal sufficiency has three equivalent forms: refinement of the canonical target
concept, factorization through the concept readout, and constancy of the target on each
concept fiber. Nonempty states make the target image nonempty, providing the arbitrary
off-range value required when the concept readout is not surjective. -/
theorem universal_sufficiency_factorization
    {X B Y : Type _} [Nonempty X] (q_C : Concept X B) (T : X → Y) :
    (Refines (canonicalTargetReadout T) q_C ↔
      ∃ factor : B → TargetImage T,
        canonicalTargetReadout T = factor ∘ q_C) ∧
    ((∃ factor : B → TargetImage T,
        canonicalTargetReadout T = factor ∘ q_C) ↔
      ∀ ⦃x y : X⦄, q_C x = q_C y → T x = T y) := by
  letI : Nonempty (TargetImage T) :=
    ⟨canonicalTargetReadout T (Classical.arbitrary X)⟩
  constructor
  · rfl
  · constructor
    · intro hfactor
      have hthrough : (canonicalTargetReadout T).FactorsThrough q_C :=
        (Function.factorsThrough_iff (f := q_C) (canonicalTargetReadout T)).2 hfactor
      intro x y hxy
      exact congrArg Subtype.val (hthrough hxy)
    · intro hfiber
      refine ⟨targetFactor q_C T hfiber, ?_⟩
      funext x
      change canonicalTargetReadout T x = targetFactor q_C T hfiber (q_C x)
      exact (targetFactor_apply q_C T hfiber x).symm

example :
    Refines
      (canonicalTargetReadout (fun p : Bool × Bool ↦ p.1))
      (fun p : Bool × Bool ↦ p.1) := by
  refine ⟨fun b ↦ ⟨b, (b, false), rfl⟩, ?_⟩
  funext p
  apply Subtype.ext
  rfl

#print axioms universal_sufficiency_factorization

end D5.S3.ConceptDynamics.Sufficiency.UniversalSufficiencyFactorization
