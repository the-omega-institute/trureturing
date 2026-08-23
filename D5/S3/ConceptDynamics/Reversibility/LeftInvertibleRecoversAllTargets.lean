/- GID: D5/S3/ConceptDynamics/Reversibility/LeftInvertibleRecoversAllTargets
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Reversibility/LeftInvertibleRecoversAllTargets
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A left inverse recovers every target, while identity erasure can retain value. -/

import D5.S3.ConceptDynamics.Sufficiency.UniversalSufficiencyFactorization

/- Library-search audit trail (2026-08-22):
   * `rg -n -F 'left_invertible_recovers_all_targets' D5 Golden/Frozen/accepted`
     returned no hit, so there is no repository or accepted duplicate.
   * `rg -n 'left.*invers|reversib|recover' D5/S3/ConceptDynamics/ --glob '*.lean'`
     found related recovery modules, but no result covering left invertibility and the
     required finite counterexample.
   * The repository theorem
     `Sufficiency.UniversalSufficiencyFactorization.universal_sufficiency_factorization`
     characterizes target recovery as factorization and is applied below instead of
     reproving that characterization.
   * The pinned Mathlib search for `LeftInverse` and `injective` found
     `Function.LeftInverse.injective`; it is used to refute a left inverse for the
     identity-erasing finite process. The direct recovery equation uses only function
     extensionality, composition, and the supplied left-inverse equation. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v w

namespace D5.S3.ConceptDynamics.Reversibility.LeftInvertibleRecoversAllTargets

open D5.S3.ConceptDynamics.ConceptJoinUniversal
open D5.S3.ConceptDynamics.Sufficiency.UniversalSufficiencyFactorization

/-- A finite process that retains a Boolean value and deletes the Boolean identity. -/
def eraseIdentity : Bool × Bool → Bool := fun state ↦ state.1

/-- A nonconstant numerical target depending only on the retained value coordinate. -/
def retainedValue : Bool × Bool → Nat := fun state ↦ if state.1 then 1 else 0

/-- Erasing identity is not left-invertible, although it preserves a nonconstant target. -/
theorem identity_erasure_preserves_nontrivial_value :
    (¬∃ R : Bool → Bool × Bool, Function.LeftInverse R eraseIdentity) ∧
      ∃ recover : Bool → Nat,
        retainedValue = recover ∘ eraseIdentity ∧
          retainedValue (false, false) ≠ retainedValue (true, false) := by
  constructor
  · rintro ⟨R, hleft⟩
    have hpair : (false, false) = (false, true) := hleft.injective rfl
    simp at hpair
  · refine ⟨fun value ↦ if value then 1 else 0, ?_, ?_⟩
    · rfl
    · decide

/-- A left inverse gives the stated recovery formula for every target and, via the
universal sufficiency theorem, the corresponding canonical-target refinement. The finite
identity-erasure witness records that a non-left-invertible process may still preserve a
particular nonconstant target. -/
theorem left_invertible_recovers_all_targets
    {X : Type u} {B : Type v} (U : X → B) (R : B → X)
    (hleft : Function.LeftInverse R U) :
    (∀ {Y : Type w} (T : X → Y),
      T = (T ∘ R) ∘ U ∧ Refines (canonicalTargetReadout T) U) ∧
      (¬∃ R' : Bool → Bool × Bool, Function.LeftInverse R' eraseIdentity) ∧
      ∃ recover : Bool → Nat,
        retainedValue = recover ∘ eraseIdentity ∧
          retainedValue (false, false) ≠ retainedValue (true, false) := by
  constructor
  · intro Y T
    constructor
    · funext x
      change T x = T (R (U x))
      exact congrArg T (hleft x).symm
    · by_cases hnonempty : Nonempty X
      · letI : Nonempty X := hnonempty
        have hfiber : ∀ ⦃x y : X⦄, U x = U y → T x = T y := by
          intro x y hxy
          calc
            T x = T (R (U x)) := congrArg T (hleft x).symm
            _ = T (R (U y)) := congrArg (T ∘ R) hxy
            _ = T y := congrArg T (hleft y)
        have hfactor := (universal_sufficiency_factorization U T).2.mpr hfiber
        exact (universal_sufficiency_factorization U T).1.mpr hfactor
      · refine ⟨fun b ↦ (hnonempty ⟨R b⟩).elim, ?_⟩
        funext x
        exact (hnonempty ⟨x⟩).elim
  · exact identity_erasure_preserves_nontrivial_value

example : retainedValue (true, false) = 1 := rfl

#print axioms left_invertible_recovers_all_targets

end D5.S3.ConceptDynamics.Reversibility.LeftInvertibleRecoversAllTargets
