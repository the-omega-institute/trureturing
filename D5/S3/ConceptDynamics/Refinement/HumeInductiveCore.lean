/- GID: D5/S3/ConceptDynamics/Refinement/HumeInductiveCore
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Refinement/HumeInductiveCore
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A constant finite past permits incompatible futures, while descent yields prediction. -/

import D5.S3.ConceptDynamics.Refinement.InductiveSufficiency

/- Library-search audit trail (2026-09-01):
   * Repository statement-shape searches for finite pasts, Hume, same-history
     witnesses, and inductive sufficiency found no theorem stating this concrete
     countermodel together with the general positive implication.
   * The exact repository hit `inductive_sufficiency_criterion` supplies both
     required directions and is imported and applied directly below.
   * Pinned Mathlib supplies the reused `Function.FactorsThrough` predicate and
     `Set.rangeFactorization`; no duplicate theorem packages both source clauses. -/

namespace D5.S3.ConceptDynamics.Refinement.HumeInductiveCore

open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.ConceptJoinUniversal
open D5.S3.ConceptDynamics.Refinement.InductiveSufficiency

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- The concrete finite-past readout forgets which Boolean state occurred. -/
def constantPast : Concept Bool Unit := fun _ => ()

/-- The concrete future law retains the Boolean distinction forgotten by the past. -/
def identityFuture : Concept Bool Bool := id

/-- Finite past data alone does not force a future law: the constant Boolean
history has equal pasts with different identity predictions and therefore does
not support prediction refinement. Conversely, any supplied descent premise
does yield prediction through the realized-history image. -/
theorem hume_inductive_core :
    ((exists x y : Bool,
        constantPast x = constantPast y /\
          Not (identityFuture x = identityFuture y)) /\
      Not (Refines identityFuture (Set.rangeFactorization constantPast))) /\
    forall {X History Prediction : Type*}
      (history : Concept X History) (predict : Concept X Prediction),
      Function.FactorsThrough predict history ->
        Refines predict (Set.rangeFactorization history) := by
  have samePast : constantPast false = constantPast true := rfl
  have differentFuture : Not (identityFuture false = identityFuture true) := by
    simp [identityFuture]
  have witness :
      exists x y : Bool,
        constantPast x = constantPast y /\
          Not (identityFuture x = identityFuture y) :=
    ⟨false, true, samePast, differentFuture⟩
  refine ⟨⟨witness, ?_⟩, ?_⟩
  · exact
      (inductive_sufficiency_criterion constantPast identityFuture).2.mpr witness
  · intro X History Prediction history predict factors
    exact (inductive_sufficiency_criterion history predict).1.mp factors

/-- The countermodel domain is inhabited. -/
example : Bool := false

/-- The positive descent premise is satisfiable. -/
example : Function.FactorsThrough identityFuture (id : Bool -> Bool) := by
  intro x y sameState
  simpa [identityFuture] using sameState

#print axioms hume_inductive_core

end D5.S3.ConceptDynamics.Refinement.HumeInductiveCore
