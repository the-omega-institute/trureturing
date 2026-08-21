/- GID: D5/S3/ConceptDynamics/Dialectics/MinimalDialecticalRepair
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Dialectics/MinimalDialecticalRepair
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Construct the least target-complete repair and expose carry as a closure refutation. -/

/- Library-search audit trail (2026-08-22):
   * The source defines a carry witness as a same-current, different-consequence
     pair and defines relative completion as the joint readout.
   * Exact repository hit `concept_join_universal` supplies both refinement
     projections and the universal least-common-refinement property; it is
     imported and applied directly below.
   * Searches for carry refutation and minimal conceptual repair found no theorem
     combining the explicit witness clause with all three completion clauses.
-/

import D5.S3.ConceptDynamics.ConceptJoinUniversal

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Dialectics.MinimalDialecticalRepair

open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.ConceptJoinUniversal

/-- Two states are a carry witness when the current readout identifies them but
the target consequence separates them. -/
def IsCarryWitness {X Current Target : Type _}
    (current : Concept X Current) (process : X → X) (target : Concept X Target)
    (left right : X) : Prop :=
  current left = current right ∧
    target (process left) ≠ target (process right)

/--
The joint readout of the current concept and target consequence preserves the
current distinctions, decides the target, is least among such refinements, and
turns every explicit carry into a refutation of current target-closure.
-/
theorem minimal_dialectical_repair
    {X Current Target : Type _}
    (current : Concept X Current) (process : X → X) (target : Concept X Target) :
    Refines current (conceptJoin current (target ∘ process)) ∧
    Refines (target ∘ process) (conceptJoin current (target ∘ process)) ∧
    (∀ {Candidate : Type _} (candidate : Concept X Candidate),
      Refines current candidate → Refines (target ∘ process) candidate →
        Refines (conceptJoin current (target ∘ process)) candidate) ∧
    ∀ {left right}, IsCarryWitness current process target left right →
      ¬Refines (target ∘ process) current := by
  refine ⟨(concept_join_universal current (target ∘ process)
      (conceptJoin current (target ∘ process))).1,
    (concept_join_universal current (target ∘ process)
      (conceptJoin current (target ∘ process))).2.1, ?_, ?_⟩
  · intro Candidate candidate hCurrent hTarget
    exact (concept_join_universal current (target ∘ process) candidate).2.2
      hCurrent hTarget
  · intro left right witness
    rintro ⟨factor, hfactor⟩
    apply witness.2
    calc
      target (process left) = factor (current left) :=
        congrFun hfactor left
      _ = factor (current right) :=
        congrArg factor witness.1
      _ = target (process right) :=
        (congrFun hfactor right).symm

/-- A concrete carry exists when a constant current readout hides a Boolean target. -/
def booleanCarry :
    IsCarryWitness (fun _ : Bool => ()) id id false true :=
  ⟨rfl, Bool.false_ne_true⟩

example : ¬Refines (id : Bool → Bool) (fun _ : Bool => ()) :=
  (minimal_dialectical_repair.{0, 0, 0, 0}
    (fun _ : Bool => ()) id id).2.2.2 booleanCarry

#print axioms minimal_dialectical_repair

end D5.S3.ConceptDynamics.Dialectics.MinimalDialecticalRepair
