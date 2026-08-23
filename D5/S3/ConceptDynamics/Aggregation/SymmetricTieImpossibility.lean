/- GID: D5/S3/ConceptDynamics/Aggregation/SymmetricTieImpossibility
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Aggregation/SymmetricTieImpossibility
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Anonymous and candidate-neutral deterministic choice cannot resolve a two-voter tie. -/

import Mathlib.Data.Bool.Basic

/- Library-search audit trail (2026-08-23):
   * Repository searches for anonymous or neutral social-choice rules and for
     the two-voter Boolean profile found no theorem covering this obstruction.
   * The nearby aggregation module treats a three-candidate majority cycle,
     not anonymity and candidate neutrality at a two-voter tie.
   * Pinned Mathlib's exact `Bool.not_ne_self` lemma supplies the final
     fixed-point contradiction and is applied directly below. No exact theorem
     packages the source's three conditions. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Aggregation.SymmetricTieImpossibility

/-- A total deterministic rule from two Boolean voter choices to one Boolean
candidate cannot be both anonymous under voter exchange and neutral under
candidate exchange. -/
theorem symmetric_tie_impossibility :
    ¬ ∃ rule : Bool × Bool → Bool,
        (∀ profile, rule (profile.2, profile.1) = rule profile) ∧
          (∀ profile, rule (!profile.1, !profile.2) = !(rule profile)) := by
  rintro ⟨rule, anonymous, neutral⟩
  have hanonymous := anonymous (false, true)
  have hneutral := neutral (false, true)
  simp only at hanonymous hneutral
  exact Bool.not_ne_self (rule (false, true)) (hneutral.symm.trans hanonymous)

/-- The exact two-voter profile carrier is inhabited by a tied profile. -/
example : Bool × Bool := (false, true)

/-- Anonymity alone is satisfiable by a total deterministic rule. -/
example : ∃ rule : Bool × Bool → Bool,
    ∀ profile, rule (profile.2, profile.1) = rule profile := by
  exact ⟨fun _ => false, fun _ => rfl⟩

/-- Candidate neutrality alone is satisfiable by a total deterministic rule. -/
example : ∃ rule : Bool × Bool → Bool,
    ∀ profile, rule (!profile.1, !profile.2) = !(rule profile) := by
  exact ⟨Prod.fst, fun _ => rfl⟩

#print axioms symmetric_tie_impossibility

end D5.S3.ConceptDynamics.Aggregation.SymmetricTieImpossibility
