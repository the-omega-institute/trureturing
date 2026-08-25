/- GID: D5/S3/ConceptDynamics/Audits/CountermodelRepairUnderdetermination
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Audits/CountermodelRepairUnderdetermination
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A countermodel permits distinct repairs without selecting the repaired component. -/

import Mathlib.Data.Set.Lattice

/- Library-search audit trail (2026-08-26):
   * Repository searches for countermodels, diagnostic alternatives, and
     repair underdetermination found no exact frozen theorem.
   * The adjacent incomparable-cost theorem supplies only a special two-face
     cost comparison, so it is neither an exact hit nor a prerequisite.
   * Body-shape searches found no canonical primitive for either witnessed
     predicate restriction or conclusion enlargement; both remain inline.
   * Pinned Mathlib has the strict-subset witness criterion
     `Set.ssubset_iff_exists`, which is applied directly below. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Audits.CountermodelRepairUnderdetermination

/-- A model satisfying the assumptions and refuting the conclusion exposes the
four advertised diagnostic alternatives. The same witness also yields two
different kinds of strict response: restrict the assumptions or enlarge the
conclusion. In either case the corresponding countermodel set shrinks strictly,
so the witness itself does not select which component should be revised. -/
theorem countermodel_diagnosis_is_underdetermined
    (Model : Type*) (assumptions conclusion : Set Model)
    (inferenceRule : Set Model → Set Model → Prop) (model : Model)
    (countermodel : model ∈ assumptions \ conclusion) :
    (model ∉ conclusion ∨
      ¬assumptions ⊆ conclusion ∨
      (∃ revisedAssumptions : Set Model,
        revisedAssumptions ⊂ assumptions ∧ model ∉ revisedAssumptions) ∨
      (inferenceRule assumptions conclusion ∧ ¬assumptions ⊆ conclusion)) ∧
    ({candidate | candidate ∈ assumptions ∧ candidate ≠ model} : Set Model) ⊂
        assumptions ∧
    (({candidate | candidate ∈ assumptions ∧ candidate ≠ model} : Set Model) \
        conclusion) ⊂ assumptions \ conclusion ∧
    conclusion ⊂ {candidate | candidate ∈ conclusion ∨ candidate = model} ∧
    (assumptions \
        {candidate | candidate ∈ conclusion ∨ candidate = model}) ⊂
      assumptions \ conclusion := by
  have modelAssumed : model ∈ assumptions := countermodel.1
  have modelRefutes : model ∉ conclusion := countermodel.2
  constructor
  · exact Or.inl modelRefutes
  constructor
  · apply Set.ssubset_iff_exists.mpr
    refine ⟨?_, model, modelAssumed, ?_⟩
    · intro candidate candidateRestricted
      exact candidateRestricted.1
    · simp
  constructor
  · apply Set.ssubset_iff_exists.mpr
    refine ⟨?_, model, countermodel, ?_⟩
    · intro candidate candidateRestricted
      exact ⟨candidateRestricted.1.1, candidateRestricted.2⟩
    · simp
  constructor
  · apply Set.ssubset_iff_exists.mpr
    refine ⟨?_, model, ?_, ?_⟩
    · intro candidate candidateConcluded
      exact Or.inl candidateConcluded
    · exact Or.inr rfl
    · exact modelRefutes
  · apply Set.ssubset_iff_exists.mpr
    refine ⟨?_, model, countermodel, ?_⟩
    · intro candidate candidateRepaired
      refine ⟨candidateRepaired.1, ?_⟩
      intro candidateConcluded
      exact candidateRepaired.2 (Or.inl candidateConcluded)
    · simp

#print axioms countermodel_diagnosis_is_underdetermined

end D5.S3.ConceptDynamics.Audits.CountermodelRepairUnderdetermination
