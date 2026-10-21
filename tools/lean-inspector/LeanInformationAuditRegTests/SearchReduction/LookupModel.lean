import LeanInformationAuditRegTests.SearchReduction.GraphModel

/-! Production lookup guards and their proof-hard boundary. -/
namespace LeanInformationAudit.Tests.SearchReduction.GraphModel
open LeanInformationAudit.SearchReduction

/-- A positive verdict cannot be inferred from an unfinished root query. -/
theorem nonBindOnly_root_exhausted (reading : GraphReading)
    (positive : classifyGraph reading = .nonBindOnly) :
    reading.baselineProbe.outcome = .exhausted := by
  unfold classifyGraph at positive
  split at positive
  · contradiction
  · split at positive
    · rename_i condition
      simp only [Bool.and_eq_true, beq_iff_eq] at condition
      tauto
    · contradiction

theorem unfinished_root_not_nonBindOnly (reading : GraphReading) (failure : Failure)
    (unfinished : reading.baselineProbe.outcome = .incomplete failure) :
    classifyGraph reading ≠ .nonBindOnly := by
  intro positive
  have completed := nonBindOnly_root_exhausted reading positive
  rw [unfinished] at completed
  contradiction

/-- This is the production proof_hard predicate, with the actual baseline
depth supplied by its caller; zero-cost helpers cannot enter this witness list. -/
theorem zero_helper_not_proof_hard (graph : ProofGraph) (selected : List Nat) (id : Nat) :
    proofHardEligible graph selected id (.finite 0) = false := by
  simp [proofHardEligible]

theorem proof_hard_requires_lookup_exhausted (graph : ProofGraph)
    (selected : List Nat) (id : Nat) (baselineDepth : Bound)
    (hard : proofHardEligible graph selected id baselineDepth = true) :
    ∃ v ∈ graph.vertices, v.id = id ∧ v.independentLookup = .exhausted := by
  simp only [proofHardEligible, Bool.and_eq_true] at hard
  have found := hard.1.2
  cases h : graph.vertices.find? (·.id == id) with
  | none => simp [h] at found
  | some v =>
    refine ⟨v, List.mem_of_find?_eq_some h, ?_, ?_⟩
    · simpa using List.find?_some h
    · simpa [h] using found

#print axioms nonBindOnly_root_exhausted
#print axioms unfinished_root_not_nonBindOnly
#print axioms zero_helper_not_proof_hard
#print axioms proof_hard_requires_lookup_exhausted

end LeanInformationAudit.Tests.SearchReduction.GraphModel
