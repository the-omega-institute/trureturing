/- GID: D5/S3/ConceptDynamics/InstitutionalCapture/IndependentSourceCaptureLowerBound
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/InstitutionalCapture/IndependentSourceCaptureLowerBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Independent irreplaceable branch sources force a capture lower bound. -/

import D5.S3.ConceptDynamics.InstitutionalCapture.CommonSourceCaptureCollapse

/- Library-search audit trail (2026-08-22):
   * `rg -n -F 'independent_source_capture_lower_bound' D5 Golden/Frozen/accepted`
     now hits only this module's audit, theorem, and `#print`; excluding this
     module with `--glob '!IndependentSourceCaptureLowerBound.lean'` found no hit.
   * The required ConceptDynamics search found only the sibling common-source
     theorem as an institutional-capture result. This module imports and reuses
     its `branchCompromised`, `capturesAllBranches`, and `captureNumber` definitions.
   * Mathlib searches found and the proof directly reuses
     `Set.ncard_range_of_injective`, `Set.ncard_le_ncard`, and `Nat.sInf_mem`.
     No institutional-capture theorem beyond the imported sibling was found. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.InstitutionalCapture.IndependentSourceCaptureLowerBound

open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.InstitutionalCapture.CommonSourceCaptureCollapse

/-- A family of branch sources is independent and irreplaceable when its source
assignment is injective and exactly the assigned source controls each branch. -/
def independentNecessarySources
    {Source State Signal Branch Result : Type*}
    (channel : Source -> Concept State Signal)
    (output : Branch -> Concept State Result)
    (source : Branch -> Source) : Prop :=
  Function.Injective source ∧ forall branch candidate,
    (output branch).FactorsThrough (channel candidate) ↔
      candidate = source branch

/-- Independent irreplaceable sources for finitely many branches force every
all-branch capture, hence the minimum capture number, to use at least one source
per branch. -/
theorem independent_source_capture_lower_bound
    {Source State Signal Branch Result : Type*}
    [Fintype Branch]
    (channel : Source -> Concept State Signal)
    (output : Branch -> Concept State Result)
    (source : Branch -> Source)
    (independent : independentNecessarySources channel output source) :
    Fintype.card Branch <= captureNumber channel output := by
  let candidateSizes : Set Nat :=
    {size | exists controlled : Set Source,
      controlled.Finite ∧ controlled.ncard = size ∧
        capturesAllBranches channel output controlled}
  have rangeCaptures :
      capturesAllBranches channel output (Set.range source) := by
    intro branch
    exact ⟨source branch, Set.mem_range_self branch,
      (independent.2 branch (source branch)).2 rfl⟩
  have rangeCandidate : Fintype.card Branch ∈ candidateSizes := by
    refine ⟨Set.range source, Set.finite_range source, ?_, rangeCaptures⟩
    rw [Set.ncard_range_of_injective independent.1, Nat.card_eq_fintype_card]
  change Fintype.card Branch <= sInf candidateSizes
  have minimumCandidate : sInf candidateSizes ∈ candidateSizes :=
    Nat.sInf_mem ⟨Fintype.card Branch, rangeCandidate⟩
  rcases minimumCandidate with
    ⟨controlled, controlledFinite, controlledCard, captures⟩
  have rangeSubset : Set.range source ⊆ controlled := by
    rintro _ ⟨branch, rfl⟩
    rcases captures branch with ⟨candidate, candidateMem, controls⟩
    have candidateEq : candidate = source branch :=
      (independent.2 branch candidate).1 controls
    simpa only [candidateEq] using candidateMem
  calc
    Fintype.card Branch = (Set.range source).ncard := by
      rw [Set.ncard_range_of_injective independent.1, Nat.card_eq_fintype_card]
    _ <= controlled.ncard := Set.ncard_le_ncard rangeSubset controlledFinite
    _ = sInf candidateSizes := controlledCard

/-- Three identity branches with three distinct sources realize the lower-bound
hypotheses and have capture number exactly three. -/
example :
    let readout : Fin 3 -> Concept (Fin 3 × Bool) Bool :=
      fun source state => if state.1 = source then state.2 else false
    captureNumber readout readout = 3 := by
  dsimp only
  let readout : Fin 3 -> Concept (Fin 3 × Bool) Bool :=
    fun source state => if state.1 = source then state.2 else false
  change captureNumber readout readout = 3
  have independent : independentNecessarySources readout readout id := by
    refine ⟨Function.injective_id, ?_⟩
    intro branch candidate
    constructor
    · intro factors
      by_contra unequal
      change candidate ≠ branch at unequal
      have sameCandidate :
          readout candidate (branch, false) =
            readout candidate (branch, true) := by
        simp [readout, Ne.symm unequal]
      have sameBranch := factors sameCandidate
      simp [readout] at sameBranch
    · intro candidateEq
      subst candidate
      exact Function.FactorsThrough.rfl
  apply le_antisymm
  · rw [captureNumber]
    apply Nat.sInf_le
    refine ⟨Set.univ, Set.finite_univ, by simp, ?_⟩
    intro branch
    exact ⟨branch, Set.mem_univ branch, Function.FactorsThrough.rfl⟩
  · simpa using
      independent_source_capture_lower_bound readout readout id independent

#print axioms independent_source_capture_lower_bound

end D5.S3.ConceptDynamics.InstitutionalCapture.IndependentSourceCaptureLowerBound
