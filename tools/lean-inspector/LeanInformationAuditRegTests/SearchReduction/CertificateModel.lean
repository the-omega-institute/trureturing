import LeanInformationAuditRegTests.SearchReduction.LookupModel
import LeanInformationAuditRegAnalysis.SearchReduction.Local

/-! Certificate and interval models, with the production edge-attachment interface. -/

namespace LeanInformationAudit.Tests.SearchReduction.CertificateModel
open LeanInformationAudit.SearchReduction
open GraphModel

/-- Accepted certificates use the same finite domain and candidate-local
resource policy as the mechanical reference enumerator. -/
def Accepted (scope : List ObviousCertificate)
    (attempt : ObviousCertificate → Option LookupCandidateAttempt)
    (preparation search : Nat) (certificate : ObviousCertificate) : Prop :=
  certificate ∈ scope ∧ candidateOutcome preparation search (attempt certificate) = .found

theorem cert_iff_candidate_success (scope : List ObviousCertificate)
    (attempt : ObviousCertificate → Option LookupCandidateAttempt) (preparation search : Nat) :
    (∃ certificate, Accepted scope attempt preparation search certificate) ↔
      perCandidateLookup scope attempt preparation search = .found := by
  simpa only [Accepted] using (perCandidate_found scope attempt preparation search).symm

theorem nohit_excludes_cert (scope : List ObviousCertificate)
    (attempt : ObviousCertificate → Option LookupCandidateAttempt) (preparation search : Nat)
    (nohit : perCandidateLookup scope attempt preparation search = .exhausted) :
    ¬ ∃ certificate, Accepted scope attempt preparation search certificate := by
  rintro ⟨certificate, member, found⟩
  have failed := (perCandidate_nohit scope attempt preparation search).mp nohit certificate member
  rw [failed] at found
  contradiction

theorem scope_symmetry (scope : List ObviousCertificate)
    (base paired : ObviousCertificate → Option LookupCandidateAttempt)
    (preparation search : Nat) (certificate : ObviousCertificate) :
    (Accepted scope base preparation search certificate ∨
      Accepted scope paired preparation search certificate) → certificate ∈ scope := by
  intro accepted
  rcases accepted with accepted | accepted <;> exact accepted.1

/-- This uses the production strictDrop function and quantifies over every
completion lying inside the certified endpoint envelope. -/
theorem interval_strictDrop_sound (base paired : Interval) (baseValue pairedValue : Nat)
    (baseBound : base.lower ≤ Bound.finite baseValue)
    (pairedBound : Bound.finite pairedValue ≤ paired.upper)
    (drop : strictDrop base paired = true) : pairedValue < baseValue := by
  cases hl : base.lower with
  | top => simp [strictDrop, hl] at drop
  | finite lower =>
    cases hu : paired.upper with
    | top => simp [strictDrop, hl, hu] at drop
    | finite upper =>
      simp only [strictDrop, hl, hu, decide_eq_true_eq] at drop
      rw [hl] at baseBound
      rw [hu] at pairedBound
      change lower ≤ baseValue at baseBound
      change pairedValue ≤ upper at pairedBound
      omega

/-- Any later full attack inside the current envelope still has a strict
drop when the lazy procedure grants one. Other lazy exits grant no positive. -/
theorem interval_lazy_exit_conservative (base paired : Interval) (baseValue pairedValue : Nat)
    (baseBound : base.lower ≤ Bound.finite baseValue)
    (pairedBound : Bound.finite pairedValue ≤ paired.upper) :
    (strictDrop base paired = true → pairedValue < baseValue) ∧
    (strictDrop base paired = false →
      (if strictDrop base paired then Verdict.nonBindOnly else .insufficient) = .insufficient) := by
  constructor
  · exact interval_strictDrop_sound base paired baseValue pairedValue baseBound pairedBound
  · intro failed
    simp [failed]

/-- The production classifier reads neither a paired negative probe nor the
paired lower endpoint. Both can remain unresolved. -/
theorem paired_negative_irrelevant (reading : GraphReading) (probe : ProbeResult)
    (lower : Bound) :
    classifyGraph {reading with pairedProbe := probe, paired := {reading.paired with lower}} =
      classifyGraph reading := rfl

/-- Holding the paired distance fixed, a new base certificate can only lower
the base distance and cannot create a strict drop that was absent before. -/
theorem base_cert_never_creates_nonBindOnly (before after paired : Nat)
    (baseImproves : after ≤ before) (noOldDrop : before ≤ paired) : ¬ paired < after := by
  omega

/-- The actual production normalization of positive evidence has no one-price
branch, regardless of any producer's proposed price. -/
theorem attack_failure_not_cost_one (certificate : ObviousCertificate) (result : LocalResult) :
    (certificateOnlyResult certificate result).cost ≠ .one := by
  unfold certificateOnlyResult
  split
  · rename_i checked
    simp only [Bool.and_eq_true, beq_iff_eq] at checked
    simp [checked.1]
  · simp

theorem no_certificate_not_imp_not_obvious :
    ∃ (scope nominations : List ObviousCertificate)
      (attempt : ObviousCertificate → Option LookupCandidateAttempt),
      (¬ ∃ c ∈ nominations, Accepted scope attempt 1 1 c) ∧
      (∃ c, Accepted scope attempt 1 1 c) := by
  refine ⟨[.close], [], fun _ => some ⟨0, 0, .found⟩, ?_, ?_⟩
  · simp
  · exact ⟨.close, by simp [Accepted, candidateOutcome]⟩

/-- This is the exact edge-attachment function used by priceGraph and lazy
baseline refinement, preserving the replayed term and actual support. The
kernel and source-audit calls that authorize the attachment remain meta work. -/
theorem certificate_to_GraphEdge (edge : GraphEdge) (certificate : ObviousCertificate)
    (proof : Lean.Expr) (used : List Nat) :
    (attachCertificate edge false certificate proof used).cost = .zero ∧
    (attachCertificate edge false certificate proof used).zeroProof = some proof ∧
    (attachCertificate edge false certificate proof used).usedPremises = used ∧
    (attachCertificate edge true certificate proof used).pairedCost = .zero ∧
    (attachCertificate edge true certificate proof used).pairedZeroProof = some proof ∧
    (attachCertificate edge true certificate proof used).pairedUsedPremises = used := by
  simp [attachCertificate]

/-- A completed reverse negative is sufficient to clear the target-part
exclusion even though no positive reverse certificate was nominated. -/
theorem reverse_nohit_clears_target_part (independent : Run) :
    targetPartDecision independent .exhausted = .exhausted := by
  cases independent <;> rfl

/-- Neither an incomplete reverse attack nor an incomplete independent attack
with a reverse hit can silently clear the exclusion guard. -/
theorem unresolved_target_part_blocks (reason : Failure) :
    targetPartDecision .exhausted (.incomplete reason) = .incomplete .undecided ∧
    targetPartDecision (.incomplete reason) .found = .incomplete .undecided := by
  exact ⟨rfl, rfl⟩

/-- The decision set contains the missing reverse query, and omits it after a
hit, after NoHit, without a decisive gap, or with unresolved independence. -/
theorem reverse_lazy_decision_set (reason : Failure) :
    needsReverseNegative true .exhausted (.incomplete reason) = true ∧
    needsReverseNegative true .exhausted .found = false ∧
    needsReverseNegative true .exhausted .exhausted = false ∧
    needsReverseNegative false .exhausted (.incomplete reason) = false ∧
    needsReverseNegative true (.incomplete reason) (.incomplete reason) = false := by
  simp [needsReverseNegative]

/-- Reverse evidence cannot change prices, intervals, or paired negative
probes; it only changes the vertex exclusion bookkeeping. -/
theorem reverse_evidence_price_irrelevant (reading : GraphReading)
    (vertices : List GraphVertex) :
    ({reading with graph := {reading.graph with vertices}} : GraphReading).baseline =
        reading.baseline ∧
    ({reading with graph := {reading.graph with vertices}} : GraphReading).paired =
        reading.paired ∧
    ({reading.graph with vertices} : ProofGraph).edges = reading.graph.edges := by
  exact ⟨rfl, rfl, rfl⟩

#print axioms reverse_nohit_clears_target_part
#print axioms unresolved_target_part_blocks
#print axioms reverse_lazy_decision_set
#print axioms reverse_evidence_price_irrelevant

#print axioms cert_iff_candidate_success
#print axioms nohit_excludes_cert
#print axioms scope_symmetry
#print axioms interval_strictDrop_sound
#print axioms interval_lazy_exit_conservative
#print axioms paired_negative_irrelevant
#print axioms base_cert_never_creates_nonBindOnly
#print axioms attack_failure_not_cost_one
#print axioms no_certificate_not_imp_not_obvious
#print axioms certificate_to_GraphEdge

end LeanInformationAudit.Tests.SearchReduction.CertificateModel
