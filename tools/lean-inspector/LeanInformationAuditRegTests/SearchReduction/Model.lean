import LeanInformationAuditRegAnalysis.SearchReduction.Graph

/-! Executable evidence model for the search-reduction contract. These inputs
record certified observations; this model does not implement or certify Lean's
tactic runner. In particular, `exhausted` is not a resource exception. -/

namespace LeanInformationAudit.Tests.SearchReduction

open LeanInformationAudit.SearchReduction

theorem union_found_iff (left right : Run) :
    unionRun left right = .found ↔ left = .found ∨ right = .found := by
  cases left <;> cases right <;> simp [unionRun]

theorem union_exhausted_iff (left right : Run) :
    unionRun left right = .exhausted ↔ left = .exhausted ∧ right = .exhausted := by
  cases left <;> cases right <;> simp [unionRun]

theorem certified_restatement_bind_only (base paired : Run) (checkedS cleanS : Bool) :
    classifyCertified true .found base checkedS cleanS paired = .bindOnly := rfl

theorem incomplete_presentation_not_content (failure : Failure) (checked checkedS cleanS : Bool)
    (base paired : Run) :
    classifyCertified checked (.incomplete failure) base checkedS cleanS paired ≠ .nonBindOnly := by
  cases checked <;> cases base <;> cases checkedS <;> cases cleanS <;>
    cases paired <;> simp [classifyCertified, classify]

theorem complete_presentation_uses_model (checked checkedS cleanS : Bool) (base paired : Run) :
    classifyCertified checked .exhausted base checkedS cleanS paired =
      classify checked false base checkedS cleanS paired := rfl

theorem certified_non_bind_only_iff (checked checkedS cleanS : Bool)
    (presentation base paired : Run) :
    classifyCertified checked presentation base checkedS cleanS paired = .nonBindOnly ↔
      presentation = .exhausted ∧
        classify checked false base checkedS cleanS paired = .nonBindOnly := by
  cases presentation <;> cases checked <;> cases base <;> cases checkedS <;>
    cases cleanS <;> cases paired <;> simp [classifyCertified, classify]

/-- The four paired conditions, with the common target compilation check. -/
theorem non_bind_only_iff (checked restated checkedS cleanS : Bool) (base paired : Run) :
    classify checked restated base checkedS cleanS paired = .nonBindOnly ↔
      checked = true ∧ restated = false ∧ base = .exhausted ∧
        checkedS = true ∧ cleanS = true ∧ paired = .found := by
  cases checked <;> cases restated <;> cases base <;> cases checkedS <;>
    cases cleanS <;> cases paired <;> simp [classify]

theorem bind_only_iff (checked restated checkedS cleanS : Bool) (base paired : Run) :
    classify checked restated base checkedS cleanS paired = .bindOnly ↔
      checked = true ∧ (restated = true ∨ base = .found) := by
  cases checked <;> cases restated <;> cases base <;> cases checkedS <;>
    cases cleanS <;> cases paired <;> simp [classify]

/-- A failed baseline is not a completed negative search. -/
theorem baseline_failure_not_content (reason : Failure) (restated checkedS cleanS : Bool)
    (paired : Run) :
    classify true restated (.incomplete reason) checkedS cleanS paired ≠ .nonBindOnly := by
  simp [non_bind_only_iff]

theorem unclosed_pair_insufficient (checkedS cleanS : Bool) :
    classify true false .exhausted checkedS cleanS .exhausted = .insufficient := by
  cases checkedS <;> cases cleanS <;> rfl

/-- T4: the certificate, rather than an arbitrary equivalence proof, has priority. -/
theorem restatement_bind_only (base paired : Run) (checkedS cleanS : Bool) :
    classify true true base checkedS cleanS paired = .bindOnly := rfl

/-- T6: even a purported successful pair cannot legitimize target leakage. -/
theorem dirty_structure_not_content (checked restated checkedS : Bool) (base paired : Run) :
    classify checked restated base checkedS false paired ≠ .nonBindOnly := by
  simp [non_bind_only_iff]

/-- An uncompiled structure cannot supply content. -/
theorem unchecked_not_content (checked restated cleanS : Bool) (base paired : Run) :
    classify checked restated base false cleanS paired ≠ .nonBindOnly := by
  simp [non_bind_only_iff]

/-- T1: identifying bind-only with an unbounded provability closure leaves no
content among the already proved candidates. -/
def unboundedContent {Task : Type*} (closure : Task → Prop) (task : Task) : Prop :=
  ¬ closure task

theorem unbounded_closure_degenerate {Task : Type*} (proved closure : Task → Prop)
    (included : ∀ t, proved t → closure t) :
    ¬ ∃ t, proved t ∧ unboundedContent closure t := by
  rintro ⟨t, ht, hn⟩
  exact hn (included t ht)

/-- T2: the literal reading accepts every compiled declaration, including aliases. -/
def literal (checked : Bool) : Verdict := if checked then .nonBindOnly else .insufficient

theorem literal_accepts_alias (base paired : Run) (checkedS cleanS : Bool) :
    literal true = .nonBindOnly ∧
      classify true true base checkedS cleanS paired = .bindOnly := by
  exact ⟨rfl, restatement_bind_only base paired checkedS cleanS⟩

/-- Success inclusion says nothing about whether an unsuccessful run completed. -/
def SuccessIncluded {Task : Type*} (weak strong : Task → Run) : Prop :=
  ∀ t, weak t = .found → strong t = .found

/-- T5: strengthening the baseline can only enlarge the bind-only set. -/
theorem bind_only_monotone {Task : Type*} (weak strong : Task → Run)
    (included : SuccessIncluded weak strong) (t : Task)
    (checked restated checkedS cleanS : Bool) (paired : Run)
    (h : classify checked restated (weak t) checkedS cleanS paired = .bindOnly) :
    classify checked restated (strong t) checkedS cleanS paired = .bindOnly := by
  obtain ⟨hc, ha | hb⟩ := (bind_only_iff ..).mp h
  · exact (bind_only_iff ..).mpr ⟨hc, Or.inl ha⟩
  · exact (bind_only_iff ..).mpr ⟨hc, Or.inr (included t hb)⟩

theorem baseline_miss_antitone {Task : Type*} (weak strong : Task → Run)
    (included : SuccessIncluded weak strong) (t : Task) (h : strong t ≠ .found) :
    weak t ≠ .found := fun hw => h (included t hw)

theorem strong_content_excludes_weak_bind {Task : Type*} (weak strong : Task → Run)
    (included : SuccessIncluded weak strong) (t : Task)
    (checked restated checkedS cleanS : Bool) (paired : Run)
    (h : classify checked restated (strong t) checkedS cleanS paired = .nonBindOnly) :
    classify checked restated (weak t) checkedS cleanS paired ≠ .bindOnly := by
  intro hb
  have lifted := bind_only_monotone weak strong included t checked restated checkedS cleanS paired hb
  rw [h] at lifted
  cases lifted

/-- T5: preserving paired success preserves content only when the strengthened
baseline still completes without finding the target. -/
theorem paired_content_preserved {Task : Type*} (weak strong : Task → Run)
    (included : SuccessIncluded weak strong) (t : Task)
    (checked restated checkedS cleanS : Bool) (oldBase : Run)
    (h : classify checked restated oldBase checkedS cleanS (weak t) = .nonBindOnly) :
    classify checked restated .exhausted checkedS cleanS (strong t) = .nonBindOnly := by
  obtain ⟨hc, ha, _, hs, hn, hp⟩ := (non_bind_only_iff ..).mp h
  exact (non_bind_only_iff ..).mpr ⟨hc, ha, rfl, hs, hn, included t hp⟩

/-- New paired success may move insufficient evidence to content under a stronger
searcher. A blanket antitonicity claim for paired content would be false. -/
theorem paired_content_not_globally_antitone :
    SuccessIncluded (fun _ : Unit => Run.exhausted) (fun _ => Run.found) ∧
    classify true false .exhausted true true .exhausted = .insufficient ∧
    classify true false .exhausted true true .found = .nonBindOnly := by
  refine ⟨?_, rfl, rfl⟩
  intro _ h
  cases h

theorem verdicts_exhaustive (checked restated checkedS cleanS : Bool) (base paired : Run) :
    let v := classify checked restated base checkedS cleanS paired
    v = .bindOnly ∨ v = .nonBindOnly ∨ v = .insufficient := by
  dsimp
  cases classify checked restated base checkedS cleanS paired <;> simp

#print axioms certified_restatement_bind_only
#print axioms incomplete_presentation_not_content
#print axioms complete_presentation_uses_model
#print axioms certified_non_bind_only_iff
#print axioms non_bind_only_iff
#print axioms union_found_iff
#print axioms union_exhausted_iff
#print axioms bind_only_iff
#print axioms baseline_failure_not_content
#print axioms unclosed_pair_insufficient
#print axioms restatement_bind_only
#print axioms dirty_structure_not_content
#print axioms unchecked_not_content
#print axioms unbounded_closure_degenerate
#print axioms literal_accepts_alias
#print axioms bind_only_monotone
#print axioms baseline_miss_antitone
#print axioms strong_content_excludes_weak_bind
#print axioms paired_content_preserved
#print axioms paired_content_not_globally_antitone
#print axioms verdicts_exhaustive

end LeanInformationAudit.Tests.SearchReduction
