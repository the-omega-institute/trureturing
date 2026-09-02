/- GID: D5/S3/ConceptDynamics/Answering/RenderCeilingDisclosure
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Answering/RenderCeilingDisclosure
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: An audited render never exceeds the register ceiling and discloses only the record. -/

import D5.S3.ConceptDynamics.Answering.AssertionSettlementCeiling

/- Library-search audit trail (2026-09-02):
   * Exact repository hits `settle`, `permits`, `Claim.isFormal`,
     `open_permits_only_unsettled`, and `formal_claim_requires_successful_build`
     in `AssertionSettlementCeiling` supply the register ceiling and its
     soundness; this module applies them to a rendered draft.
   * `rg -l 'render|Render|disclos|Disclos' D5 --include='*.lean'` hit the
     `Disclosure` information-flow modules, which bound secret leakage from
     observations; none models a prose draft audited against a claim ceiling
     or a disclosure switch that attaches the internal record.
   * Pinned Lean core supplies `List.all_eq_true` and `Option.some.inj`; no
     upstream declaration packages the audited renderer. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Answering.RenderCeilingDisclosure

open D5.S3.ConceptDynamics.Answering.AssertionSettlementCeiling

/-- One competent-reader takeaway of a draft: the assertion key it is about and
the claim a competent reader would take away from it. -/
structure Takeaway (Key : Type*) where
  key : Key
  claim : Claim
  deriving DecidableEq

/-- A takeaway is within the ceiling when the settled outcome of its key permits
its claim. The register is the renderer's only epistemic input. -/
def withinCeiling {Key : Type*} (register : Key → Evidence) (t : Takeaway Key) : Bool :=
  permits (settle (register t.key)) t.claim

/-- The audit passes when every takeaway of the draft is within the ceiling. -/
def auditPasses {Key : Type*} (register : Key → Evidence) (draft : List (Takeaway Key)) :
    Bool :=
  draft.all (withinCeiling register)

/-- Disclosure mode: the plain conversational answer, or the answer with its
internal run record attached on request. -/
inductive Disclosure
  | plain
  | showWork
  deriving DecidableEq, Repr

/-- The rendered output: the audited prose and, only on request, the record. -/
structure Output (Key Record : Type*) where
  prose : List (Takeaway Key)
  record : Option Record
  deriving DecidableEq

/-- The record is attached exactly in `showWork` mode. -/
def attach {Record : Type*} (record : Record) : Disclosure → Option Record
  | .plain => none
  | .showWork => some record

/-- Render emits the draft only when the audit passes, attaching the record
according to the disclosure mode; a draft that exceeds the ceiling is not emitted. -/
def render {Key Record : Type*} (register : Key → Evidence) (record : Record)
    (mode : Disclosure) (draft : List (Takeaway Key)) : Option (Output Key Record) :=
  if auditPasses register draft then some ⟨draft, attach record mode⟩ else none

/-- Every takeaway of an emitted answer is permitted by the settled outcome of
its assertion key. -/
theorem rendered_takeaway_within_ceiling {Key Record : Type*} (register : Key → Evidence)
    (record : Record) (mode : Disclosure) (draft : List (Takeaway Key))
    (out : Output Key Record) (h : render register record mode draft = some out) :
    ∀ t ∈ out.prose, permits (settle (register t.key)) t.claim = true := by
  unfold render at h
  by_cases haudit : auditPasses register draft = true
  · rw [if_pos haudit] at h
    obtain rfl := Option.some.inj h
    intro t ht
    exact List.all_eq_true.mp haudit t ht
  · rw [if_neg haudit] at h
    exact absurd h (by simp)

/-- Every formal-grade claim conveyed by an emitted answer is backed by one
successful current build of the exact statement it is about. -/
theorem rendered_formal_claim_is_compiled {Key Record : Type*} (register : Key → Evidence)
    (record : Record) (mode : Disclosure) (draft : List (Takeaway Key))
    (out : Output Key Record) (h : render register record mode draft = some out) :
    ∀ t ∈ out.prose, t.claim.isFormal = true → (register t.key).buildSucceeded = true := by
  intro t ht hf
  exact formal_claim_requires_successful_build (register t.key) t.claim hf
    (rendered_takeaway_within_ceiling register record mode draft out h t ht)

/-- A draft that conveys anything about an `open` assertion is not emitted in
any disclosure mode. -/
theorem open_key_blocks_emission {Key Record : Type*} (register : Key → Evidence)
    (record : Record) (mode : Disclosure) (draft : List (Takeaway Key)) (t : Takeaway Key)
    (ht : t ∈ draft) (hopen : settle (register t.key) = .open) (hf : t.claim ≠ .unsettled) :
    render register record mode draft = none := by
  unfold render
  rw [if_neg]
  intro haudit
  have hwithin : withinCeiling register t = true := List.all_eq_true.mp haudit t ht
  unfold withinCeiling at hwithin
  rw [hopen] at hwithin
  exact hf ((open_permits_only_unsettled t.claim).mp hwithin)

/-- Disclosure changes what is attached, never what is claimed: the plain answer
and the show-work answer carry the same audited prose. -/
theorem disclosure_preserves_claims {Key Record : Type*} (register : Key → Evidence)
    (record : Record) (draft : List (Takeaway Key)) :
    (render register record .plain draft).map Output.prose =
      (render register record .showWork draft).map Output.prose := by
  unfold render
  split <;> rfl

/-- In show-work mode the emitted answer carries the internal record. -/
theorem show_work_exposes_record {Key Record : Type*} (register : Key → Evidence)
    (record : Record) (draft : List (Takeaway Key)) (out : Output Key Record)
    (h : render register record .showWork draft = some out) : out.record = some record := by
  unfold render at h
  split at h
  · obtain rfl := Option.some.inj h
    rfl
  · exact absurd h (by simp)

/-- In plain mode the emitted answer carries no internal record. -/
theorem plain_answer_hides_record {Key Record : Type*} (register : Key → Evidence)
    (record : Record) (draft : List (Takeaway Key)) (out : Output Key Record)
    (h : render register record .plain draft = some out) : out.record = none := by
  unfold render at h
  split at h
  · obtain rfl := Option.some.inj h
    rfl
  · exact absurd h (by simp)

/-- A two-key register: key `true` is proved, key `false` is open. -/
def sampleRegister : Bool → Evidence
  | true => ⟨.formalizable, true, true, true, false, 0⟩
  | false => ⟨.ambiguous, true, false, false, false, 0⟩

/- The plain answer may assert the proved key and call the open key unsettled. -/
example : render sampleRegister () .plain [⟨true, .assertP⟩, ⟨false, .unsettled⟩] =
    some ⟨[⟨true, .assertP⟩, ⟨false, .unsettled⟩], none⟩ := by
  decide

/- The same draft in show-work mode attaches the record and keeps the prose. -/
example : render sampleRegister () .showWork [⟨true, .assertP⟩, ⟨false, .unsettled⟩] =
    some ⟨[⟨true, .assertP⟩, ⟨false, .unsettled⟩], some ()⟩ := by
  decide

/- Asserting the open key is rejected in both modes. -/
example : render sampleRegister () .plain [⟨false, .assertP⟩] = none ∧
    render sampleRegister () .showWork [⟨false, .assertP⟩] = none := by
  decide

#print axioms rendered_takeaway_within_ceiling
#print axioms rendered_formal_claim_is_compiled
#print axioms open_key_blocks_emission
#print axioms disclosure_preserves_claims
#print axioms show_work_exposes_record
#print axioms plain_answer_hides_record

end D5.S3.ConceptDynamics.Answering.RenderCeilingDisclosure
