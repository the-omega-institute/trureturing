import LeanInformationAuditRegTests.SearchReduction.FiniteModel

/-! Statement-level prefix and scope model. This does not verify the metaprogram. -/
namespace LeanInformationAudit.Tests.SearchReduction.VocabularyModel
open FiniteModel
open LeanInformationAudit.SearchReduction (Failure Run)

/-- Weakening transports derivations, without asserting that a bounded search
will find the transported proof. -/
theorem derives_weaken {small large : List Atom} (subset : ∀ c ∈ small, c ∈ large)
    {t : Atom} (proof : Derives small t) : Derives large t := by
  induction proof with
  | premise h => exact .premise (subset _ h)
  | bridge _ ih => exact .bridge ih
  | target _ ih => exact .target ih

theorem search_subbase_certificate {small large : List Atom}
    (subset : ∀ c ∈ small, c ∈ large) (fuel : Nat) (t : Atom)
    (found : search fuel small t = true) : Derives large t :=
  derives_weaken subset (search_sound fuel small t found)

/-- A real finite counterexample to uploading a bounded miss. -/
theorem finite_miss_does_not_upload :
    (∀ c ∈ ([Atom.seed] : List Atom), c ∈ [Atom.seed, Atom.bridge]) ∧
    run [.seed] .target = .exhausted ∧
    run [.seed, .bridge] .target = .found := by
  decide

/-- Cut eliminates a reconstructed certificate from the final proof. -/
theorem derives_cut {base certificates : List Atom}
    (closed : ∀ c ∈ certificates, Derives base c) {t : Atom}
    (proof : Derives (base ++ certificates) t) : Derives base t := by
  induction proof with
  | premise h =>
    rcases List.mem_append.mp h with h | h
    · exact .premise h
    · exact closed _ h
  | bridge _ ih => exact .bridge ih
  | target _ ih => exact .target ih

/-- Each obligation sees B and only the already completed prefix. -/
inductive Prefix (base : List Atom) : List Atom → Prop where
  | nil : Prefix base []
  | step {earlier : List Atom} {c : Atom} : Prefix base earlier →
      Derives (base ++ earlier) c → Prefix base (earlier ++ [c])

theorem prefix_certificates_close {base certificates : List Atom}
    (chain : Prefix base certificates) : ∀ c ∈ certificates, Derives base c := by
  induction chain with
  | nil => simp
  | @step earlier c _ proof ih =>
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact ih x hx
    · have equal : x = c := by simpa using hx
      subst x
      exact derives_cut ih proof

/-- The output derives the same target in the original environment. All
certificate assumptions disappear; there are no extra axiom constructors. -/
theorem prefix_reconstruction_preserves_target {base certificates : List Atom}
    (chain : Prefix base certificates) {t : Atom}
    (typed : Derives (base ++ certificates) t) : Derives base t :=
  derives_cut (prefix_certificates_close chain) typed

/-- Transport failure cannot create a content verdict, even with a found pair. -/
theorem transport_failure_not_non_bind_only (failure : Failure) (paired : Run) :
    classifyCertified true (.incomplete failure) (.incomplete failure) true true paired ≠
      .nonBindOnly :=
  incomplete_presentation_not_content failure true true true (.incomplete failure) paired

/-- Independent search unions keep the existing found/exhausted laws. -/
theorem prefix_union_found (a b : Run) :
    unionRun a b = .found ↔ a = .found ∨ b = .found := union_found_iff a b

theorem prefix_union_exhausted (a b : Run) :
    unionRun a b = .exhausted ↔ a = .exhausted ∧ b = .exhausted := union_exhausted_iff a b

#print axioms derives_weaken
#print axioms search_subbase_certificate
#print axioms finite_miss_does_not_upload
#print axioms derives_cut
#print axioms prefix_certificates_close
#print axioms prefix_reconstruction_preserves_target
#print axioms transport_failure_not_non_bind_only
end LeanInformationAudit.Tests.SearchReduction.VocabularyModel
