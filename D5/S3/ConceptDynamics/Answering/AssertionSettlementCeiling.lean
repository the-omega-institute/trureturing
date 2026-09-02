/- GID: D5/S3/ConceptDynamics/Answering/AssertionSettlementCeiling
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Answering/AssertionSettlementCeiling
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: First-match settlement of an assertion record bounds its permitted public claim. -/

import Mathlib.Logic.Basic

/- Library-search audit trail (2026-09-02):
   * `rg -l 'permittedClaim|ceiling|Ceiling' D5 --include='*.lean'` hit only
     identification-depth and Renyi-order modules; none models an outcome
     register or a claim ceiling.
   * `rg -l 'Outcome' D5` hit `Audits/ProcedureDerivedCorrectOutcome` and
     `Audits/OutcomeLogAccountabilityCompletion`, which concern audit-log
     accountability, not the five-outcome first-match settlement of a formal
     answer record.
   * `SpectrumCommitmentSettlement` settles five parent atoms by a vote count;
     it does not rank public claims or bound them by compiled evidence.
   * Pinned Mathlib supplies only `Bool` and `Nat` simp lemmas here; every
     statement below is a finite case analysis over the settlement function. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Answering.AssertionSettlementCeiling

/-- Clause-shape classification, fixed at inventory time and never revised by
proof difficulty, elapsed effort, or compiler availability. -/
inductive Classification
  | formalizable
  | conditionalEmpirical
  | ambiguous
  | notFormalizable
  deriving DecidableEq, Repr

/-- The five settlement outcomes of one assertion record. -/
inductive Outcome
  | notFormalized
  | conditional
  | proved
  | refuted
  | open
  deriving DecidableEq, Repr

/-- Build evidence for one assertion record. `establishesP` and `establishesNegP`
say that the compiled statement is exact `P` or its exact negation;
`buildSucceeded` says that one current canonical build succeeded; `undischarged`
counts the named empirical or metaphysical premises the compiled statement still
assumes. -/
structure Evidence where
  classification : Classification
  hasLeanStatement : Bool
  buildSucceeded : Bool
  establishesP : Bool
  establishesNegP : Bool
  undischarged : Nat
  deriving DecidableEq, Repr

/-- A successful current build compiles exact `P`. -/
def compiledP (e : Evidence) : Bool := e.buildSucceeded && e.establishesP

/-- A successful current build compiles the exact negation of `P`. -/
def compiledNegP (e : Evidence) : Bool := e.buildSucceeded && e.establishesNegP

/-- The first rule: a `not-formalizable` record that carries no Lean statement. -/
def notFormalizedRule (e : Evidence) : Bool :=
  decide (e.classification = Classification.notFormalizable) && !e.hasLeanStatement

/-- First-match settlement: `not-formalized`, then `conditional`, then `proved`,
then `refuted`, and `open` otherwise. -/
def settle (e : Evidence) : Outcome :=
  if notFormalizedRule e then .notFormalized
  else if compiledP e && decide (0 < e.undischarged) then .conditional
  else if compiledP e then .proved
  else if compiledNegP e then .refuted
  else .open

/-- The public claims an answer can convey about one assertion, from the
bottom claim that conveys nothing about `P` to exact `P` and exact `¬P`. -/
inductive Claim
  | unsettled
  | nonformalJudgment
  | consequentUnderConditions
  | assertP
  | assertNegP
  deriving DecidableEq, Repr

/-- `c.le d` holds when claim `c` commits to at most what claim `d` commits to:
`unsettled` is below everything, the conditional consequent is below exact `P`,
and otherwise only equal claims compare. -/
def Claim.le : Claim → Claim → Bool
  | .unsettled, _ => true
  | .consequentUnderConditions, .assertP => true
  | c, d => decide (c = d)

/-- Formal-grade claims are those that assert something about `P` in the model. -/
def Claim.isFormal : Claim → Bool
  | .consequentUnderConditions | .assertP | .assertNegP => true
  | .unsettled | .nonformalJudgment => false

/-- The maximum permitted public claim of each outcome. -/
def ceiling : Outcome → Claim
  | .proved => .assertP
  | .refuted => .assertNegP
  | .conditional => .consequentUnderConditions
  | .notFormalized => .nonformalJudgment
  | .open => .unsettled

/-- An outcome permits every claim at or below its ceiling. -/
def permits (o : Outcome) (c : Claim) : Bool := c.le (ceiling o)

/-- The ordered rules are exhaustive and single-valued: each outcome is
characterized exactly by the first rule it matches, so no record is left
without an outcome and no record receives two. -/
theorem settle_first_match (e : Evidence) :
    (settle e = .notFormalized ↔ notFormalizedRule e = true) ∧
      (settle e = .conditional ↔
        notFormalizedRule e = false ∧ compiledP e = true ∧ 0 < e.undischarged) ∧
      (settle e = .proved ↔
        notFormalizedRule e = false ∧ compiledP e = true ∧ e.undischarged = 0) ∧
      (settle e = .refuted ↔
        notFormalizedRule e = false ∧ compiledP e = false ∧ compiledNegP e = true) ∧
      (settle e = .open ↔
        notFormalizedRule e = false ∧ compiledP e = false ∧ compiledNegP e = false) := by
  rcases e with ⟨c, h, b, p, q, u⟩
  cases c <;> cases h <;> cases b <;> cases p <;> cases q <;> cases u <;>
    simp [settle, notFormalizedRule, compiledP, compiledNegP]

/-- A failed or unavailable build settles nothing: the record is `open`, or it was
`not-formalized` before any build was attempted. -/
theorem failed_build_settles_open_or_not_formalized (e : Evidence)
    (h : e.buildSucceeded = false) :
    settle e = .open ∨ settle e = .notFormalized := by
  rcases e with ⟨c, hs, b, p, q, u⟩
  cases c <;> cases hs <;> cases b <;> cases p <;> cases q <;> cases u <;>
    simp_all [settle, notFormalizedRule, compiledP, compiledNegP]

/-- A failed proof never implies falsity: `refuted` requires a compiled exact
negation. -/
theorem refuted_requires_compiled_negation (e : Evidence)
    (h : settle e = .refuted) : compiledNegP e = true :=
  ((settle_first_match e).2.2.2.1.mp h).2.2

/-- A compiled conditional never discharges its real-world premises: the
`conditional` outcome retains at least one undischarged condition. -/
theorem conditional_retains_undischarged (e : Evidence)
    (h : settle e = .conditional) : 0 < e.undischarged :=
  ((settle_first_match e).2.1.mp h).2.2

/-- Capability failure is not evidence about formalizability: whether a record
settles `not-formalized` depends only on its fixed classification and on whether
a Lean statement exists, never on build success or proof content. -/
theorem not_formalized_independent_of_build (e e' : Evidence)
    (hc : e.classification = e'.classification)
    (hs : e.hasLeanStatement = e'.hasLeanStatement) :
    settle e = .notFormalized ↔ settle e' = .notFormalized := by
  rw [(settle_first_match e).1, (settle_first_match e').1]
  unfold notFormalizedRule
  rw [hc, hs]

/-- The claim order is reflexive. -/
theorem claim_le_refl (c : Claim) : c.le c = true := by
  cases c <;> simp [Claim.le]

/-- The claim order is transitive. -/
theorem claim_le_trans (a b c : Claim) (hab : a.le b = true) (hbc : b.le c = true) :
    a.le c = true := by
  cases a <;> cases b <;> cases c <;> simp_all [Claim.le]

/-- An `open` record permits neither `P` nor its negation nor any conditional
consequent: only the claim that conveys nothing about `P`. -/
theorem open_permits_only_unsettled (c : Claim) :
    permits .open c = true ↔ c = .unsettled := by
  cases c <;> simp [permits, ceiling, Claim.le]

/-- A `conditional` record never permits exact `P`. -/
theorem conditional_never_permits_p : permits .conditional .assertP = false := by
  decide

/-- Only a decisive outcome permits a formal-grade claim. -/
theorem formal_claim_needs_decisive_outcome (o : Outcome) (c : Claim)
    (hc : c.isFormal = true) (h : permits o c = true) :
    o = .proved ∨ o = .refuted ∨ o = .conditional := by
  cases o <;> cases c <;> simp_all [permits, ceiling, Claim.le, Claim.isFormal]

/-- Ceiling soundness: every formal-grade claim the ceiling permits is backed by
one successful current build of the exact statement. -/
theorem formal_claim_requires_successful_build (e : Evidence) (c : Claim)
    (hc : c.isFormal = true) (h : permits (settle e) c = true) :
    e.buildSucceeded = true := by
  have compiledP_build : compiledP e = true → e.buildSucceeded = true :=
    fun hp => ((Bool.and_eq_true _ _).mp hp).1
  have compiledNegP_build : compiledNegP e = true → e.buildSucceeded = true :=
    fun hn => ((Bool.and_eq_true _ _).mp hn).1
  rcases formal_claim_needs_decisive_outcome (settle e) c hc h with ho | ho | ho
  · exact compiledP_build ((settle_first_match e).2.2.1.mp ho).2.1
  · exact compiledNegP_build ((settle_first_match e).2.2.2.1.mp ho).2.2
  · exact compiledP_build ((settle_first_match e).2.1.mp ho).2.1

/-- Exact `P` is permitted only when the successful build compiled `P` with no
undischarged condition. -/
theorem permitted_p_is_unconditionally_compiled (e : Evidence)
    (h : permits (settle e) .assertP = true) :
    compiledP e = true ∧ e.undischarged = 0 := by
  rcases formal_claim_needs_decisive_outcome (settle e) .assertP rfl h with ho | ho | ho
  · exact ((settle_first_match e).2.2.1.mp ho).2
  · rw [ho] at h
    exact absurd h (by decide)
  · rw [ho] at h
    exact absurd h (by decide)

/- A compiled exact statement with a successful build settles `proved`. -/
example : settle ⟨.formalizable, true, true, true, false, 0⟩ = .proved := by
  decide

/- The same claimed proof with a failed build settles `open`, not `proved`. -/
example : settle ⟨.formalizable, true, false, true, false, 0⟩ = .open := by
  decide

/- Two undischarged empirical premises make the compiled statement `conditional`. -/
example : settle ⟨.conditionalEmpirical, true, true, true, false, 2⟩ = .conditional := by
  decide

/- A `not-formalizable` clause without a Lean statement settles `not-formalized`. -/
example : settle ⟨.notFormalizable, false, false, false, false, 0⟩ = .notFormalized := by
  decide

/- A failed build permits no exact `P`, even when a proof text was written. -/
example : permits (settle ⟨.formalizable, true, false, true, false, 0⟩) .assertP = false := by
  decide

#print axioms settle_first_match
#print axioms failed_build_settles_open_or_not_formalized
#print axioms not_formalized_independent_of_build
#print axioms open_permits_only_unsettled
#print axioms formal_claim_requires_successful_build
#print axioms permitted_p_is_unconditionally_compiled

end D5.S3.ConceptDynamics.Answering.AssertionSettlementCeiling
