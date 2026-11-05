import LeanInformationAuditRegTests.SearchReduction.GraphModel
import LeanInformationAuditRegAnalysis.SearchReduction.LookupPruning

/-! Production lookup guards and their proof-hard boundary. Implication bases
are B_T; exact membership independently ranges over protected B0. The model
properties remain universally quantified over arbitrary B_T candidate lists. -/
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


/-- Resource use and the checked outcome of one immutable candidate attempt.
An absent attempt represents a missing index entry or an unloaded candidate. -/
structure LookupCandidateAttempt where
  preparation : Nat
  search : Nat
  outcome : Run

/-- A later checked certificate wins over an earlier unavailable candidate;
an unavailable candidate never contributes a completed negative result. -/
def keepLookupUnknown (failure : Failure) : Run → Run
  | .found => .found
  | _ => .incomplete failure

/-- Both allocations are cumulative within one branch. Candidate order and
attempts are fixed before either resource allocation is applied. -/
def enumerateLookup (preparation search : Nat) : List (Option LookupCandidateAttempt) → Run
  | [] => .exhausted
  | none :: rest => keepLookupUnknown .missing (enumerateLookup preparation search rest)
  | some attempt :: rest =>
    if attempt.preparation ≤ preparation ∧ attempt.search ≤ search then
      match attempt.outcome with
      | .found => .found
      | .exhausted => enumerateLookup (preparation - attempt.preparation)
          (search - attempt.search) rest
      | .incomplete failure => keepLookupUnknown failure
          (enumerateLookup (preparation - attempt.preparation) (search - attempt.search) rest)
    else .incomplete .heartbeat

private theorem keepUnknown_not_exhausted (failure : Failure) (result : Run) :
    keepLookupUnknown failure result ≠ .exhausted := by
  cases result <;> simp [keepLookupUnknown]

private theorem lookup_enumeration_exhausted (attempts : List (Option LookupCandidateAttempt))
    (preparation search : Nat)
    (finished : enumerateLookup preparation search attempts = .exhausted) :
    ∀ slot ∈ attempts, ∃ attempt, slot = some attempt ∧ attempt.outcome = .exhausted := by
  induction attempts generalizing preparation search with
  | nil => simp
  | cons slot rest ih =>
    cases slot with
    | none => exact False.elim (keepUnknown_not_exhausted _ _ finished)
    | some attempt =>
      simp only [enumerateLookup] at finished
      split at finished
      · cases outcome : attempt.outcome with
        | found => simp [outcome] at finished
        | incomplete failure =>
          rw [outcome] at finished
          exact False.elim (keepUnknown_not_exhausted _ _ finished)
        | exhausted =>
          rw [outcome] at finished
          intro slot member
          rcases List.mem_cons.mp member with equal | member
          · exact ⟨attempt, equal, outcome⟩
          · exact ih _ _ finished slot member
      · contradiction

/-- Completed negative enumeration accounts for every member of the complete
primary-index candidate list, including missing/unloaded entries. Otherwise
the result is unknown or an independently checked success; no absent primary
candidate silently becomes NoHit. -/
theorem total_candidate_complete_or_unknown {Candidate : Type*}
    (primaryIndexCandidates : List Candidate)
    (attempt : Candidate → Option LookupCandidateAttempt) (preparation search : Nat) :
    (∃ failure, enumerateLookup preparation search
      (primaryIndexCandidates.map attempt) = .incomplete failure) ∨
    enumerateLookup preparation search (primaryIndexCandidates.map attempt) = .found ∨
    (enumerateLookup preparation search (primaryIndexCandidates.map attempt) = .exhausted ∧
      ∀ candidate ∈ primaryIndexCandidates, ∃ checked,
        attempt candidate = some checked ∧ checked.outcome = .exhausted) := by
  cases result : enumerateLookup preparation search
      (primaryIndexCandidates.map attempt) with
  | found => exact Or.inr (Or.inl rfl)
  | incomplete failure => exact Or.inl ⟨failure, rfl⟩
  | exhausted =>
    refine Or.inr (Or.inr ⟨rfl, ?_⟩)
    intro candidate member
    exact lookup_enumeration_exhausted _ _ _ result (attempt candidate)
      (List.mem_map.mpr ⟨candidate, member, rfl⟩)

private def LookupSettled (result : Run) : Prop := result = .found ∨ result = .exhausted

private theorem keepUnknown_settled (failure : Failure) (result : Run)
    (settled : LookupSettled (keepLookupUnknown failure result)) : result = .found := by
  cases result <;> simp_all [LookupSettled, keepLookupUnknown]

/-- Enlarging either allocation preserves every already certified outcome.
Only unknown results can be resolved by extra resources. The entire ordered
candidate plan is shared, so this is not a change of R or of the basis_T. -/
theorem total_unknown_monotonicity (attempts : List (Option LookupCandidateAttempt))
    (preparation search largerPreparation largerSearch : Nat)
    (preparation_le : preparation ≤ largerPreparation) (search_le : search ≤ largerSearch)
    (settled : enumerateLookup preparation search attempts = .found ∨
      enumerateLookup preparation search attempts = .exhausted) :
    enumerateLookup largerPreparation largerSearch attempts =
      enumerateLookup preparation search attempts := by
  induction attempts generalizing preparation search largerPreparation largerSearch with
  | nil => rfl
  | cons slot rest ih =>
    cases slot with
    | none =>
      have found := keepUnknown_settled .missing _ settled
      have same := ih _ _ _ _ preparation_le search_le (Or.inl found)
      simp only [enumerateLookup, same]
    | some attempt =>
      by_cases fits : attempt.preparation ≤ preparation ∧ attempt.search ≤ search
      · have largerFits : attempt.preparation ≤ largerPreparation ∧ attempt.search ≤ largerSearch :=
          ⟨fits.1.trans preparation_le, fits.2.trans search_le⟩
        simp only [enumerateLookup, ite_eq_left fits] at settled ⊢
        rw [ite_eq_left largerFits]
        have hp := Nat.sub_le_sub_right preparation_le attempt.preparation
        have hs := Nat.sub_le_sub_right search_le attempt.search
        cases outcome : attempt.outcome with
        | found => rfl
        | exhausted =>
          simp only [outcome] at settled ⊢
          exact ih _ _ _ _ hp hs settled
        | incomplete failure =>
          simp only [outcome] at settled ⊢
          have found := keepUnknown_settled failure _ settled
          rw [ih _ _ _ _ hp hs (Or.inl found)]
      · simp [enumerateLookup, fits] at settled



/-- Dependency edges point from a declaration to its prerequisites. A new
certificate adds edges only from the target to its chosen basis_T declarations. -/
def lookupCertificateEdges {Declaration : Type*} (dependency : Declaration → Declaration → Prop)
    (target : Declaration) (candidates_T : Set Declaration) : Declaration → Declaration → Prop :=
  fun origin destination => dependency origin destination ∨
    (origin = target ∧ destination ∈ candidates_T)

private theorem lookup_certificate_path {Declaration : Type*}
    (dependency : Declaration → Declaration → Prop) (target : Declaration)
    (candidates_T : Set Declaration)
    (outside_downstream : ∀ candidate ∈ candidates_T,
      ¬ Relation.ReflTransGen dependency candidate target)
    {origin destination : Declaration}
    (path : Relation.TransGen (lookupCertificateEdges dependency target candidates_T)
      origin destination) :
    Relation.TransGen dependency origin destination ∨
      (Relation.ReflTransGen dependency origin target ∧
        ¬ Relation.ReflTransGen dependency destination target) := by
  induction path with
  | single edge =>
    rcases edge with old | ⟨equal, member⟩
    · exact Or.inl (.single old)
    · subst equal
      exact Or.inr ⟨.refl, outside_downstream _ member⟩
  | @tail middle destination path edge ih =>
    rcases edge with old | ⟨equal, member⟩
    · rcases ih with original | ⟨beforeTarget, safe⟩
      · exact Or.inl (original.tail old)
      · exact Or.inr ⟨beforeTarget, fun returning => safe (returning.head old)⟩
    · rcases ih with original | ⟨_, safe⟩
      · subst equal
        exact Or.inr ⟨original.to_reflTransGen, outside_downstream _ member⟩
      · exact False.elim (safe (equal ▸ Relation.ReflTransGen.refl))

/-- Excluding the target and its downstream origin the candidate scope preserves
acyclicity of the full certificate dependency graph, not only its direct edges. -/
theorem scope_acyclic {Declaration : Type*}
    (dependency : Declaration → Declaration → Prop) (target : Declaration)
    (candidates_T : Set Declaration)
    (baseline_acyclic : ∀ declaration, ¬ Relation.TransGen dependency declaration declaration)
    (outside_downstream : ∀ candidate ∈ candidates_T,
      ¬ Relation.ReflTransGen dependency candidate target) :
    ∀ declaration, ¬ Relation.TransGen (lookupCertificateEdges dependency target candidates_T)
      declaration declaration := by
  intro declaration cycle
  rcases lookup_certificate_path dependency target candidates_T outside_downstream cycle with
    original | ⟨beforeTarget, safe⟩
  · exact baseline_acyclic declaration original
  · exact safe beforeTarget


#print axioms total_candidate_complete_or_unknown
#print axioms total_unknown_monotonicity
#print axioms scope_acyclic

/-- Candidate-local limits reset rather than subtracting the preceding cost. -/
def candidateOutcome (preparation search : Nat) : Option LookupCandidateAttempt → Run
  | none => .incomplete .missing
  | some attempt =>
    if attempt.preparation ≤ preparation ∧ attempt.search ≤ search then attempt.outcome
    else .incomplete .heartbeat

/-- Found has priority over every unknown residual. A negative requires every
member, including unavailable and capped members, to fail normally. -/
noncomputable def perCandidateLookup {Candidate : Type*} (basis_T : List Candidate)
    (attempt : Candidate → Option LookupCandidateAttempt) (preparation search : Nat) : Run := by
  classical
  exact if ∃ candidate ∈ basis_T, candidateOutcome preparation search (attempt candidate) = .found then
    .found
  else if ∀ candidate ∈ basis_T, candidateOutcome preparation search (attempt candidate) = .exhausted then
    .exhausted
  else .incomplete .undecided

theorem perCandidate_found {Candidate : Type*} (basis_T : List Candidate)
    (attempt : Candidate → Option LookupCandidateAttempt) (preparation search : Nat) :
    perCandidateLookup basis_T attempt preparation search = .found ↔
      ∃ candidate ∈ basis_T, candidateOutcome preparation search (attempt candidate) = .found := by
  classical
  unfold perCandidateLookup
  split
  · rename_i found
    exact ⟨fun _ => found, fun _ => rfl⟩
  · rename_i absent
    split <;> constructor
    all_goals intro h
    all_goals first | contradiction | exact False.elim (absent h)

theorem perCandidate_nohit {Candidate : Type*} (basis_T : List Candidate)
    (attempt : Candidate → Option LookupCandidateAttempt) (preparation search : Nat) :
    perCandidateLookup basis_T attempt preparation search = .exhausted ↔
      ∀ candidate ∈ basis_T, candidateOutcome preparation search (attempt candidate) = .exhausted := by
  classical
  constructor
  · intro h
    unfold perCandidateLookup at h
    split at h
    · contradiction
    · split at h
      · assumption
      · contradiction
  · intro h
    have absent : ¬ ∃ candidate ∈ basis_T,
        candidateOutcome preparation search (attempt candidate) = .found := by
      rintro ⟨candidate, member, found⟩
      rw [h candidate member] at found
      contradiction
    rw [perCandidateLookup, if_neg absent, if_pos h]

/-- Arbitrary permutations preserve the full three-valued candidate result. -/
theorem per_candidate_order_invariant {Candidate : Type*} (basis_T reordered : List Candidate)
    (permutation : basis_T.Perm reordered) (attempt : Candidate → Option LookupCandidateAttempt)
    (preparation search : Nat) :
    perCandidateLookup basis_T attempt preparation search =
      perCandidateLookup reordered attempt preparation search := by
  classical
  simp only [perCandidateLookup, permutation.mem_iff]

/-- Enlarging the basis_T preserves certified hits; restricting it preserves
completed negatives. No assumption about declaration order is used. -/
theorem basis_extension_monotone {Candidate : Type*} (basis_T larger : List Candidate)
    (included : ∀ candidate ∈ basis_T, candidate ∈ larger)
    (attempt : Candidate → Option LookupCandidateAttempt) (preparation search : Nat) :
    (perCandidateLookup basis_T attempt preparation search = .found →
      perCandidateLookup larger attempt preparation search = .found) ∧
    (perCandidateLookup larger attempt preparation search = .exhausted →
      perCandidateLookup basis_T attempt preparation search = .exhausted) := by
  constructor
  · intro h
    rcases (perCandidate_found _ _ _ _).mp h with ⟨candidate, member, found⟩
    exact (perCandidate_found _ _ _ _).mpr ⟨candidate, included candidate member, found⟩
  · intro h
    exact (perCandidate_nohit _ _ _ _).mpr fun candidate member =>
      (perCandidate_nohit _ _ _ _).mp h candidate (included candidate member)

/-- A normally failing prefix consumes the complete shared allocation before
the hit is attempted; both candidates_T individually fit the allocation. -/
theorem total_budget_nonmonotone :
    let hit : LookupCandidateAttempt := ⟨0, 1, .found⟩
    let heavy : LookupCandidateAttempt := ⟨0, 1, .exhausted⟩
    enumerateLookup 0 1 [some heavy] = .exhausted ∧
    enumerateLookup 0 1 [some hit] = .found ∧
      enumerateLookup 0 1 [some heavy, some hit] = .incomplete .heartbeat := by
  decide

private theorem candidate_normal_failure (preparation search : Nat)
    (slot : Option LookupCandidateAttempt)
    (normal : candidateOutcome preparation search slot = .exhausted) :
    ∃ checked, slot = some checked ∧ checked.preparation ≤ preparation ∧
      checked.search ≤ search ∧ checked.outcome = .exhausted := by
  cases slot with
  | none => contradiction
  | some checked =>
    simp only [candidateOutcome] at normal
    split at normal
    · rename_i fits
      exact ⟨checked, rfl, fits.1, fits.2, normal⟩
    · contradiction

/-- NoHit is relative to the complete primary-index candidate list. Every
primary-index member needs a loaded attempt and normal failure inside both
candidate-local limits; star-fallback candidates are outside this statement. -/
theorem nohit_requires_complete_uncapped {Candidate : Type*}
    (primaryIndexCandidates : List Candidate)
    (attempt : Candidate → Option LookupCandidateAttempt) (preparation search : Nat)
    (nohit : perCandidateLookup primaryIndexCandidates attempt preparation search = .exhausted) :
    ∀ candidate ∈ primaryIndexCandidates, ∃ checked, attempt candidate = some checked ∧
      checked.preparation ≤ preparation ∧ checked.search ≤ search ∧
      checked.outcome = .exhausted := by
  intro candidate member
  exact candidate_normal_failure _ _ _ ((perCandidate_nohit _ _ _ _).mp nohit candidate member)

theorem cap_overrun_not_nohit {Candidate : Type*}
    (primaryIndexCandidates : List Candidate)
    (attempt : Candidate → Option LookupCandidateAttempt) (preparation search : Nat)
    (candidate : Candidate) (member : candidate ∈ primaryIndexCandidates)
    (checked : LookupCandidateAttempt)
    (loaded : attempt candidate = some checked)
    (capped : preparation < checked.preparation ∨ search < checked.search) :
    perCandidateLookup primaryIndexCandidates attempt preparation search ≠ .exhausted := by
  intro nohit
  rcases nohit_requires_complete_uncapped _ _ _ _ nohit candidate member with
    ⟨other, equal, hp, hs, _⟩
  rw [loaded] at equal
  cases Option.some.inj equal
  omega

/-- Full accounting for the primary-index candidate list: every absent,
failed or capped attempt blocks NoHit but cannot erase a successful
certificate from another primary-index candidate. -/
theorem candidate_complete_or_unknown {Candidate : Type*}
    (primaryIndexCandidates : List Candidate)
    (attempt : Candidate → Option LookupCandidateAttempt) (preparation search : Nat) :
    (∃ failure, perCandidateLookup primaryIndexCandidates attempt preparation search = .incomplete failure) ∨
    perCandidateLookup primaryIndexCandidates attempt preparation search = .found ∨
    (perCandidateLookup primaryIndexCandidates attempt preparation search = .exhausted ∧
      ∀ candidate ∈ primaryIndexCandidates, ∃ checked, attempt candidate = some checked ∧
        checked.preparation ≤ preparation ∧ checked.search ≤ search ∧
        checked.outcome = .exhausted) := by
  cases result : perCandidateLookup primaryIndexCandidates attempt preparation search with
  | incomplete failure => exact Or.inl ⟨failure, rfl⟩
  | found => exact Or.inr (Or.inl rfl)
  | exhausted => exact Or.inr (Or.inr ⟨rfl,
      nohit_requires_complete_uncapped _ _ _ _ result⟩)

private theorem candidate_settled_monotone (slot : Option LookupCandidateAttempt)
    (preparation search largerPreparation largerSearch : Nat)
    (hp : preparation ≤ largerPreparation) (hs : search ≤ largerSearch)
    (settled : candidateOutcome preparation search slot = .found ∨
      candidateOutcome preparation search slot = .exhausted) :
    candidateOutcome largerPreparation largerSearch slot =
      candidateOutcome preparation search slot := by
  cases slot with
  | none => simp [candidateOutcome] at settled
  | some checked =>
    by_cases fits : checked.preparation ≤ preparation ∧ checked.search ≤ search
    · have largerFits := And.intro (fits.1.trans hp) (fits.2.trans hs)
      simp [candidateOutcome, fits, largerFits]
    · simp [candidateOutcome, fits] at settled

/-- Only unknown can change when the two per-candidate allocations grow. -/
theorem unknown_monotonicity {Candidate : Type*} (basis_T : List Candidate)
    (attempt : Candidate → Option LookupCandidateAttempt)
    (preparation search largerPreparation largerSearch : Nat)
    (hp : preparation ≤ largerPreparation) (hs : search ≤ largerSearch)
    (settled : perCandidateLookup basis_T attempt preparation search = .found ∨
      perCandidateLookup basis_T attempt preparation search = .exhausted) :
    perCandidateLookup basis_T attempt largerPreparation largerSearch =
      perCandidateLookup basis_T attempt preparation search := by
  rcases settled with found | nohit
  · rw [found]
    rcases (perCandidate_found _ _ _ _).mp found with ⟨candidate, member, hit⟩
    apply (perCandidate_found _ _ _ _).mpr
    exact ⟨candidate, member, (candidate_settled_monotone _ _ _ _ _ hp hs (Or.inl hit)).trans hit⟩
  · rw [nohit]
    apply (perCandidate_nohit _ _ _ _).mpr
    intro candidate member
    have normal := (perCandidate_nohit _ _ _ _).mp nohit candidate member
    exact (candidate_settled_monotone _ _ _ _ _ hp hs (Or.inr normal)).trans normal

/-- Coverage thresholds are cumulative heartbeats attached to the fixed
candidate stream. Candidates beyond G are represented as unavailable, never
as normal failures. The thresholds are shared when G grows. -/
def coverageAttempt {Candidate : Type*} (threshold : Candidate → Nat) (G : Nat)
    (attempt : Candidate → Option LookupCandidateAttempt) (candidate : Candidate) :
    Option LookupCandidateAttempt :=
  if threshold candidate ≤ G then attempt candidate else none

theorem coverage_monotone_in_G {Candidate : Type*} (basis_T : List Candidate)
    (threshold : Candidate → Nat) (attempt : Candidate → Option LookupCandidateAttempt)
    (preparation search G largerG : Nat) (hg : G ≤ largerG)
    (settled : perCandidateLookup basis_T (coverageAttempt threshold G attempt) preparation search = .found ∨
      perCandidateLookup basis_T (coverageAttempt threshold G attempt) preparation search = .exhausted) :
    perCandidateLookup basis_T (coverageAttempt threshold largerG attempt) preparation search =
      perCandidateLookup basis_T (coverageAttempt threshold G attempt) preparation search := by
  rcases settled with found | nohit
  · rw [found]
    rcases (perCandidate_found _ _ _ _).mp found with ⟨candidate, member, hit⟩
    have covered : threshold candidate ≤ G := by
      by_contra h
      simp [coverageAttempt, h, candidateOutcome] at hit
    apply (perCandidate_found _ _ _ _).mpr
    exact ⟨candidate, member, by simpa [coverageAttempt, covered, covered.trans hg] using hit⟩
  · rw [nohit]
    apply (perCandidate_nohit _ _ _ _).mpr
    intro candidate member
    have normal := (perCandidate_nohit _ _ _ _).mp nohit candidate member
    have covered : threshold candidate ≤ G := by
      by_contra h
      simp [coverageAttempt, h, candidateOutcome] at normal
    simpa [coverageAttempt, covered, covered.trans hg] using normal

/-- A reset runner admits no incoming mutable-cache influence. Query includes
(T, Γ, B0, index version, R version); both budgets are explicit arguments.
The runtime obligation is that its attempt function realizes this reset law. -/
theorem budget_noninterference {Query Cache Candidate : Type*}
    (run : Query → Cache → Candidate → Option LookupCandidateAttempt)
    (reset : Cache → Cache) (initial : Cache) (law : ∀ cache, reset cache = initial)
    (query : Query) (basis_T : List Candidate) (cold warm : Cache) (preparation search : Nat) :
    perCandidateLookup basis_T (run query (reset cold)) preparation search =
      perCandidateLookup basis_T (run query (reset warm)) preparation search ∧
    (∀ candidate, run query initial candidate = none →
      candidateOutcome preparation search (run query initial candidate) = .incomplete .missing) := by
  constructor
  · rw [law cold, law warm]
  · intro candidate missing
    simp [missing, candidateOutcome]

#print axioms per_candidate_order_invariant
#print axioms basis_extension_monotone
#print axioms total_budget_nonmonotone
#print axioms nohit_requires_complete_uncapped
#print axioms cap_overrun_not_nohit
#print axioms candidate_complete_or_unknown
#print axioms unknown_monotonicity
#print axioms coverage_monotone_in_G
#print axioms budget_noninterference

/-- The only data-assignment routes in R: a matching/synthesis site, or the
type of an argument determined by an earlier route. Seeds include proposition
premise unification and instance synthesis, including output parameters. -/
inductive StarDetermined (plan : StarDeterminationPlan) : Nat → Prop
  | seed {i} : i ∈ plan.seeds → StarDetermined plan i
  | dependency {i j} : StarDetermined plan i → (i, j) ∈ plan.dependencies →
      StarDetermined plan j

private theorem star_determined_inside_barrier (plan : StarDeterminationPlan)
    (support : List Nat) (closed : starDeterminationClosed plan support = true)
    {i : Nat} (determined : StarDetermined plan i) : i ∈ support := by
  simp only [starDeterminationClosed, Bool.and_eq_true, List.all_eq_true,
    List.contains_iff_mem, Bool.or_eq_true] at closed
  induction determined with
  | seed member => exact closed.1 _ member
  | @dependency i j determined edge ih =>
    rcases closed.2 (i, j) edge with absent | present
    · have missing : i ∉ support := by simpa using absent
      exact False.elim (missing ih)
    · exact present

/-- A compliant certificate closes every data argument using R's allowed
routes. The target is arbitrary and supplies no extra assignment mechanism. -/
def StarCompliantCertificate (plan : StarDeterminationPlan) {Target : Type*}
    (_target : Target) : Prop :=
  plan.supported = true ∧ ∀ i ∈ plan.required, StarDetermined plan i

/-- The production static predicate rules out a compliant certificate for
every target. The barrier is checked by the predicate itself; no completeness
assumption about the support-computation algorithm is needed. -/
theorem static_star_impossible_no_certificate (plan : StarDeterminationPlan)
    (support : List Nat) (impossible : staticStarImpossible plan support = true)
    {Target : Type*} (target : Target) : ¬ StarCompliantCertificate plan target := by
  intro certificate
  simp only [staticStarImpossible, Bool.or_eq_true, Bool.and_eq_true,
    List.any_eq_true] at impossible
  rcases impossible with unsupported | ⟨closed, i, required, absent⟩
  · simp [certificate.1] at unsupported
  · have inside := star_determined_inside_barrier plan support closed
      (certificate.2 i required)
    have missing : i ∉ support := by simpa using absent
    exact missing inside

#print axioms static_star_impossible_no_certificate

end LeanInformationAudit.Tests.SearchReduction.GraphModel
