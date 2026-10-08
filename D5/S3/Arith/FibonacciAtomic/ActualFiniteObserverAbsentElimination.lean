/- GID: D5/S3/Arith/FibonacciAtomic/ActualFiniteObserverAbsentElimination
   generality: G
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Complete nominal observers and native bounded-source raw absence. -/

import D5.S3.Arith.FibonacciAtomic.ActualLeafHistoryRigidity
import D5.S3.Arith.FibonacciAtomic.ActualCoarseReadoutHistory

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.ActualFiniteObserverAbsentElimination

universe u

open GenealogicalFiberTransport (Source)
open ActualTreeReadoutAcquisition (Address Reply readout Positive)
open ActualLeafHistoryRigidity (subtree actual_address_geometry)
open ActualCoarseReadoutHistory (kappa_hist)
open D5.S3.ConceptDynamics.Experiment.PassivePolicyNormalization (Hist)

/-- Chronological literal-address reports, retaining raw replies and repetitions. -/
abbrev RawHistory := Hist (fun _ : Address => Reply)

/-- The original bounded source domain; native sources are always nonempty. -/
def Allowed (N : Nat) (U : Source) : Prop := U.length ≤ N

/-- Bounded actual-node addresses. Original query permission remains unrestricted. -/
def Q_N (N : Nat) : Set Address := {q | q.length ≤ N - 1}

/-- Truth refers to the same immutable original source at every cached address. -/
def CacheTruth (cache : RawHistory) (U : Source) : Prop :=
  ∀ a ∈ cache, a.2 = readout a.1 U

/-- An exact hit supplies its stored raw reply; only a miss reads the source. -/
def queryReply (cache : RawHistory) (q : Address) (U : Source) : Reply :=
  match cache.find? (fun a => a.1 == q) with
  | some a => a.2
  | none => readout q U

/-- The ordered first-occurrence update, with no inferred or overwritten entry. -/
def cacheUpdate (cache : RawHistory) (q : Address) (y : Reply) : RawHistory :=
  if q ∈ cache.map Sigma.fst then cache else cache ++ [⟨q, y⟩]

/-- Every nominal row remains present. The initial row witnesses nonemptiness.
The only dynamic storage is this finite carrier and its decoded raw cache. -/
structure Observer (E : Type u) [Fintype E] where
  e0 : E
  action : E → Sum Address Bool
  transition : E → Reply → E
  decoder : E → RawHistory
  decoded_nodup : ∀ e, ((decoder e).map Sigma.fst).Nodup

variable {E : Type u} [Fintype E]

/-- Counterfactual response transitions absorb at every halt row. -/
def barStep (M : Observer E) (e : E) (y : Reply) : E :=
  match M.action e with
  | .inl _ => M.transition e y
  | .inr _ => e

/-- Raw response words act on arbitrary nominal starting rows. -/
def responseState (M : Observer E) (e : E) (word : List Reply) : E :=
  word.foldl (barStep M) e

/-- Reported address labels are ignored by the total counterfactual extension. -/
def historyState (M : Observer E) (h : RawHistory) : E :=
  responseState M M.e0 (h.map Sigma.snd)

/-- The last absorbing row supplies the action on every finite history. -/
def historyAction (M : Observer E) (h : RawHistory) : Sum Address Bool :=
  M.action (historyState M h)

/-- Actual finite prefixes use the current row's literal query and decoded cache.
The history is an external record and is never an argument to the controller. -/
inductive ActualPrefix (M : Observer E) (U : Source) : E → RawHistory → Prop
  | initial : ActualPrefix M U M.e0 []
  | query {e : E} {h : RawHistory} {q : Address}
      (prior : ActualPrefix M U e h) (row : M.action e = .inl q) :
      ActualPrefix M U (M.transition e (queryReply (M.decoder e) q U))
        (h ++ [⟨q, queryReply (M.decoder e) q U⟩])

/-- Sourcewise finite execution, including every repeat and cache hit.
This relation supplies no uniform fuel or extra runtime state. -/
inductive Run (M : Observer E) (U : Source) :
    E → RawHistory → E → Bool → Prop
  | halt {e : E} {b : Bool} (row : M.action e = .inr b) :
      Run M U e [] e b
  | query {e f : E} {q : Address} {t : RawHistory} {b : Bool}
      (row : M.action e = .inl q)
      (tail : Run M U (M.transition e (queryReply (M.decoder e) q U)) t f b) :
      Run M U e (⟨q, queryReply (M.decoder e) q U⟩ :: t) f b

/-- Cache truth and the exact update law are premises only at actual prefixes.
All nominal rows retain their separate address-Nodup obligation. -/
def Legal (M : Observer E) (U : Source) : Prop :=
  M.decoder M.e0 = [] ∧
  ∀ (e : E) (h : RawHistory), ActualPrefix M U e h →
    CacheTruth (M.decoder e) U ∧
    ∀ q : Address, M.action e = .inl q →
      M.decoder (M.transition e (queryReply (M.decoder e) q U)) =
        cacheUpdate (M.decoder e) q (queryReply (M.decoder e) q U)

/-- The original complete bounded observer contract. Correct finite execution is
sourcewise; coarse action factorization quantifies over all finite histories. -/
structure Admissible (N : Nat) (M : Observer E) : Prop where
  budget_pos : 1 ≤ N
  legal : ∀ U : Source, Allowed N U → Legal M U
  correct : ∀ U : Source, Allowed N U →
    ∃ (t : RawHistory) (f : E) (b : Bool),
      Run M U M.e0 t f b ∧ (b = true ↔ Positive U)
  coarse : Function.FactorsThrough (historyAction M) kappa_hist

private theorem queryReply_eq_readout (cache : RawHistory) (U : Source)
    (truth : CacheTruth cache U) (q : Address) :
    queryReply cache q U = readout q U := by
  unfold queryReply
  cases hit : cache.find? (fun a => a.1 == q) with
  | none => rfl
  | some a =>
    have address : a.1 = q := by simpa using List.find?_some hit
    simpa only [address] using truth a (List.mem_of_find?_eq_some hit)

/-- Actual chronological prefixes decode to their exact first-occurrence replay,
and their raw replies agree with the same source. Their rows are the absorbing
response folds even though the controller never receives the external trace. -/
theorem actualPrefix_semantics (M : Observer E) (U : Source) (legal : Legal M U)
    {e : E} {h : RawHistory} (pref : ActualPrefix M U e h) :
    historyState M h = e ∧
    M.decoder e = h.foldl (fun cache a => cacheUpdate cache a.1 a.2) [] ∧
    CacheTruth h U := by
  induction pref with
  | initial =>
    exact ⟨rfl, legal.1, by simp [CacheTruth]⟩
  | @query e h q prior row ih =>
    have at_prefix := legal.2 e h prior
    refine ⟨?_, ?_, ?_⟩
    · simp only [historyState, responseState, List.map_append, List.map_cons,
        List.map_nil, List.foldl_append, List.foldl_cons, List.foldl_nil]
      change barStep M (historyState M h) (queryReply (M.decoder e) q U) = _
      rw [ih.1]
      simp only [barStep, row]
    · rw [at_prefix.2 q row, ih.2.1]
      simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
    · intro a member
      rcases List.mem_append.mp member with member | member
      · exact ih.2.2 a member
      · obtain rfl := List.mem_singleton.mp member
        exact queryReply_eq_readout (M.decoder e) U at_prefix.1 q

/-- A head/tail execution extends any actual chronological prefix to its final
halt row, retaining every report and repetition in their original order. -/
theorem run_from_actualPrefix (M : Observer E) (U : Source)
    {e f : E} {t h : RawHistory} {b : Bool}
    (run : Run M U e t f b) (pref : ActualPrefix M U e h) :
    ActualPrefix M U f (h ++ t) ∧ M.action f = .inr b := by
  induction run generalizing h with
  | halt row => exact ⟨by simpa only [List.append_nil] using pref, row⟩
  | query row tail ih =>
    have extended := ih (ActualPrefix.query pref row)
    simpa only [List.append_assoc, List.singleton_append] using extended

/-- The immutable source and fixed observer determine the entire finite trace,
final nominal row and output bit from any given starting row. -/
theorem run_deterministic (M : Observer E) (U : Source)
    {e f g : E} {t s : RawHistory} {b c : Bool}
    (left : Run M U e t f b) (right : Run M U e s g c) :
    t = s ∧ f = g ∧ b = c := by
  induction left generalizing s g c with
  | halt row =>
    cases right with
    | halt other =>
      have bits := row.symm.trans other
      exact ⟨rfl, rfl, Sum.inr.inj bits⟩
    | query other tail => simp only [row, Sum.inr_ne_inl] at other
  | @query e f q t b row tail ih =>
    cases right with
    | halt other => simp only [row, Sum.inl_ne_inr] at other
    | @query _ g r s c other rest =>
      have queries : q = r := Sum.inl.inj (row.symm.trans other)
      subst r
      obtain ⟨trace, final, bit⟩ := ih rest
      exact ⟨congrArg (List.cons _) trace, final, bit⟩

/-- Every run from the original initial row of an admissible observer realizes
the actual-prefix and absorbing-fold semantics, has the exact ordered cache,
and returns the correct bit for the same original allowed source. -/
theorem admissible_run_contract (N : Nat) (M : Observer E)
    (admissible : Admissible N M) (U : Source) (allowed : Allowed N U)
    {t : RawHistory} {f : E} {b : Bool} (run : Run M U M.e0 t f b) :
    ActualPrefix M U f t ∧ historyState M t = f ∧
    M.action f = .inr b ∧ historyAction M t = .inr b ∧
    M.decoder f = t.foldl (fun cache a => cacheUpdate cache a.1 a.2) [] ∧
    CacheTruth (M.decoder f) U ∧ CacheTruth t U ∧ (b = true ↔ Positive U) := by
  obtain ⟨pref, halt⟩ := run_from_actualPrefix M U run ActualPrefix.initial
  simp only [List.nil_append] at pref
  have legal := admissible.legal U allowed
  obtain ⟨state, cache, reports⟩ := actualPrefix_semantics M U legal pref
  obtain ⟨s, g, c, correctRun, correct⟩ := admissible.correct U allowed
  have bit := (run_deterministic M U run correctRun).2.2
  refine ⟨pref, state, halt, ?_, cache, (legal.2 f t pref).1, reports, ?_⟩
  · simpa only [historyAction, state] using halt
  · simpa only [bit] using correct

/-- Every edge of a native subtree path leaves a nonempty sibling behind. -/
theorem subtree_leaf_count (U : Source) (q : Address) (T : Source)
    (present : subtree q U = some T) : q.length + T.length ≤ U.length := by
  induction U generalizing q T with
  | of b =>
    cases q with
    | nil =>
      simp only [subtree, Option.some.injEq] at present
      subst T
      simp
    | cons d q => simp [subtree] at present
  | mul L R ihL ihR =>
    cases q with
    | nil =>
      simp only [subtree, Option.some.injEq] at present
      subst T
      simp
    | cons d q =>
      cases d with
      | false =>
        change subtree q L = some T at present
        have inner := ihL q T present
        have sibling := R.length_pos
        simp only [List.length_cons, FreeMagma.length]
        omega
      | true =>
        change subtree q R = some T at present
        have inner := ihR q T present
        have sibling := L.length_pos
        simp only [List.length_cons, FreeMagma.length]
        omega

/-- Outside the native node budget, both source reads and truthful cached hits
return raw absent. The stored-hit clause retains the original four-reply value. -/
theorem outside_Q_N_absent (N : Nat) (U : Source) (allowed : Allowed N U)
    (q : Address) (outside : q ∉ Q_N N) :
    readout q U = .absent ∧
    ∀ (cache : RawHistory), CacheTruth cache U →
      queryReply cache q U = .absent ∧
      ∀ a ∈ cache, a.1 = q → a.2 = .absent := by
  have missing : subtree q U = none := by
    cases at_q : subtree q U with
    | none => rfl
    | some T =>
      have bound := subtree_leaf_count U q T at_q
      have positive := T.length_pos
      change U.length ≤ N at allowed
      change ¬ q.length ≤ N - 1 at outside
      omega
  have raw : readout q U = .absent := by
    have at_empty := actual_address_geometry.2.2.2.2.2.2.2.2.2.2.2.2.2.1 q [] U
    simpa only [List.append_nil, missing] using at_empty
  refine ⟨raw, ?_⟩
  intro cache truth
  have hit_absent : ∀ a ∈ cache, a.1 = q → a.2 = .absent := by
    intro a member address
    simpa only [address, raw] using truth a member
  refine ⟨?_, hit_absent⟩
  unfold queryReply
  cases hit : cache.find? (fun a => a.1 == q) with
  | none => exact raw
  | some a =>
    have address : a.1 = q := by simpa using List.find?_some hit
    exact hit_absent a (List.mem_of_find?_eq_some hit) address

end D5.S3.Arith.FibonacciAtomic.ActualFiniteObserverAbsentElimination
