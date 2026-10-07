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
