/- GID: D5/S3/Arith/FibonacciAtomic/Observer/ActualExactSupportPruning
   generality: G
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Exact actual-support pruning and complete nominal table representation. -/

import D5.S3.Arith.FibonacciAtomic.Observer.ActualObserverFiniteTable

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.Observer.ActualExactSupportPruning

universe u
open GenealogicalFiberTransport (Source)
open ActualTreeReadoutAcquisition (Address Reply)
open ActualCoarseReadoutHistory (kappa kappa_hist)
open ActualFiniteObserverAbsentElimination
open ActualObserverPairReach
open ActualObserverFiniteTable

variable {E : Type u} [Fintype E]

/-- The literal support contains every actual query; ghost queries are unrestricted. -/
def ActualSupport (Q : Finset Address) (M : Observer E) (U : Source) : Prop :=
  ∀ e h, ActualPrefix M U e h → ∀ q, M.action e = .inl q → q ∈ Q

/-- Keep raw replies and their order, discarding only addresses outside the support. -/
def supportCache (Q : Finset Address) (h : RawHistory) : RawHistory :=
  h.filter (fun a => a.1 ∈ Q)

/-- Queries outside the prescribed support become false halts. -/
def supportAction (Q : Finset Address) : Sum Address Bool → Sum Address Bool
  | .inl q => if q ∈ Q then .inl q else .inr false
  | .inr b => .inr b

/-- Preserve the complete nominal carrier and raw successor table. Absorbing
history semantics makes the new false halts absorb without using those successors. -/
def supportObserver (Q : Finset Address) (M : Observer E) : Observer E where
  e0 := M.e0
  action e := supportAction Q (M.action e)
  transition := M.transition
  decoder e := supportCache Q (M.decoder e)
  decoded_nodup e := by
    exact List.Nodup.sublist (List.Sublist.map Sigma.fst List.filter_sublist)
      (M.decoded_nodup e)

private theorem support_query (Q : Finset Address) (a : Sum Address Bool) (q : Address) :
    supportAction Q a = .inl q ↔ a = .inl q ∧ q ∈ Q := by
  cases a with
  | inr b => simp [supportAction]
  | inl r =>
      by_cases kept : r ∈ Q
      · simp only [supportAction, if_pos kept, Sum.inl.injEq]
        exact ⟨fun equal => ⟨equal, equal ▸ kept⟩, And.left⟩
      · simp only [supportAction, if_neg kept, Sum.inr_ne_inl, false_iff, Sum.inl.injEq]
        rintro ⟨rfl, member⟩
        exact kept member

private theorem support_update (Q : Finset Address) (cache : RawHistory)
    (fixed : supportCache Q cache = cache) (q : Address) (y : Reply) (kept : q ∈ Q) :
    supportCache Q (cacheUpdate cache q y) = cacheUpdate cache q y := by
  unfold cacheUpdate
  split
  · exact fixed
  · simp only [supportCache, List.filter_append, List.filter_cons,
      List.filter_nil, kept, decide_true, ↓reduceIte]
    exact congrArg (· ++ [⟨q, y⟩]) fixed

private theorem old_prefix (Q : Finset Address) (M : Observer E) (U : Source)
    (legal : Legal M U) (supported : ActualSupport Q M U)
    {e : E} {h : RawHistory} (pref : ActualPrefix M U e h) :
    ActualPrefix (supportObserver Q M) U e h ∧ supportCache Q (M.decoder e) = M.decoder e := by
  induction pref with
  | initial =>
      exact ⟨ActualPrefix.initial, by rw [legal.1]; rfl⟩
  | @query e h q prior row ih =>
      have kept := supported e h prior q row
      have newrow : (supportObserver Q M).action e = .inl q :=
        (support_query Q (M.action e) q).mpr ⟨row, kept⟩
      have reply : queryReply ((supportObserver Q M).decoder e) q U =
          queryReply (M.decoder e) q U := congrArg (fun c => queryReply c q U) ih.2
      refine ⟨?_, ?_⟩
      · simpa only [supportObserver, ih.2] using (ActualPrefix.query ih.1 newrow)
      · rw [(legal.2 e h prior).2 q row]
        exact support_update Q (M.decoder e) ih.2 q _ kept

private theorem new_prefix (Q : Finset Address) (M : Observer E) (U : Source)
    (legal : Legal M U) (supported : ActualSupport Q M U)
    {e : E} {h : RawHistory} (pref : ActualPrefix (supportObserver Q M) U e h) :
    ActualPrefix M U e h := by
  induction pref with
  | initial => exact ActualPrefix.initial
  | @query e h q prior row ih =>
      have original := ((support_query Q (M.action e) q).mp row).1
      have fixed := (old_prefix Q M U legal supported ih).2
      have reply : queryReply ((supportObserver Q M).decoder e) q U =
          queryReply (M.decoder e) q U := congrArg (fun c => queryReply c q U) fixed
      simpa only [supportObserver, fixed] using ActualPrefix.query ih original

private theorem support_legal (Q : Finset Address) (M : Observer E) (U : Source)
    (legal : Legal M U) (supported : ActualSupport Q M U) :
    Legal (supportObserver Q M) U := by
  refine ⟨by change supportCache Q (M.decoder M.e0) = []; rw [legal.1]; rfl, ?_⟩
  intro e h pref
  have original := new_prefix Q M U legal supported pref
  have fixed := (old_prefix Q M U legal supported original).2
  have decoder : (supportObserver Q M).decoder e = M.decoder e := fixed
  refine ⟨by rw [decoder]; exact (legal.2 e h original).1, ?_⟩
  intro q row
  have next := ActualPrefix.query pref row
  have nextOld := new_prefix Q M U legal supported next
  have nextFixed := (old_prefix Q M U legal supported nextOld).2
  change supportCache Q (M.decoder _) = _
  rw [nextFixed, decoder]
  exact (legal.2 e h original).2 q ((support_query Q (M.action e) q).mp row).1

private theorem support_run (Q : Finset Address) (M : Observer E) (U : Source)
    (legal : Legal M U) (supported : ActualSupport Q M U)
    {e f : E} {t : RawHistory} {b : Bool} (run : Run M U e t f b)
    {h : RawHistory} (pref : ActualPrefix M U e h) :
    Run (supportObserver Q M) U e t f b := by
  induction run generalizing h with
  | halt row => exact .halt (by simp only [supportObserver, row, supportAction])
  | @query e f q t b row tail ih =>
      have kept := supported e h pref q row
      have newrow : (supportObserver Q M).action e = .inl q :=
        (support_query Q (M.action e) q).mpr ⟨row, kept⟩
      have fixed := (old_prefix Q M U legal supported pref).2
      have reply : queryReply ((supportObserver Q M).decoder e) q U =
          queryReply (M.decoder e) q U := congrArg (fun c => queryReply c q U) fixed
      have next := ih (ActualPrefix.query pref row)
      have rest : Run (supportObserver Q M) U
          ((supportObserver Q M).transition e
            (queryReply ((supportObserver Q M).decoder e) q U)) t f b := by
        simpa only [supportObserver, fixed] using next
      simpa only [reply] using Run.query newrow rest

private theorem support_pair (Q : Finset Address) (M : Observer E)
    (coarse : Function.FactorsThrough (historyAction M) kappa_hist) {e f : E}
    (reached : PairReach (supportObserver Q M) e f) : PairReach M e f := by
  have invariant : pairActionInvariant M :=
    (pairActionInvariant_iff_allHistoryFactorization M).mpr coarse
  induction reached with
  | initial => exact .initial
  | @step e f y z prior equal ih =>
      have same := invariant ih
      cases action : M.action e with
      | inr b =>
          have other : M.action f = .inr b := same.symm.trans action
          simpa only [barStep, supportObserver, action, other, supportAction] using ih
      | inl q =>
          have other : M.action f = .inl q := same.symm.trans action
          by_cases kept : q ∈ Q
          · simpa only [barStep, supportObserver, action, other, supportAction, if_pos kept]
              using (PairReach.step ih equal)
          · simpa only [barStep, supportObserver, action, other, supportAction, if_neg kept]
              using ih

/-- Sourcewise pruning preserves the full actual states, observations and runs;
all-history factorization is retained through the original paired relation. -/
structure SupportPruningContract (N : Nat) (Q : Finset Address) (M : Observer E) : Prop where
  prefixes : ∀ U, Allowed N U → ∀ e h,
    ActualPrefix (supportObserver Q M) U e h ↔ ActualPrefix M U e h
  cache : ∀ U, Allowed N U → ∀ e h, ActualPrefix M U e h →
    (supportObserver Q M).decoder e = M.decoder e
  actions : ∀ U, Allowed N U → ∀ e h, ActualPrefix M U e h →
    (supportObserver Q M).action e = M.action e
  runs : ∀ U, Allowed N U → ∀ t f b, Run M U M.e0 t f b →
    Run (supportObserver Q M) U M.e0 t f b
  admissible : Admissible N (supportObserver Q M)

/-- Every admissible competitor can be pruned to its actual literal support
without deleting any nominal configuration or changing any actual state visit. -/
theorem support_pruning_contract (N : Nat) (Q : Finset Address) (M : Observer E)
    (admissible : Admissible N M)
    (supported : ∀ U, Allowed N U → ActualSupport Q M U) :
    SupportPruningContract N Q M := by
  have legal U allowed := support_legal Q M U (admissible.legal U allowed) (supported U allowed)
  have runs U (allowed : Allowed N U) {e f : E} {t : RawHistory} {b : Bool}
      (run : Run M U e t f b) {h : RawHistory} (pref : ActualPrefix M U e h) :=
    support_run Q M U (admissible.legal U allowed) (supported U allowed) run pref
  refine ⟨?_, ?_, ?_, ?_, ⟨admissible.budget_pos, legal, ?_, ?_⟩⟩
  · intro U allowed e h
    exact ⟨new_prefix Q M U (admissible.legal U allowed) (supported U allowed),
      fun pref => (old_prefix Q M U (admissible.legal U allowed) (supported U allowed) pref).1⟩
  · intro U allowed e h pref
    exact (old_prefix Q M U (admissible.legal U allowed) (supported U allowed) pref).2
  · intro U allowed e h pref
    change supportAction Q (M.action e) = M.action e
    cases row : M.action e with
    | inr b => rfl
    | inl q => simp only [supportAction, if_pos (supported U allowed e h pref q row)]
  · intro U allowed t f b run
    exact runs U allowed run ActualPrefix.initial
  · intro U allowed
    obtain ⟨t, f, b, run, correct⟩ := admissible.correct U allowed
    exact ⟨t, f, b, runs U allowed run ActualPrefix.initial, correct⟩
  · apply (pairActionInvariant_iff_allHistoryFactorization _).mp
    intro e f reached
    have old := support_pair Q M admissible.coarse reached
    exact congrArg (supportAction Q)
      (((pairActionInvariant_iff_allHistoryFactorization M).mpr admissible.coarse) old)

/-- A packing envelope for a finite literal support, independent of the source budget. -/
def supportWidth (Q : Finset Address) : Nat := 1 + Q.sup List.length

/-- Full nominal tables cover the pruned observer, at the unchanged cardinality.
The envelope is only a representation bound, not a restriction on source size. -/
private theorem support_table_coverage (Q : Finset Address) (M : Observer E) :
    ∃ (positive : 0 < Fintype.card E) (r : E ≃ Fin (Fintype.card E))
      (T : NativeTable (supportWidth Q) (Fintype.card E)),
      tableObserver positive T = relabel (supportObserver Q M) r ∧
      RepresentationContract (supportWidth Q) (supportObserver Q M) positive r T ∧
      (∀ e q, (tableObserver positive T).action e = .inl q → q ∈ Q) ∧
      (∀ e a, a ∈ (tableObserver positive T).decoder e → a.1 ∈ Q) := by
  have bound q (member : q ∈ Q) : q ∈ Q_N (supportWidth Q) := by
    have le := Finset.le_sup (f := List.length) member
    simpa only [Q_N, Set.mem_ofPred_eq, supportWidth, Nat.add_sub_cancel_left] using le
  have requests e q (row : (supportObserver Q M).action e = .inl q) : q ∈ Q :=
    ((support_query Q (M.action e) q).mp row).2
  have caches e a (member : a ∈ (supportObserver Q M).decoder e) : a.1 ∈ Q := by
    exact of_decide_eq_true (List.mem_filter.mp member).2
  obtain ⟨positive, r, T, initial, table⟩ := bounded_table_representation
    (supportWidth Q) (supportObserver Q M) (fun e q row => bound q (requests e q row))
    (fun e a member => bound a.1 (caches e a member))
  have contract := representation_contract (supportWidth Q) (supportObserver Q M)
    positive r T initial table
  refine ⟨positive, r, T, table, contract, ?_, ?_⟩
  · intro e q row
    have actions := contract.actions (r.symm e)
    simp only [Equiv.apply_symm_apply] at actions
    exact requests (r.symm e) q (actions.symm.trans row)
  · intro e a member
    have decoded := contract.caches (r.symm e)
    simp only [Equiv.apply_symm_apply] at decoded
    rw [decoded] at member
    exact caches (r.symm e) a member

/-- The exact finite literal support of all prescribed terminal traces. -/
noncomputable def prescribedSupport (N : Nat) (π : ActualTreeReadoutAcquisition.Strategy) :
    Finset Address :=
  (ActualObserverAbsorbingNormalization.allowedSources N).biUnion
    (fun U => ActualTreeReadoutAcquisition.paid (ActualTreeReadoutAcquisition.terminal π U).1)

/-- Every allowed input has the prescribed raw trace and terminal bit.
This contract does not identify all counterfactual behavior or prescribe phase labels. -/
def ExactTraces (N : Nat) (π : ActualTreeReadoutAcquisition.Strategy) (M : Observer E) : Prop :=
  ∀ U, Allowed N U → ∃ f, Run M U M.e0
    (ActualTreeReadoutAcquisition.terminal π U).1 f (ActualTreeReadoutAcquisition.terminal π U).2

theorem prefix_run_tail (M : Observer E) (U : Source)
    {e : E} {h : RawHistory} (pref : ActualPrefix M U e h)
    {t : RawHistory} {f : E} {b : Bool} (run : Run M U M.e0 t f b) :
    ∃ s, Run M U e s f b ∧ h ++ s = t := by
  induction pref with
  | initial => exact ⟨t, run, rfl⟩
  | @query e h q prior row ih =>
      obtain ⟨s, rest, equal⟩ := ih
      cases rest with
      | halt stop => simp only [row, Sum.inl_ne_inr] at stop
      | @query _ f r tail b other next =>
          have qr : q = r := Sum.inl.inj (row.symm.trans other)
          subst r
          exact ⟨tail, next, by simpa only [List.append_assoc, List.singleton_append] using equal⟩

private theorem prescribed_actual_support (N : Nat)
    (π : ActualTreeReadoutAcquisition.Strategy) (M : Observer E)
    (exact : ExactTraces N π M) (U : Source) (allowed : Allowed N U) :
    ActualSupport (prescribedSupport N π) M U := by
  intro e h pref q row
  obtain ⟨f, run⟩ := exact U allowed
  obtain ⟨s, rest, equal⟩ := prefix_run_tail M U pref run
  have member : q ∈ ActualTreeReadoutAcquisition.paid
      (ActualTreeReadoutAcquisition.terminal π U).1 := by
    cases rest with
    | halt stop => simp only [row, Sum.inl_ne_inr] at stop
    | @query _ f r tail b other next =>
        have qr : q = r := Sum.inl.inj (row.symm.trans other)
        subst r
        rw [← equal]
        apply List.mem_toFinset.mpr
        apply List.mem_map.mpr
        exact ⟨⟨q, queryReply (M.decoder e) q U⟩,
          List.mem_append_right _ List.mem_cons_self, rfl⟩
  exact Finset.mem_biUnion.mpr ⟨U,
    (ActualObserverAbsorbingNormalization.allowedSources_exact N U).mpr allowed, member⟩

/-- Every exact competitor is represented at its unchanged full nominal size
using Qπ-only actions and caches. Source budget N remains separate from the
packing envelope. Prefix states transport by a bijection, preserving any
additional state observation under the same bijection. -/
theorem exact_competitor_table_coverage (N : Nat)
    (π : ActualTreeReadoutAcquisition.Strategy) (M : Observer E)
    (admissible : Admissible N M) (exact : ExactTraces N π M) :
    ∃ (positive : 0 < Fintype.card E) (r : E ≃ Fin (Fintype.card E))
      (T : NativeTable (supportWidth (prescribedSupport N π)) (Fintype.card E)),
      Admissible N (tableObserver positive T) ∧ ExactTraces N π (tableObserver positive T) ∧
      (∀ U, Allowed N U → ∀ e h,
        ActualPrefix (tableObserver positive T) U (r e) h ↔ ActualPrefix M U e h) ∧
      (∀ U, Allowed N U → ∀ e h, ActualPrefix M U e h →
        (tableObserver positive T).decoder (r e) = M.decoder e ∧
        (tableObserver positive T).action (r e) = M.action e) ∧
      (∀ e q, (tableObserver positive T).action e = .inl q → q ∈ prescribedSupport N π) ∧
      (∀ e a, a ∈ (tableObserver positive T).decoder e → a.1 ∈ prescribedSupport N π) := by
  let Q := prescribedSupport N π
  have pruning := support_pruning_contract N Q M admissible
    (prescribed_actual_support N π M exact)
  obtain ⟨positive, r, T, table, representation, requests, caches⟩ := support_table_coverage Q M
  refine ⟨positive, r, T, ?_, ?_, ?_, ?_, requests, caches⟩
  · rw [table]
    exact relabel_admissible N _ r pruning.admissible
  · intro U allowed
    obtain ⟨f, run⟩ := exact U allowed
    refine ⟨r f, ?_⟩
    have newrun := (representation.runs U M.e0 _ f _).mpr (pruning.runs U allowed _ _ _ run)
    have initial : r M.e0 = (tableObserver positive T).e0 := representation.initial
    rw [initial] at newrun
    exact newrun
  · intro U allowed e h
    exact (representation.prefixes U e h).trans (pruning.prefixes U allowed e h)
  · intro U allowed e h pref
    exact ⟨(representation.caches e).trans (pruning.cache U allowed e h pref),
      (representation.actions e).trans (pruning.actions U allowed e h pref)⟩

end D5.S3.Arith.FibonacciAtomic.Observer.ActualExactSupportPruning
