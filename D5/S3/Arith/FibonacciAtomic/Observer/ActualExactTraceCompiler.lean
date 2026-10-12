/- GID: D5/S3/Arith/FibonacciAtomic/Observer/ActualExactTraceCompiler
   generality: G
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Chronological first-occurrence cache projection for repeated logical histories. -/

import D5.S3.Arith.FibonacciAtomic.ActualCoarseReadoutCompletion
import D5.S3.Arith.FibonacciAtomic.ActualFiniteObserverAbsentElimination
import D5.S3.Arith.FibonacciAtomic.Observer.ActualAcquisitionCacheFiber
import D5.S3.Arith.FibonacciAtomic.Observer.ActualObserverAbsorbingNormalization
import D5.S3.Arith.FibonacciAtomic.Observer.ActualObserverPairReach

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.Observer.ActualExactTraceCompiler

open GenealogicalFiberTransport (Source)
open ActualTreeReadoutAcquisition (Address Reply readout)
open ActualCoarseReadoutHistory (kappa kappa_hist)
open ActualFiniteObserverAbsentElimination
  (RawHistory cacheUpdate Allowed Observer ActualPrefix queryReply CacheTruth
    queryReply_eq_readout)
open ActualAcquisitionCacheFiber
  (CompatCache decode decode_injective decode_projection decode_pack decode_addresses pack noneCount
    compatible_cache_card)
open ActualTreeReadoutAcquisition (Strategy terminal)
open ActualObserverAbsorbingNormalization (allowedSources allowedSources_exact
  allowedSources_nonempty)
open D5.S3.ConceptDynamics.Experiment.PassivePolicyNormalization (execute execute_transfer)

abbrev CoarseHistory := ActualAcquisitionCacheFiber.CoarseHistory

/-- The first-occurrence update on coarse symbols.  A repeated logical request
keeps its original coarse response, exactly as `cacheUpdate` keeps its raw
response. -/
def coarseCacheUpdate (cache : CoarseHistory) (q : Address)
    (z : Option Bool) : CoarseHistory :=
  if q ∈ cache.map Sigma.fst then cache else cache ++ [⟨q, z⟩]

/-- Fold the raw first-occurrence cache in chronological request order. -/
def firstRaw : RawHistory → RawHistory :=
  List.foldl (fun cache a => cacheUpdate cache a.1 a.2) []

/-- Fold the coarse first-occurrence cache in chronological logical order. -/
def firstCoarse : CoarseHistory → CoarseHistory :=
  List.foldl (fun cache a => coarseCacheUpdate cache a.1 a.2) []

private theorem kappa_cacheUpdate (cache : RawHistory) (q : Address) (y : Reply) :
    kappa_hist (cacheUpdate cache q y) =
      coarseCacheUpdate (kappa_hist cache) q (kappa y) := by
  classical
  have addresses : q ∈ cache.map Sigma.fst ↔
      q ∈ (kappa_hist cache).map Sigma.fst := by
    simp only [kappa_hist, List.map_map, Function.comp_def]
  unfold cacheUpdate coarseCacheUpdate
  split <;> split <;> simp_all [kappa_hist, List.map_append]

private theorem fold_projection (cache : RawHistory) (g : CoarseHistory)
    (projection : kappa_hist cache = g) (h : RawHistory) :
    kappa_hist (h.foldl (fun cache a => cacheUpdate cache a.1 a.2) cache) =
      (kappa_hist h).foldl
        (fun cache a => coarseCacheUpdate cache a.1 a.2) g := by
  induction h generalizing cache g with
  | nil => simpa [kappa_hist] using projection
  | cons a h ih =>
      simp only [List.foldl_cons]
      apply ih
      rw [kappa_cacheUpdate, projection]

private theorem firstRaw_projection (h : RawHistory) :
    kappa_hist (firstRaw h) = firstCoarse (kappa_hist h) := by
  exact fold_projection [] [] rfl h

private theorem firstRaw_append_single (h : RawHistory) (a : Sigma (fun _ : Address => Reply)) :
    firstRaw (h ++ [a]) = cacheUpdate (firstRaw h) a.1 a.2 := by
  simp only [firstRaw, List.foldl_append, List.foldl_cons, List.foldl_nil]

private theorem firstCoarse_append_single (g : CoarseHistory)
    (a : Sigma (fun _ : Address => Option Bool)) :
    firstCoarse (g ++ [a]) = coarseCacheUpdate (firstCoarse g) a.1 a.2 := by
  simp only [firstCoarse, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- The finite compiler carrier keeps the full logical history as control while
indexing its raw-cache fiber by the chronological first-occurrence history. -/
abbrev ExactIndex (G : Finset CoarseHistory) := {g : CoarseHistory // g ∈ G}
abbrev ExactRow (G : Finset CoarseHistory) :=
  Sigma (fun i : ExactIndex G => CompatCache (firstCoarse i.1))
abbrev ExactState (G : Finset CoarseHistory) := Sum (ExactRow G) Unit

noncomputable instance exactStateFintype (G : Finset CoarseHistory) :
    Fintype (ExactState G) := by
  dsimp [ExactState, ExactRow, ExactIndex]
  infer_instance

noncomputable def exactStateCard (G : Finset CoarseHistory) : Nat :=
  1 + ∑ g ∈ G, 2 ^ noneCount (firstCoarse g)

private theorem exactState_card (G : Finset CoarseHistory) :
    Fintype.card (ExactState G) = exactStateCard G := by
  classical
  simp only [ExactState, ExactRow, ExactIndex, Fintype.card_sum, Fintype.card_unit,
    Fintype.card_sigma, compatible_cache_card, exactStateCard]
  rw [← Finset.sum_coe_sort G (fun g => 2 ^ noneCount (firstCoarse g))]
  exact Nat.add_comm _ _

private theorem coarse_update_nodup (cache : CoarseHistory)
    (nodup : (cache.map Sigma.fst).Nodup) (q : Address) (z : Option Bool) :
    ((coarseCacheUpdate cache q z).map Sigma.fst).Nodup := by
  classical
  unfold coarseCacheUpdate
  split
  · exact nodup
  · rename_i fresh
    simp only [List.map_append, List.map_cons, List.map_nil]
    apply List.nodup_append.mpr
    refine ⟨nodup, by simp, ?_⟩
    intro a ha b hb equal
    have bq : b = q := List.mem_singleton.mp hb
    have aq : a = q := equal.trans bq
    exact fresh (aq ▸ ha)

private theorem firstCoarse_nodup_fold (cache : CoarseHistory)
    (nodup : (cache.map Sigma.fst).Nodup) (g : CoarseHistory) :
    ((g.foldl (fun cache a => coarseCacheUpdate cache a.1 a.2) cache).map Sigma.fst).Nodup := by
  induction g generalizing cache with
  | nil => exact nodup
  | cons a g ih =>
      simp only [List.foldl_cons]
      exact ih (coarseCacheUpdate cache a.1 a.2)
        (coarse_update_nodup cache nodup a.1 a.2)

private theorem firstCoarse_nodup (g : CoarseHistory) :
    ((firstCoarse g).map Sigma.fst).Nodup := by
  exact firstCoarse_nodup_fold [] (by simp) g

/-- The raw decoder of a compiler row is the compatible first-occurrence cache
installed at its full logical control history. -/
noncomputable def exactRowDecoder {G : Finset CoarseHistory} (r : ExactRow G) : RawHistory :=
  decode (firstCoarse r.1.1) r.2

private theorem exactRowDecoder_projection {G : Finset CoarseHistory} (r : ExactRow G) :
    kappa_hist (exactRowDecoder r) = firstCoarse r.1.1 := by
  exact decode_projection _ _

/-- Extend a row by one logical response. The membership guard concerns the full
logical history; the cache fiber is indexed only by its first-occurrence fold. -/
noncomputable def exactAppendRow {G : Finset CoarseHistory} (r : ExactRow G)
    (q : Address) (y : Reply)
    (member : r.1.1 ++ [⟨q, kappa y⟩] ∈ G) : ExactRow G := by
  let g' := r.1.1 ++ [⟨q, kappa y⟩]
  have projection :
      kappa_hist (cacheUpdate (exactRowDecoder r) q y) = firstCoarse g' := by
    rw [kappa_cacheUpdate, exactRowDecoder_projection]
    exact (firstCoarse_append_single r.1.1 ⟨q, kappa y⟩).symm
  exact ⟨⟨g', member⟩, pack (firstCoarse g')
    (cacheUpdate (exactRowDecoder r) q y) projection⟩

noncomputable def exactAction {G : Finset CoarseHistory}
    (policy : CoarseHistory → Sum Address Bool) : ExactState G → Sum Address Bool
  | .inl r => policy r.1.1
  | .inr _ => .inr false

noncomputable def exactTransition {G : Finset CoarseHistory}
    (policy : CoarseHistory → Sum Address Bool) : ExactState G → Reply → ExactState G
  | .inr u, _ => .inr u
  | .inl r, y =>
      match policy r.1.1 with
      | .inr _ => .inl r
      | .inl q =>
          let g' := r.1.1 ++ [⟨q, kappa y⟩]
          if member : g' ∈ G then .inl (exactAppendRow r q y member) else .inr ()

private theorem exactTransition_projection {G : Finset CoarseHistory}
    (r : ExactRow G)
    (q : Address) (y : Reply) (member : r.1.1 ++ [⟨q, kappa y⟩] ∈ G) :
    exactRowDecoder (exactAppendRow r q y member) =
      cacheUpdate (exactRowDecoder r) q y := by
  simp only [exactRowDecoder, exactAppendRow]
  exact decode_pack _ _ _

/-- All coarse prefixes of the original terminal runs. Repeated logical
requests remain in the control history; only their installed cache fiber is
first-occurrence indexed. -/
noncomputable def strategyPrefixes (N : Nat) (π : Strategy) : Finset CoarseHistory :=
  (allowedSources N).biUnion (fun U =>
    (List.inits (kappa_hist (terminal π U).1)).toFinset)

private theorem strategyPrefixes_nonempty (N : Nat) (π : Strategy) (positive : 1 ≤ N) :
    [] ∈ strategyPrefixes N π := by
  obtain ⟨U, member⟩ := allowedSources_nonempty N positive
  refine Finset.mem_biUnion.mpr ⟨U, member, ?_⟩
  exact List.mem_toFinset.mpr ((List.mem_inits _ _).mpr List.nil_prefix)

theorem strategy_prefix_mem (N : Nat) (π : Strategy) {U : Source}
    (allowed : Allowed N U) {h : RawHistory}
    (pre : h.IsPrefix (terminal π U).1) :
    kappa_hist h ∈ strategyPrefixes N π := by
  refine Finset.mem_biUnion.mpr ⟨U, (allowedSources_exact N U).mpr allowed, ?_⟩
  exact List.mem_toFinset.mpr ((List.mem_inits _ _).mpr
    (pre.map (fun a : Sigma (fun _ : Address => Reply) =>
      (⟨a.1, kappa a.2⟩ : Sigma (fun _ : Address => Option Bool)))))

noncomputable def strategyStateCard (N : Nat) (π : Strategy) : Nat :=
  exactStateCard (strategyPrefixes N π)

theorem strategy_state_card (N : Nat) (π : Strategy) :
    Fintype.card (ExactState (strategyPrefixes N π)) = strategyStateCard N π := by
  exact exactState_card _

noncomputable def exactObserver {G : Finset CoarseHistory}
    (empty : [] ∈ G) (policy : CoarseHistory → Sum Address Bool) :
    Observer (ExactState G) where
  e0 := .inl ⟨⟨[], empty⟩, PUnit.unit⟩
  action := exactAction policy
  transition := exactTransition policy
  decoder
    | .inl r => exactRowDecoder r
    | .inr _ => []
  decoded_nodup e := by
    cases e with
    | inr _ => simp
    | inl r =>
        change ((decode (firstCoarse r.1.1) r.2).map Sigma.fst).Nodup
        rw [decode_addresses]
        exact firstCoarse_nodup _

private theorem exactObserver_initial_decoder {G : Finset CoarseHistory}
    (empty : [] ∈ G) (policy : CoarseHistory → Sum Address Bool) :
    (exactObserver empty policy).decoder (exactObserver empty policy).e0 = [] := by
  rfl

/-- A sourcewise continuation hypothesis for a coarse policy. It states exactly
that every query taken at an actual prefix has its next coarse prefix in the
finite carrier. The compiler replay theorem below consumes this hypothesis;
the supplied original `execute` run is the intended instantiation. -/
def ReplayStep (G : Finset CoarseHistory) (policy : CoarseHistory → Sum Address Bool)
    (U : Source) (horizon : RawHistory) : Prop :=
  ∀ {h : RawHistory} {q : Address},
    h.IsPrefix horizon → policy (kappa_hist h) = .inl q →
      kappa_hist (h ++ [(⟨q, readout q U⟩ : Sigma (fun _ : Address => Reply))]) ∈ G ∧
        (h ++ [(⟨q, readout q U⟩ : Sigma (fun _ : Address => Reply))]).IsPrefix horizon

private theorem exact_actual_prefix_replay {G : Finset CoarseHistory}
    (empty : [] ∈ G) (policy : CoarseHistory → Sum Address Bool)
    (U : Source) (horizon : RawHistory)
    (truth : ∀ {h : RawHistory}, h.IsPrefix horizon → CacheTruth (firstRaw h) U)
    (step : ReplayStep G policy U horizon)
    {e : ExactState G} {h : RawHistory}
    (pref : ActualPrefix (exactObserver empty policy) U e h) :
    ∃ r : ExactRow G,
      e = .inl r ∧ r.1.1 = kappa_hist h ∧ exactRowDecoder r = firstRaw h ∧
        h.IsPrefix horizon := by
  induction pref with
  | initial =>
      refine ⟨⟨⟨[], empty⟩, PUnit.unit⟩, rfl, rfl, ?_, List.nil_prefix⟩
      rfl
  | @query e h q prior row ih =>
      obtain ⟨r, state, history, decoder, pre⟩ := ih
      have action : policy (kappa_hist h) = .inl q := by
        rw [state] at row
        simpa only [exactObserver, exactAction, history] using row
      have action_r : policy r.1.1 = .inl q := by
        rw [state] at row
        simpa only [exactObserver, exactAction] using row
      obtain ⟨member, prenext⟩ := step pre action
      have reply : queryReply (exactRowDecoder r) q U = readout q U := by
        rw [decoder]
        exact queryReply_eq_readout (firstRaw h) U (truth pre) q
      have member' : r.1.1 ++ [⟨q, kappa (readout q U)⟩] ∈ G := by
        simpa only [history, kappa_hist, List.map_append, List.map_cons, List.map_nil]
          using member
      have projection_first :
          kappa_hist (firstRaw (h ++ [⟨q, readout q U⟩])) =
            firstCoarse (r.1.1 ++ [⟨q, kappa (readout q U)⟩]) := by
        rw [firstRaw_projection]
        simp only [kappa_hist, List.map_append, List.map_cons, List.map_nil, history]
      let r' := exactAppendRow r q (readout q U) member'
      let rawRow : ExactRow G :=
        ⟨⟨r.1.1 ++ [⟨q, kappa (readout q U)⟩], member'⟩,
          pack _ (firstRaw (h ++ [⟨q, readout q U⟩])) projection_first⟩
      have row_eq : r' = rawRow := by
        dsimp [r', exactAppendRow, rawRow]
        apply Sigma.ext
        · rfl
        · apply heq_of_eq
          apply decode_injective _
          rw [decode_pack, decode_pack]
          rw [decoder]
          exact (firstRaw_append_single h ⟨q, readout q U⟩).symm
      have prenext' :
          (h ++ [(⟨q, queryReply (exactRowDecoder r) q U⟩ :
            Sigma (fun _ : Address => Reply))]).IsPrefix horizon := by
        simpa only [reply] using prenext
      refine ⟨r', ?_, ?_, ?_, ?_⟩
      · rw [state]
        change exactTransition policy (.inl r)
          (queryReply (exactRowDecoder r) q U) = .inl r'
        rw [reply]
        simpa only [exactTransition, action_r, dif_pos member', r'] using
          congrArg (fun x : ExactRow G => (Sum.inl x : ExactState G)) row_eq
      · rw [state]
        change r'.1.1 = kappa_hist (h ++ [⟨q, queryReply (exactRowDecoder r) q U⟩])
        rw [reply, row_eq]
        simp only [rawRow, kappa_hist, List.map_append, List.map_cons, List.map_nil, history]
      · rw [state]
        change exactRowDecoder r' =
          firstRaw (h ++ [⟨q, queryReply (exactRowDecoder r) q U⟩])
        rw [reply]
        change exactRowDecoder (exactAppendRow r q (readout q U) member') = _
        rw [exactTransition_projection, decoder]
        exact (firstRaw_append_single h ⟨q, readout q U⟩).symm
      · rw [state]
        exact prenext'

private theorem cacheUpdate_truth (U : Source) (cache : RawHistory)
    (truth : CacheTruth cache U) (q : Address) (y : Reply)
    (answer : y = readout q U) : CacheTruth (cacheUpdate cache q y) U := by
  classical
  unfold cacheUpdate
  split
  · exact truth
  · intro a member
    rcases List.mem_append.mp member with member | member
    · exact truth a member
    · obtain rfl := List.mem_singleton.mp member
      exact answer

private theorem firstRaw_truth_fold (U : Source) (cache h : RawHistory)
    (hc : CacheTruth cache U) (hh : CacheTruth h U) :
    CacheTruth (h.foldl (fun cache a => cacheUpdate cache a.1 a.2) cache) U := by
  induction h generalizing cache with
  | nil => exact hc
  | cons a h ih =>
      exact ih (cacheUpdate cache a.1 a.2)
        (cacheUpdate_truth U cache hc a.1 a.2 (hh a (List.mem_cons_self)))
        (fun b hb => hh b (List.mem_cons_of_mem a hb))

private theorem firstRaw_truth (U : Source) (h : RawHistory) (truth : CacheTruth h U) :
    CacheTruth (firstRaw h) U := by
  exact firstRaw_truth_fold U [] h (by simp [CacheTruth]) truth

private theorem terminal_prefix_truth (π : Strategy) (U : Source) {h : RawHistory}
    (pre : h.IsPrefix (terminal π U).1) : CacheTruth (firstRaw h) U := by
  apply firstRaw_truth
  obtain ⟨run, correct⟩ := Classical.choose_spec (Classical.choose_spec (π.correct U))
  have reports := (execute_transfer readout π.policy _ [] U _ _ run).1
  intro a ha
  exact (reports a (pre.subset ha)).symm


private theorem execute_suffix (raw : RawHistory → Sum Address Bool) (U : Source)
    (n : Nat) (h₀ h s : RawHistory) (b : Bool)
    (run : execute readout raw n h₀ U = some (h ++ s, b)) :
    ∃ m, execute readout raw m (h₀ ++ h) U = some (s, b) := by
  induction n generalizing h₀ h with
  | zero => simp [execute] at run
  | succ n ih =>
      cases h with
      | nil => exact ⟨n + 1, by simpa using run⟩
      | cons a h =>
          cases action : raw h₀ with
          | inr c => simp [execute, action] at run
          | inl q =>
              simp only [execute, action] at run
              obtain ⟨⟨t, c⟩, tail, equal⟩ := Option.map_eq_some_iff.mp run
              have parts : (⟨q, readout q U⟩ : Sigma (fun _ : Address => Reply)) = a ∧
                  t = h ++ s ∧ c = b := by
                simpa only [Prod.mk.injEq, List.cons_append, List.cons.injEq, and_assoc]
                  using equal
              obtain ⟨rfl, rfl, rfl⟩ := parts
              obtain ⟨m, rest⟩ := ih (h₀ ++ [⟨q, readout q U⟩]) h tail
              exact ⟨m, by simpa only [List.append_assoc, List.singleton_append] using rest⟩

private theorem execute_query_prefix (raw : RawHistory → Sum Address Bool)
    (U : Source) (n : Nat) (t : RawHistory) (b : Bool)
    (run : execute readout raw n [] U = some (t, b))
    {h : RawHistory} {q : Address} (pre : h.IsPrefix t)
    (action : raw h = .inl q) :
    (h ++ [(⟨q, readout q U⟩ : Sigma (fun _ : Address => Reply))]).IsPrefix t := by
  obtain ⟨s, rfl⟩ := pre
  obtain ⟨m, tail⟩ := execute_suffix raw U n [] h s b run
  simp only [List.nil_append] at tail
  cases m with
  | zero => simp [execute] at tail
  | succ m =>
      simp only [execute, action] at tail
      obtain ⟨⟨s', c⟩, rest, equal⟩ := Option.map_eq_some_iff.mp tail
      have same : (⟨q, readout q U⟩ : Sigma (fun _ : Address => Reply)) :: s' = s :=
        (Prod.mk.inj equal).1
      subst s
      exact ⟨s', by simp only [List.append_assoc, List.singleton_append]⟩

/-- Evaluate the original coarse-factorizing policy through the fixed section
of the raw reply quotient. No stored raw branch/absent distinction enters it. -/
noncomputable def strategyPolicy (π : Strategy) : CoarseHistory → Sum Address Bool :=
  fun g => π.policy (ActualCoarseReadoutCompletion.encodeHistory g)

theorem encode_projection (g : CoarseHistory) :
    kappa_hist (ActualCoarseReadoutCompletion.encodeHistory g) = g := by
  induction g with
  | nil => rfl
  | cons a g ih =>
      rcases a with ⟨q, z⟩
      cases z with
      | none => simpa only [ActualCoarseReadoutCompletion.encodeHistory, kappa_hist,
          List.map_cons, kappa] using congrArg (List.cons ⟨q, none⟩) ih
      | some b =>
          cases b <;> simpa only [ActualCoarseReadoutCompletion.encodeHistory, kappa_hist,
            List.map_cons, kappa] using congrArg (List.cons ⟨q, some _⟩) ih

private theorem strategyPolicy_exact (π : Strategy)
    (coarse : Function.FactorsThrough π.policy kappa_hist) (h : RawHistory) :
    strategyPolicy π (kappa_hist h) = π.policy h := by
  exact coarse (encode_projection (kappa_hist h))

private theorem strategy_replay_step (N : Nat) (π : Strategy)
    (coarse : Function.FactorsThrough π.policy kappa_hist)
    (U : Source) (allowed : Allowed N U) :
    ReplayStep (strategyPrefixes N π) (strategyPolicy π) U (terminal π U).1 := by
  intro h q pre action
  have action' : π.policy h = .inl q := by
    rwa [strategyPolicy_exact π coarse h] at action
  obtain ⟨run, _⟩ := Classical.choose_spec (Classical.choose_spec (π.correct U))
  have next := execute_query_prefix π.policy U _ _ _ run pre action'
  exact ⟨strategy_prefix_mem N π allowed next, next⟩

/-- The original finite coarse prefixes give a finite observer for every
coarse-factorizing strategy, including repeated and arbitrarily long requests. -/
noncomputable def strategyObserver (N : Nat) (π : Strategy) (positive : 1 ≤ N) :
    Observer (ExactState (strategyPrefixes N π)) :=
  exactObserver (strategyPrefixes_nonempty N π positive) (strategyPolicy π)

theorem strategy_actual_prefix_replay (N : Nat) (π : Strategy) (positive : 1 ≤ N)
    (coarse : Function.FactorsThrough π.policy kappa_hist)
    (U : Source) (allowed : Allowed N U)
    {e : ExactState (strategyPrefixes N π)} {h : RawHistory}
    (pref : ActualPrefix (strategyObserver N π positive) U e h) :
    ∃ r : ExactRow (strategyPrefixes N π),
      e = .inl r ∧ r.1.1 = kappa_hist h ∧ exactRowDecoder r = firstRaw h ∧
        h.IsPrefix (terminal π U).1 := by
  exact exact_actual_prefix_replay _ _ U _ (terminal_prefix_truth π U)
    (strategy_replay_step N π coarse U allowed) pref

/-- Forget the raw cache lift, retaining the logical control word or sink. -/
def exactControl {G : Finset CoarseHistory} : ExactState G → Option CoarseHistory
  | .inl r => some r.1.1
  | .inr _ => none

private theorem exact_action_control {G : Finset CoarseHistory}
    (policy : CoarseHistory → Sum Address Bool) {e f : ExactState G}
    (same : exactControl e = exactControl f) : exactAction policy e = exactAction policy f := by
  cases e with
  | inr u => cases f <;> simp_all [exactControl, exactAction]
  | inl r =>
      cases f with
      | inr u => simp [exactControl] at same
      | inl s =>
          have history : r.1.1 = s.1.1 := Option.some.inj same
          simp only [exactAction, history]

private theorem exact_bar_control {G : Finset CoarseHistory}
    (empty : [] ∈ G) (policy : CoarseHistory → Sum Address Bool)
    {e f : ExactState G} (same : exactControl e = exactControl f)
    {y z : Reply} (coarse : kappa y = kappa z) :
    exactControl (ActualFiniteObserverAbsentElimination.barStep (exactObserver empty policy) e y) =
      exactControl (ActualFiniteObserverAbsentElimination.barStep
        (exactObserver empty policy) f z) := by
  classical
  cases e with
  | inr u =>
      cases f <;> simp_all [exactControl, ActualFiniteObserverAbsentElimination.barStep,
        exactObserver, exactAction]
  | inl r =>
      cases f with
      | inr u => simp [exactControl] at same
      | inl s =>
          have history : r.1.1 = s.1.1 := Option.some.inj same
          simp only [ActualFiniteObserverAbsentElimination.barStep, exactObserver, exactAction]
          rw [← history]
          cases action : policy r.1.1 with
          | inr b => exact same
          | inl q =>
              simp only [exactTransition, ← history, action, ← coarse]
              split <;> simp only [exactControl, exactAppendRow, history, coarse]

/-- Raw ghost contradictions cannot affect control: all finite histories,
including wrong-address, repeated and post-halt reports, factor coarsely. -/
theorem exact_all_history_factorization {G : Finset CoarseHistory}
    (empty : [] ∈ G) (policy : CoarseHistory → Sum Address Bool) :
    Function.FactorsThrough
      (ActualFiniteObserverAbsentElimination.historyAction (exactObserver empty policy))
      kappa_hist := by
  apply (ActualObserverPairReach.pairActionInvariant_iff_allHistoryFactorization _).mp
  intro e f reached
  have same : exactControl e = exactControl f := by
    induction reached with
    | initial => rfl
    | step prior coarse ih => exact exact_bar_control empty policy ih coarse
  exact exact_action_control policy same

theorem strategy_prefix_action (N : Nat) (π : Strategy) (positive : 1 ≤ N)
    (coarse : Function.FactorsThrough π.policy kappa_hist)
    (U : Source) (allowed : Allowed N U)
    {e : ExactState (strategyPrefixes N π)} {h : RawHistory}
    (pref : ActualPrefix (strategyObserver N π positive) U e h) :
    (strategyObserver N π positive).action e = π.policy h := by
  obtain ⟨r, rfl, history, _, _⟩ :=
    strategy_actual_prefix_replay N π positive coarse U allowed pref
  change strategyPolicy π r.1.1 = _
  rw [history, strategyPolicy_exact π coarse]

private theorem strategy_legal (N : Nat) (π : Strategy) (positive : 1 ≤ N)
    (coarse : Function.FactorsThrough π.policy kappa_hist)
    (U : Source) (allowed : Allowed N U) :
    ActualFiniteObserverAbsentElimination.Legal (strategyObserver N π positive) U := by
  refine ⟨exactObserver_initial_decoder _ _, ?_⟩
  intro e h pref
  obtain ⟨r, state, history, decoder, pre⟩ :=
    strategy_actual_prefix_replay N π positive coarse U allowed pref
  have current : (strategyObserver N π positive).decoder e = firstRaw h := by
    rw [state]
    exact decoder
  refine ⟨?_, ?_⟩
  · rw [current]
    exact terminal_prefix_truth π U pre
  · intro q action
    obtain ⟨s, next, _, cache, _⟩ :=
      strategy_actual_prefix_replay N π positive coarse U allowed (ActualPrefix.query pref action)
    rw [next]
    change exactRowDecoder s = _
    rw [cache, firstRaw_append_single, current]

private theorem strategy_execute_run (N : Nat) (π : Strategy) (positive : 1 ≤ N)
    (coarse : Function.FactorsThrough π.policy kappa_hist)
    (U : Source) (allowed : Allowed N U) (n : Nat) :
    ∀ (h t : RawHistory) (b : Bool) (e : ExactState (strategyPrefixes N π)),
      ActualPrefix (strategyObserver N π positive) U e h →
      execute readout π.policy n h U = some (t, b) →
      ∃ f, ActualFiniteObserverAbsentElimination.Run (strategyObserver N π positive) U e t f b := by
  induction n with
  | zero => simp [execute]
  | succ n ih =>
      intro h t b e pref run
      have action := strategy_prefix_action N π positive coarse U allowed pref
      cases original : π.policy h with
      | inr c =>
          have parts : [] = t ∧ c = b := by simpa only [execute, original,
            Option.some.injEq, Prod.mk.injEq] using run
          obtain ⟨rfl, rfl⟩ := parts
          exact ⟨e, .halt (action.trans original)⟩
      | inl q =>
          have row := action.trans original
          have truthful := (strategy_legal N π positive coarse U allowed).2 e h pref
          have reply := queryReply_eq_readout
            ((strategyObserver N π positive).decoder e) U truthful.1 q
          simp only [execute, original] at run
          obtain ⟨⟨s, c⟩, tail, equal⟩ := Option.map_eq_some_iff.mp run
          have parts : (⟨q, readout q U⟩ : Sigma (fun _ : Address => Reply)) :: s = t ∧
              c = b := Prod.mk.inj equal
          obtain ⟨rfl, rfl⟩ := parts
          have next := ActualPrefix.query pref row
          rw [reply] at next
          obtain ⟨f, rest⟩ := ih _ s c _ next tail
          have rest' : ActualFiniteObserverAbsentElimination.Run
              (strategyObserver N π positive) U
              ((strategyObserver N π positive).transition e
                (queryReply ((strategyObserver N π positive).decoder e) q U)) s f c := by
            simpa only [reply] using rest
          refine ⟨f, ?_⟩
          simpa only [reply] using (ActualFiniteObserverAbsentElimination.Run.query row rest')

/-- The compiler has the exact original terminating raw trace and output.
No repeats or cache hits are removed from the chronological run. -/
theorem strategy_exact_run (N : Nat) (π : Strategy) (positive : 1 ≤ N)
    (coarse : Function.FactorsThrough π.policy kappa_hist)
    (U : Source) (allowed : Allowed N U) :
    ∃ f, ActualFiniteObserverAbsentElimination.Run (strategyObserver N π positive) U
      (strategyObserver N π positive).e0 (terminal π U).1 f (terminal π U).2 := by
  obtain ⟨run, _⟩ := Classical.choose_spec (Classical.choose_spec (π.correct U))
  exact strategy_execute_run N π positive coarse U allowed _ [] _ _ _ .initial run

/-- Exact finite realization retains both the full raw execution and the
original all-history observer contract on the complete bounded source domain. -/
theorem strategy_admissible (N : Nat) (π : Strategy) (positive : 1 ≤ N)
    (coarse : Function.FactorsThrough π.policy kappa_hist) :
    ActualFiniteObserverAbsentElimination.Admissible N (strategyObserver N π positive) where
  budget_pos := positive
  legal := strategy_legal N π positive coarse
  correct U allowed := by
    obtain ⟨f, run⟩ := strategy_exact_run N π positive coarse U allowed
    exact ⟨(terminal π U).1, f, (terminal π U).2, run,
      (Classical.choose_spec (Classical.choose_spec (π.correct U))).2⟩
  coarse := exact_all_history_factorization _ _

private theorem coarse_fold_length (cache g : CoarseHistory) :
    (g.foldl (fun cache a => coarseCacheUpdate cache a.1 a.2) cache).length ≤
      cache.length + g.length := by
  induction g generalizing cache with
  | nil => simp
  | cons a g ih =>
      have step : (coarseCacheUpdate cache a.1 a.2).length ≤ cache.length + 1 := by
        unfold coarseCacheUpdate
        split <;> simp
      have rest := ih (coarseCacheUpdate cache a.1 a.2)
      simp only [List.foldl_cons, List.length_cons]
      omega

private theorem coarse_fold_support (Q : Finset Address) (cache g : CoarseHistory)
    (hc : ∀ a ∈ cache, a.1 ∈ Q) (hg : ∀ a ∈ g, a.1 ∈ Q) :
    ∀ a ∈ g.foldl (fun cache a => coarseCacheUpdate cache a.1 a.2) cache, a.1 ∈ Q := by
  induction g generalizing cache with
  | nil => exact hc
  | cons a g ih =>
      apply ih (coarseCacheUpdate cache a.1 a.2)
      · intro b hb
        unfold coarseCacheUpdate at hb
        split at hb
        · exact hc b hb
        · rcases List.mem_append.mp hb with old | fresh
          · exact hc b old
          · obtain rfl := List.mem_singleton.mp fresh
            exact hg a List.mem_cons_self
      · intro b hb
        exact hg b (List.mem_cons_of_mem a hb)

private theorem firstCoarse_none_bound (Q : Finset Address) (H : Nat)
    (g : CoarseHistory) (len : g.length ≤ H) (support : ∀ a ∈ g, a.1 ∈ Q) :
    noneCount (firstCoarse g) ≤ min Q.card H := by
  have filterBound : noneCount (firstCoarse g) ≤ (firstCoarse g).length :=
    List.length_filter_le _ _
  have lengthBound : (firstCoarse g).length ≤ g.length := by
    simpa only [firstCoarse, List.length_nil, Nat.zero_add] using coarse_fold_length [] g
  have subset : ((firstCoarse g).map Sigma.fst).toFinset ⊆ Q := by
    intro q member
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp member)
    exact coarse_fold_support Q [] g (by simp) support a ha
  have cardinal : (firstCoarse g).length ≤ Q.card := by
    have count := Finset.card_le_card subset
    rwa [List.toFinset_card_of_nodup (firstCoarse_nodup g), List.length_map] at count
  exact le_min (filterBound.trans cardinal) (filterBound.trans (lengthBound.trans len))

/-- A source-uniform trace horizon bounds the number of retained logical
prefixes; repeated requests are still counted as separate chronological steps. -/
private theorem strategy_prefix_card_bound (N : Nat) (π : Strategy) (H : Nat)
    (horizon : ∀ U : Source, Allowed N U → (terminal π U).1.length ≤ H) :
    (strategyPrefixes N π).card ≤ (allowedSources N).card * (H + 1) := by
  classical
  apply Finset.card_biUnion_le_card_mul
  intro U member
  calc
    (List.inits (kappa_hist (terminal π U).1)).toFinset.card ≤
        (List.inits (kappa_hist (terminal π U).1)).length := List.toFinset_card_le _
    _ = (terminal π U).1.length + 1 := by simp [kappa_hist]
    _ ≤ H + 1 := Nat.add_le_add_right (horizon U ((allowedSources_exact N U).mp member)) 1

/-- The exact compatible-cache sum has the uniform finite-source bound using
both a literal address support and the original logical request horizon. -/
theorem strategy_state_card_bound (N : Nat) (π : Strategy) (H : Nat) (Q : Finset Address)
    (horizon : ∀ U : Source, Allowed N U → (terminal π U).1.length ≤ H)
    (support : ∀ U : Source, Allowed N U → ∀ a ∈ (terminal π U).1, a.1 ∈ Q) :
    Fintype.card (ExactState (strategyPrefixes N π)) ≤
      1 + (allowedSources N).card * (H + 1) * 2 ^ min Q.card H := by
  classical
  rw [strategy_state_card]
  unfold strategyStateCard exactStateCard
  apply Nat.add_le_add_left
  calc
    ∑ g ∈ strategyPrefixes N π, 2 ^ noneCount (firstCoarse g) ≤
        (strategyPrefixes N π).card * 2 ^ min Q.card H := by
      apply Finset.sum_le_card_nsmul
      intro g member
      obtain ⟨U, allowed, member⟩ := Finset.mem_biUnion.mp member
      have pre := (List.mem_inits _ _).mp (List.mem_toFinset.mp member)
      have permitted := (allowedSources_exact N U).mp allowed
      apply Nat.pow_le_pow_right (by omega)
      apply firstCoarse_none_bound Q H g
      · exact pre.length_le.trans (by
          simpa only [kappa_hist, List.length_map] using horizon U permitted)
      · intro a ha
        obtain ⟨b, hb, equal⟩ := List.mem_map.mp (pre.subset ha)
        have address : b.1 = a.1 := congrArg Sigma.fst equal
        rw [← address]
        exact support U permitted b hb
    _ ≤ (allowedSources N).card * (H + 1) * 2 ^ min Q.card H :=
      Nat.mul_le_mul_right _ (strategy_prefix_card_bound N π H horizon)

end D5.S3.Arith.FibonacciAtomic.Observer.ActualExactTraceCompiler
