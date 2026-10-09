/- GID: D5/S3/Arith/FibonacciAtomic/Observer/ActualPureAcquisitionCompiler
   generality: G
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Source-local pure acquisition carrier and exact compatible-cache count. -/

import D5.S3.Arith.FibonacciAtomic.Observer.ActualAcquisitionCacheFiber
import D5.S3.Arith.FibonacciAtomic.Observer.ActualObserverFiniteTable
import D5.S3.Arith.FibonacciAtomic.ActualCoarseReadoutCompletion

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.Observer.ActualPureAcquisitionCompiler

open GenealogicalFiberTransport (Source)
open D5.S3.ConceptDynamics.Experiment.PassivePolicyNormalization (execute)
open ActualTreeReadoutAcquisition
open ActualCoarseReadoutHistory (kappa kappa_hist)
open ActualFiniteObserverAbsentElimination
open ActualObserverAbsorbingNormalization
open ActualAcquisitionCacheFiber
open ActualObserverPairReach
open ActualObserverFiniteTable
open ActualCoarseReadoutCompletion (encodeHistory acquisition_prefix_representative)

/-- The exact coarse carrier: all prefixes of every original allowed trace. -/
noncomputable def coarsePrefixes (N : Nat) : Finset CoarseHistory := by
  classical
  exact (allowedSources N).biUnion (fun U =>
    (List.inits (kappa_hist (acquisitionTrace [] U))).toFinset)

abbrev CoarseIndex (N : Nat) := {g : CoarseHistory // g ∈ coarsePrefixes N}
abbrev PureRow (N : Nat) := Sigma (fun i : CoarseIndex N => CompatCache i.1)
abbrev PureState (N : Nat) := Sum (PureRow N) Unit

noncomputable instance pureStateFintype (N : Nat) : Fintype (PureState N) := by
  dsimp [PureState, PureRow, CoarseIndex]
  infer_instance

noncomputable def nominalCard (N : Nat) : Nat :=
  1 + ∑ g ∈ coarsePrefixes N, 2 ^ noneCount g

theorem pureState_card (N : Nat) :
    Fintype.card (PureState N) = nominalCard N := by
  classical
  simp only [PureState, nominalCard, Fintype.card_sum, Fintype.card_unit,
    Fintype.card_sigma, compatible_cache_card]
  rw [← Finset.sum_coe_sort (coarsePrefixes N) (fun g => 2 ^ noneCount g)]
  exact Nat.add_comm _ _

/-- The original acquisition trace has the original node preorder. -/
theorem trace_addresses (U : Source) (u : Address) :
    (acquisitionTrace u U).map Sigma.fst = (nodes U).map (u ++ ·) := by
  induction U generalizing u with
  | of b => simp [acquisitionTrace, nodes]
  | mul s t ihs iht =>
    simp only [acquisitionTrace, nodes, List.map_cons, List.map_append, ihs, iht,
      List.map_map, Function.comp_def, List.append_assoc, List.singleton_append,
      List.append_nil]


private theorem nodes_nodup (U : Source) : (nodes U).Nodup := by
  induction U with
  | of b => simp [nodes]
  | mul s t ihs iht =>
    rw [nodes, List.nodup_cons]
    refine ⟨by simp, List.nodup_append.mpr ⟨ihs.map (fun _ _ h => by cases h; rfl),
      iht.map (fun _ _ h => by cases h; rfl), ?_⟩⟩
    intro a ha b hb equal
    obtain ⟨x, _, rfl⟩ := List.mem_map.mp ha
    obtain ⟨y, _, rfl⟩ := List.mem_map.mp hb
    cases equal

private theorem trace_nodup (U : Source) :
    ((acquisitionTrace [] U).map Sigma.fst).Nodup := by
  simpa [trace_addresses] using nodes_nodup U

private theorem coarse_nodup (N : Nat) {g : CoarseHistory}
    (member : g ∈ coarsePrefixes N) : (g.map Sigma.fst).Nodup := by
  classical
  obtain ⟨U, _, hg⟩ := Finset.mem_biUnion.mp member
  have pre : g.IsPrefix (kappa_hist (acquisitionTrace [] U)) :=
    (List.mem_inits _ _).mp (List.mem_toFinset.mp hg)
  have nd : ((kappa_hist (acquisitionTrace [] U)).map Sigma.fst).Nodup := by
    simpa only [kappa_hist, List.map_map, Function.comp_def] using trace_nodup U
  exact (pre.map Sigma.fst).nodup nd

private theorem prefix_mem (N : Nat) (U : Source) (allowed : Allowed N U)
    {h : RawHistory} (pre : h.IsPrefix (acquisitionTrace [] U)) :
    kappa_hist h ∈ coarsePrefixes N := by
  classical
  refine Finset.mem_biUnion.mpr ⟨U, (allowedSources_exact N U).mpr allowed, ?_⟩
  exact List.mem_toFinset.mpr ((List.mem_inits _ _).mpr
    (pre.map (fun a : Sigma (fun _ : Address => Reply) =>
      (⟨a.1, kappa a.2⟩ : Sigma (fun _ : Address => Option Bool)))))

private theorem empty_mem (N : Nat) (positive : 1 ≤ N) :
    [] ∈ coarsePrefixes N := by
  obtain ⟨U, hU⟩ := allowedSources_nonempty N positive
  exact prefix_mem N U ((allowedSources_exact N U).mp hU) List.nil_prefix

noncomputable def emptyRow (N : Nat) (positive : 1 ≤ N) : PureRow N :=
  ⟨⟨[], empty_mem N positive⟩, PUnit.unit⟩

noncomputable def rowDecoder {N : Nat} (r : PureRow N) : RawHistory :=
  decode r.1.1 r.2

private theorem row_nodup {N : Nat} (r : PureRow N) :
    ((rowDecoder r).map Sigma.fst).Nodup := by
  change ((decode _ _).map Sigma.fst).Nodup
  rw [decode_addresses]
  exact coarse_nodup N r.1.2

noncomputable def rowOfHistory (N : Nat) (h : RawHistory)
    (hm : kappa_hist h ∈ coarsePrefixes N) : PureRow N :=
  ⟨⟨kappa_hist h, hm⟩, pack (kappa_hist h) h rfl⟩

private theorem row_decode (N : Nat) (h : RawHistory)
    (hm : kappa_hist h ∈ coarsePrefixes N) : rowDecoder (rowOfHistory N h hm) = h := by
  exact decode_pack (kappa_hist h) h rfl

private theorem row_ext {N : Nat} {r s : PureRow N} (idx : r.1 = s.1)
    (raw : rowDecoder r = rowDecoder s) : r = s := by
  cases r with
  | mk i c =>
    cases s with
    | mk j d =>
      cases idx
      exact congrArg (Sigma.mk i) (decode_injective i.1 raw)

/-- Control uses only the coarse prefix; cache lifts are invisible to it. -/
noncomputable def pureAction {N : Nat} : PureState N → Sum Address Bool
  | .inl r => acquisitionPolicy (encodeHistory r.1.1)
  | .inr _ => .inr false

private theorem update_projection (N : Nat) (r : PureRow N) (q : Address) (y : Reply)
    (hm : r.1.1 ++ [⟨q, kappa y⟩] ∈ coarsePrefixes N) :
    kappa_hist (cacheUpdate (rowDecoder r) q y) = r.1.1 ++ [⟨q, kappa y⟩] := by
  classical
  have nd := coarse_nodup N hm
  rw [List.map_append, List.nodup_append] at nd
  have fresh : q ∉ r.1.1.map Sigma.fst := by
    intro hq
    exact nd.2.2 q hq q (by simp) rfl
  have decoded : (rowDecoder r).map Sigma.fst = r.1.1.map Sigma.fst :=
    decode_addresses _ _
  rw [cacheUpdate, decoded, if_neg fresh]
  simp only [kappa_hist, List.map_append, List.map_cons, List.map_nil]
  exact congrArg (· ++ [⟨q, kappa y⟩]) (decode_projection _ _)

/-- Row versus sink depends solely on coarse-prefix membership. -/
noncomputable def appendRow (N : Nat) (r : PureRow N) (q : Address) (y : Reply) :
    PureState N := by
  classical
  let g := r.1.1 ++ [⟨q, kappa y⟩]
  exact if hm : g ∈ coarsePrefixes N then
    .inl ⟨⟨g, hm⟩, pack g (cacheUpdate (rowDecoder r) q y)
      (update_projection N r q y hm)⟩ else .inr ()

noncomputable def pureTransition {N : Nat} : PureState N → Reply → PureState N
  | .inr u, _ => .inr u
  | .inl r, y => match pureAction (.inl r) with
    | .inl q => appendRow N r q y
    | .inr _ => .inl r

/-- The original observer contract, with an input-independent empty row. -/
noncomputable def pureObserver (N : Nat) (positive : 1 ≤ N) : Observer (PureState N) where
  e0 := .inl (emptyRow N positive)
  action := pureAction
  transition := pureTransition
  decoder
    | .inl r => rowDecoder r
    | .inr _ => []
  decoded_nodup
    | .inl r => row_nodup r
    | .inr _ => List.nodup_nil

/-- Forget raw cache lifts while retaining the absorbing sink. -/
def control {N : Nat} : PureState N → Option (CoarseIndex N)
  | .inl r => some r.1
  | .inr _ => none

private theorem action_control {N : Nat} {e f : PureState N}
    (same : control e = control f) : pureAction e = pureAction f := by
  cases e with
  | inr u => cases f <;> simp_all [control, pureAction]
  | inl r =>
    cases f with
    | inr u => simp [control] at same
    | inl s =>
      have idx : r.1 = s.1 := Option.some.inj same
      simp only [pureAction, idx]

private theorem append_control (N : Nat) (r s : PureRow N) (q : Address) (y z : Reply)
    (same : r.1 = s.1) (coarse : kappa y = kappa z) :
    control (appendRow N r q y) = control (appendRow N s q z) := by
  classical
  simp only [appendRow]
  have gs : r.1.1 ++ [⟨q, kappa y⟩] = s.1.1 ++ [⟨q, kappa z⟩] := by rw [same, coarse]
  split <;> split
  · simp only [control]; congr 1; exact Subtype.ext gs
  · rename_i hr hs; exact (hs (gs ▸ hr)).elim
  · rename_i hr hs; exact (hr (gs.symm ▸ hs)).elim
  · rfl

private theorem bar_control (N : Nat) (positive : 1 ≤ N) {e f : PureState N}
    (same : control e = control f) {y z : Reply} (coarse : kappa y = kappa z) :
    control (barStep (pureObserver N positive) e y) =
      control (barStep (pureObserver N positive) f z) := by
  have act := action_control same
  cases e with
  | inr u =>
    cases f <;> simp_all [control, barStep, pureObserver, pureAction]
  | inl r =>
    cases f with
    | inr u => simp [control] at same
    | inl s =>
      have idx : r.1 = s.1 := Option.some.inj same
      simp only [barStep, pureObserver]
      rw [← act]
      cases ha : pureAction (Sum.inl r : PureState N) with
      | inr b => exact same
      | inl q =>
        simp only [pureTransition, ha]
        have other : pureAction (Sum.inl s : PureState N) = .inl q := act.symm.trans ha
        rw [other]
        exact append_control N r s q y z idx coarse

/-- Every inconsistent, repeated and post-halt raw response word is included. -/
theorem pure_all_history_factorization (N : Nat) (positive : 1 ≤ N) :
    Function.FactorsThrough (historyAction (pureObserver N positive)) kappa_hist := by
  apply (pairActionInvariant_iff_allHistoryFactorization _).mp
  intro e f reached
  have same : control e = control f := by
    induction reached with
    | initial => rfl
    | step prior coarse ih => exact bar_control N positive ih coarse
  exact action_control same


private theorem history_coarse_append (h : RawHistory) (q : Address) (y : Reply) :
    kappa_hist (h ++ [⟨q, y⟩]) = kappa_hist h ++ [⟨q, kappa y⟩] := by
  simp only [kappa_hist, List.map_append, List.map_cons, List.map_nil]

private theorem append_history (N : Nat) (h : RawHistory)
    (hm : kappa_hist h ∈ coarsePrefixes N) (q : Address) (y : Reply)
    (hn : kappa_hist (h ++ [⟨q, y⟩]) ∈ coarsePrefixes N) :
    appendRow N (rowOfHistory N h hm) q y =
      .inl (rowOfHistory N (h ++ [⟨q, y⟩]) hn) := by
  classical
  have hn' : kappa_hist h ++ [⟨q, kappa y⟩] ∈ coarsePrefixes N := by
    rwa [history_coarse_append] at hn
  have fresh : q ∉ h.map Sigma.fst := by
    have nd : ((h ++ [(⟨q, y⟩ : Sigma (fun _ : Address => Reply))]).map Sigma.fst).Nodup := by
      simpa only [kappa_hist, List.map_map, Function.comp_def] using coarse_nodup N hn
    rw [List.map_append, List.nodup_append] at nd
    intro hq
    exact nd.2.2 q hq q (by simp) rfl
  dsimp only [appendRow]
  change (if hh : kappa_hist h ++ [⟨q, kappa y⟩] ∈ coarsePrefixes N then _ else _) = _
  rw [dif_pos hn']
  congr 1
  apply row_ext
  · exact Subtype.ext (history_coarse_append h q y).symm
  · simp only [rowDecoder, decode_pack]
    rw [← rowDecoder, row_decode, ← rowDecoder, row_decode, cacheUpdate, if_neg fresh]

private theorem prefix_truth (U : Source) {h : RawHistory}
    (pre : h.IsPrefix (acquisitionTrace [] U)) : CacheTruth h U := by
  have truth := (D5.S3.ConceptDynamics.Experiment.PassivePolicyNormalization.execute_transfer
    readout acquisitionPolicy _ [] U _ _ (acquisition_foundation.2 U)).1
  intro a ha
  exact (truth a (pre.subset ha)).symm

private theorem action_history (N : Nat) (positive : 1 ≤ N) (U : Source)
    (h : RawHistory) (hm : kappa_hist h ∈ coarsePrefixes N)
    (pre : h.IsPrefix (acquisitionTrace [] U)) :
    (pureObserver N positive).action (.inl (rowOfHistory N h hm)) = acquisitionPolicy h := by
  change acquisitionPolicy (encodeHistory (kappa_hist h)) = _
  rw [acquisition_prefix_representative U h pre]

private theorem transition_history (N : Nat) (positive : 1 ≤ N) (U : Source)
    (h : RawHistory) (hm : kappa_hist h ∈ coarsePrefixes N) (q : Address)
    (pre : h.IsPrefix (acquisitionTrace [] U)) (action : acquisitionPolicy h = .inl q)
    (hn : kappa_hist (h ++ [⟨q, readout q U⟩]) ∈ coarsePrefixes N) :
    (pureObserver N positive).transition (.inl (rowOfHistory N h hm))
      (queryReply ((pureObserver N positive).decoder (.inl (rowOfHistory N h hm))) q U) =
        .inl (rowOfHistory N (h ++ [⟨q, readout q U⟩]) hn) := by
  have row := (action_history N positive U h hm pre).trans action
  have reply : queryReply (rowDecoder (rowOfHistory N h hm)) q U = readout q U := by
    rw [row_decode]
    exact queryReply_eq_readout h U (prefix_truth U pre) q
  change pureTransition (.inl (rowOfHistory N h hm))
    (queryReply (rowDecoder (rowOfHistory N h hm)) q U) = _
  rw [reply]
  simp only [pureTransition]
  change (match (pureObserver N positive).action (.inl (rowOfHistory N h hm)) with
    | .inl q' => appendRow N (rowOfHistory N h hm) q' (readout q U)
    | .inr _ => .inl (rowOfHistory N h hm)) = _
  rw [row]
  exact append_history N h hm q (readout q U) hn

private theorem execute_to_run (N : Nat) (positive : 1 ≤ N) (U : Source)
    (allowed : Allowed N U) :
    ∀ (n : Nat) (h t : RawHistory) (b : Bool)
      (hm : kappa_hist h ∈ coarsePrefixes N),
      execute readout acquisitionPolicy n h U = some (t,b) →
      h ++ t = acquisitionTrace [] U →
      ∃ f, Run (pureObserver N positive) U (.inl (rowOfHistory N h hm)) t f b := by
  intro n
  induction n with
  | zero => intro h t b hm run; simp [execute] at run
  | succ n ih =>
    intro h t b hm run full
    have pre : h.IsPrefix (acquisitionTrace [] U) := ⟨t, full⟩
    cases action : acquisitionPolicy h with
    | inr c =>
      simp only [execute, action, Option.some.injEq, Prod.mk.injEq] at run
      obtain ⟨rfl, rfl⟩ := run
      exact ⟨_, Run.halt ((action_history N positive U h hm pre).trans action)⟩
    | inl q =>
      simp only [execute, action] at run
      obtain ⟨⟨s,c⟩, rest, eq⟩ := Option.map_eq_some_iff.mp run
      simp only [Prod.mk.injEq] at eq
      obtain ⟨rfl, rfl⟩ := eq
      let hn := h ++ [⟨q, readout q U⟩]
      have fulln : hn ++ s = acquisitionTrace [] U := by
        simpa only [hn, List.append_assoc, List.singleton_append] using full
      have pren : hn.IsPrefix (acquisitionTrace [] U) := ⟨s, fulln⟩
      have hmn := prefix_mem N U allowed pren
      obtain ⟨f, tail⟩ := ih hn s c hmn rest fulln
      refine ⟨f, ?_⟩
      have next := transition_history N positive U h hm q pre action hmn
      have reply : queryReply ((pureObserver N positive).decoder
          (.inl (rowOfHistory N h hm))) q U = readout q U := by
        change queryReply (rowDecoder _) q U = _
        rw [row_decode]
        exact queryReply_eq_readout h U (prefix_truth U pre) q
      have built := Run.query ((action_history N positive U h hm pre).trans action)
        (next.symm ▸ tail)
      simpa only [reply] using built

/-- Every bounded source follows exactly the original acquisition preorder and bit. -/
theorem pure_acquisition_run (N : Nat) (positive : 1 ≤ N) (U : Source)
    (allowed : Allowed N U) :
    ∃ f, Run (pureObserver N positive) U (pureObserver N positive).e0
      (acquisitionTrace [] U) f (finiteDecision U) := by
  have hm := empty_mem N positive
  obtain ⟨f, run⟩ := execute_to_run N positive U allowed ((acquisitionTrace [] U).length + 1) []
    (acquisitionTrace [] U) (finiteDecision U) hm (acquisition_foundation.2 U) rfl
  refine ⟨f, ?_⟩
  have eq : rowOfHistory N [] hm = emptyRow N positive := by
    apply row_ext
    · rfl
    · exact row_decode N [] hm
  simpa only [pureObserver, eq] using run


private theorem actual_prefix_original (N : Nat) (positive : 1 ≤ N) (U : Source)
    (allowed : Allowed N U) {e : PureState N} {h : RawHistory}
    (pref : ActualPrefix (pureObserver N positive) U e h) :
    ∃ hm : kappa_hist h ∈ coarsePrefixes N,
      e = .inl (rowOfHistory N h hm) ∧ h.IsPrefix (acquisitionTrace [] U) ∧
      ∃ n t, execute readout acquisitionPolicy n h U = some (t,finiteDecision U) ∧
        h ++ t = acquisitionTrace [] U := by
  induction pref with
  | initial =>
    have hm := empty_mem N positive
    refine ⟨hm, ?_, List.nil_prefix, _, acquisitionTrace [] U,
      acquisition_foundation.2 U, rfl⟩
    change Sum.inl (emptyRow N positive) = Sum.inl (rowOfHistory N [] hm)
    congr 1
  | @query e h q prior row ih =>
    obtain ⟨hm, rfl, pre, n, t, run, full⟩ := ih
    have action : acquisitionPolicy h = .inl q :=
      (action_history N positive U h hm pre).symm.trans row
    have reply : queryReply ((pureObserver N positive).decoder
        (.inl (rowOfHistory N h hm))) q U = readout q U := by
      change queryReply (rowDecoder _) q U = _
      rw [row_decode]
      exact queryReply_eq_readout h U (prefix_truth U pre) q
    cases n with
    | zero => simp [execute] at run
    | succ n =>
      simp only [execute, action] at run
      obtain ⟨⟨s,c⟩, rest, equal⟩ := Option.map_eq_some_iff.mp run
      simp only [Prod.mk.injEq] at equal
      obtain ⟨rfl, rfl⟩ := equal
      let hnext := h ++ [⟨q, readout q U⟩]
      have fullnext : hnext ++ s = acquisitionTrace [] U := by
        simpa only [hnext, List.append_assoc, List.singleton_append] using full
      have prenext : hnext.IsPrefix (acquisitionTrace [] U) := ⟨s, fullnext⟩
      have hmnext := prefix_mem N U allowed prenext
      rw [reply]
      have next := transition_history N positive U h hm q pre action hmnext
      rw [reply] at next
      exact ⟨hmnext, next,
        prenext, n, s, rest, fullnext⟩

/-- At every actual prefix the decoded cache is exactly the original preorder prefix,
with raw truth required only on these actual prefixes. -/
theorem pure_actual_prefix_cache (N : Nat) (positive : 1 ≤ N) (U : Source)
    (allowed : Allowed N U) {e : PureState N} {h : RawHistory}
    (pref : ActualPrefix (pureObserver N positive) U e h) :
    h.IsPrefix (acquisitionTrace [] U) ∧
      (pureObserver N positive).decoder e = h ∧ CacheTruth h U := by
  obtain ⟨hm, rfl, pre, _⟩ := actual_prefix_original N positive U allowed pref
  exact ⟨pre, row_decode N h hm, prefix_truth U pre⟩

private theorem pure_legal (N : Nat) (positive : 1 ≤ N) (U : Source)
    (allowed : Allowed N U) : Legal (pureObserver N positive) U := by
  refine ⟨rfl, ?_⟩
  intro e h pref
  obtain ⟨pre, decoded, truth⟩ := pure_actual_prefix_cache N positive U allowed pref
  refine ⟨?_, ?_⟩
  · rw [decoded]; exact truth
  · intro q row
    have next := pure_actual_prefix_cache N positive U allowed (ActualPrefix.query pref row)
    rw [next.2.1, decoded]
    have fresh : q ∉ h.map Sigma.fst := by
      have nd := (next.1.map Sigma.fst).nodup (trace_nodup U)
      rw [List.map_append, List.nodup_append] at nd
      intro hq
      exact nd.2.2 q hq q (by simp) rfl
    simp only [cacheUpdate, if_neg fresh]
/-- Correct finite acquisition with unrestricted coarse counterfactual control. -/
theorem pure_admissible (N : Nat) (positive : 1 ≤ N) :
    Admissible N (pureObserver N positive) := by
  refine ⟨positive, pure_legal N positive, ?_, pure_all_history_factorization N positive⟩
  intro U allowed
  obtain ⟨f, run⟩ := pure_acquisition_run N positive U allowed
  exact ⟨acquisitionTrace [] U, f, finiteDecision U, run, acquisition_foundation.1 U⟩

/-- Paid addresses are exactly the original actual nodes, rather than all bounded words. -/
private theorem paid_nodes (U : Source) : paid (acquisitionTrace [] U) = (nodes U).toFinset := by
  simp only [paid, trace_addresses, List.nil_append, List.map_id']

/-- The exact node-fee baseline for every allowed source. -/
theorem pure_node_fee (N : Nat) (positive : 1 ≤ N) (tau : Address → ℝ) (U : Source)
    (allowed : Allowed N U) :
    Fee (pureObserver N positive) tau U = ∑ q ∈ (nodes U).toFinset, tau q := by
  obtain ⟨f, run⟩ := pure_acquisition_run N positive U allowed
  rw [fee_run _ tau U run, charge, paid_nodes]

noncomputable def nodeMax (N : Nat) (positive : 1 ≤ N) (tau : Address → ℝ) : ℝ :=
  (allowedSources N).sup' (allowedSources_nonempty N positive)
    (fun U => ∑ q ∈ (nodes U).toFinset, tau q)

private theorem pure_max_fee (N : Nat) (positive : 1 ≤ N) (tau : Address → ℝ) :
    maxFee N (pureObserver N positive) tau = nodeMax N positive tau := by
  classical
  rw [maxFee, dif_pos (allowedSources_nonempty N positive), nodeMax]
  apply Finset.sup'_congr (allowedSources_nonempty N positive) rfl
  intro U hU
  exact pure_node_fee N positive tau U ((allowedSources_exact N U).mp hU)

/-- Exact nominal price plus the attained maximum of actual-node fees. -/
theorem pure_joint_price (N : Nat) (positive : 1 ≤ N) (tau : Address → ℝ) (c : ℝ) :
    J_N N (pureObserver N positive) tau c =
      c * (nominalCard N : ℝ) + nodeMax N positive tau ∧
    ∃ U : Source, Allowed N U ∧ nodeMax N positive tau =
      ∑ q ∈ (nodes U).toFinset, tau q := by
  refine ⟨?_, ?_⟩
  · rw [J_N, pureState_card, pure_max_fee]
  · obtain ⟨U, allowed, attained⟩ :=
      (maximum_exact N positive (pureObserver N positive) tau).2
    rw [pure_max_fee, pure_node_fee N positive tau U allowed] at attained
    exact ⟨U, allowed, attained⟩

private theorem nodes_length (U : Source) (q : Address) (member : q ∈ nodes U) :
    q.length + 1 ≤ U.length := by
  induction U generalizing q with
  | of b =>
    have eq : q = [] := by simpa [nodes] using member
    subst q
    simp
  | mul s t ihs iht =>
    simp only [nodes, List.mem_cons, List.mem_append, List.mem_map] at member
    rcases member with rfl | ⟨v, hv, rfl⟩ | ⟨v, hv, rfl⟩
    · have hs := s.length_pos
      have ht := t.length_pos
      change 0 + 1 ≤ s.length + t.length
      omega
    · have inner := ihs v hv
      have sibling := t.length_pos
      simp only [List.length_cons, FreeMagma.length]
      omega
    · have inner := iht v hv
      have sibling := s.length_pos
      simp only [List.length_cons, FreeMagma.length]
      omega

private theorem coarse_witness (N : Nat) (i : CoarseIndex N) :
    ∃ U : Source, Allowed N U ∧ ∃ h : RawHistory,
      h.IsPrefix (acquisitionTrace [] U) ∧ i.1 = kappa_hist h := by
  classical
  obtain ⟨U, hU, hg⟩ := Finset.mem_biUnion.mp i.2
  have pre : i.1.IsPrefix (kappa_hist (acquisitionTrace [] U)) :=
    (List.mem_inits _ _).mp (List.mem_toFinset.mp hg)
  obtain ⟨h, ph, gh⟩ := List.prefix_map_iff.mp pre
  exact ⟨U, (allowedSources_exact N U).mp hU, h, ph, gh⟩

private theorem pure_native_caches (N : Nat) (positive : 1 ≤ N)
    (e : PureState N) (a : Sigma (fun _ : Address => Reply))
    (member : a ∈ (pureObserver N positive).decoder e) : a.1 ∈ Q_N N := by
  cases e with
  | inr _ => simp [pureObserver] at member
  | inl r =>
    obtain ⟨U, allowed, h, pre, gh⟩ := coarse_witness N r.1
    have addr : a.1 ∈ r.1.1.map Sigma.fst := by
      rw [← decode_addresses r.1.1 r.2]
      exact List.mem_map.mpr ⟨a, member, rfl⟩
    rw [gh] at addr
    have rawaddr : a.1 ∈ h.map Sigma.fst := by
      simpa only [kappa_hist, List.map_map, Function.comp_def] using addr
    have node : a.1 ∈ nodes U := by
      have inTrace := (pre.map Sigma.fst).subset rawaddr
      simpa only [trace_addresses, List.nil_append, List.map_id'] using inTrace
    have bound := nodes_length U a.1 node
    change U.length ≤ N at allowed
    change a.1.length ≤ N - 1
    omega

private theorem pure_native_requests (N : Nat) (positive : 1 ≤ N)
    (e : PureState N) (q : Address)
    (row : (pureObserver N positive).action e = .inl q) : q ∈ Q_N N := by
  cases e with
  | inr _ => simp [pureObserver, pureAction] at row
  | inl r =>
    obtain ⟨U, allowed, h, pre, gh⟩ := coarse_witness N r.1
    obtain ⟨pi, _, _, _, _, _, acquisition, _⟩ :=
      ActualCoarseReadoutCompletion.completion_contract 0 Fin.elim0
        (fun i => Fin.elim0 i) .stop (fun _ => none)
    have act : acquisitionPolicy (encodeHistory (kappa_hist h)) = .inl q := by
      simpa only [pureObserver, pureAction, gh] using row
    obtain ⟨T, present⟩ := (acquisition U h q pre act).1
    have bound := subtree_leaf_count U q T present
    have nonempty := T.length_pos
    change U.length ≤ N at allowed
    change q.length ≤ N - 1
    omega

private theorem pure_card_positive (N : Nat) : 0 < Fintype.card (PureState N) := by
  letI : Nonempty (PureState N) := ⟨.inr ()⟩
  exact Fintype.card_pos

/-- A faithful lawful original table retaining every nominal ghost row and exact prices. -/
noncomputable def lawfulPureTable (N : Nat) (positive : 1 ≤ N) :
    Sigma (fun r : PureState N ≃ Fin (Fintype.card (PureState N)) =>
      {T : NativeTable N (Fintype.card (PureState N)) //
        RepresentationContract N (pureObserver N positive) (pure_card_positive N) r T ∧
        T ∈ lawfulTables N (Fintype.card (PureState N)) (pure_card_positive N)}) := by
  classical
  apply Classical.choice
  obtain ⟨p, r, T, initial, table⟩ := bounded_table_representation N (pureObserver N positive)
    (pure_native_requests N positive) (pure_native_caches N positive)
  have contract := representation_contract N (pureObserver N positive) p r T initial table
  exact ⟨⟨r, T, contract, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
    contract.admissible (pure_admissible N positive)⟩⟩⟩

end D5.S3.Arith.FibonacciAtomic.Observer.ActualPureAcquisitionCompiler
