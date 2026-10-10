/- GID: D5/S3/Arith/FibonacciAtomic/Observer/ActualObserverAbsorbingNormalization
   generality: G
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Full-carrier absorbing normalization of native absent queries. -/

import D5.S3.Arith.FibonacciAtomic.Observer.ActualObserverPairReach
import D5.S3.ObserverMemory.Prediction.FiniteOrbitPeriodBound
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Max

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.Observer.ActualObserverAbsorbingNormalization

universe u
open GenealogicalFiberTransport (Source)
open ActualTreeReadoutAcquisition (Address Reply readout Positive paid)
open ActualCoarseReadoutHistory (kappa kappa_hist)
open ActualFiniteObserverAbsentElimination
open ActualObserverPairReach
open D5.S3.ObserverMemory.Prediction.FiniteOrbitPeriodBound

variable {E : Type u} [Fintype E]

/-- Literal ordered filtering, for both raw traces and nominal decoded caches. -/
def project (N : Nat) (h : RawHistory) : RawHistory :=
  h.filter (fun a => decide (a.1.length ≤ N - 1))

/-- A row is retained precisely when it halts or queries a bounded literal word. -/
def retained (N : Nat) (M : Observer E) (e : E) : Bool :=
  match M.action e with
  | .inl q => decide (q.length ≤ N - 1)
  | .inr _ => true

/-- The construction-time absent successor fixes each retained row. -/
def absentStep (N : Nat) (M : Observer E) (e : E) : E :=
  if retained N M e then e else M.transition e .absent

/-- Scan the first n nominal rows of the static absent orbit. -/
def scan (N : Nat) (M : Observer E) : Nat → E → Option E
  | 0, _ => none
  | n + 1, e => if retained N M e then some e else scan N M n (absentStep N M e)

/-- A finite installed first-exit table, including all unreachable nominal rows. -/
def skip (N : Nat) (M : Observer E) (e : E) : Option E :=
  scan N M (Fintype.card E) e

private theorem orbit_after {N : Nat} {M : Observer E} {e : E} {j : Nat}
    (hit : retained N M ((absentStep N M)^[j] e) = true) {k : Nat} (le : j ≤ k) :
    (absentStep N M)^[k] e = (absentStep N M)^[j] e := by
  have fixed : absentStep N M ((absentStep N M)^[j] e) =
      (absentStep N M)^[j] e := by simp [absentStep, hit]
  rw [← Nat.sub_add_cancel le, Function.iterate_add_apply]
  exact Function.iterate_fixed fixed _

private theorem orbit_hit_unique {N : Nat} {M : Observer E} {e : E} {i j : Nat}
    (hi : retained N M ((absentStep N M)^[i] e) = true)
    (hj : retained N M ((absentStep N M)^[j] e) = true) :
    (absentStep N M)^[i] e = (absentStep N M)^[j] e := by
  rcases le_total i j with h | h
  · exact (orbit_after hi h).symm
  · exact orbit_after hj h

private theorem first_exit_bound (N : Nat) (M : Observer E) (e : E)
    (exists_hit : ∃ j, retained N M ((absentStep N M)^[j] e) = true) :
    ∃ j < Fintype.card E, retained N M ((absentStep N M)^[j] e) = true := by
  let j := Nat.find exists_hit
  have hit : retained N M ((absentStep N M)^[j] e) = true := Nat.find_spec exists_hit
  obtain ⟨mu, p, hp, bound, period⟩ :=
    finite_orbit_and_readout_eventually_periodic (absentStep N M) (M.action) e
  have j_le : j ≤ mu := by
    by_contra bad
    have mu_lt : mu < j := by omega
    let r := max mu (j - p)
    have hr : mu ≤ r := le_max_left _ _
    have r_lt : r < j := by dsimp [r]; omega
    have jr : j ≤ r + p := by dsimp [r]; omega
    have eqn := (period r hr).1
    have at_r : retained N M ((absentStep N M)^[r] e) = true := by
      rw [← eqn, orbit_after hit jr]
      exact hit
    exact (Nat.find_min exists_hit r_lt) at_r
  exact ⟨j, by omega, hit⟩

private theorem scan_sound (N : Nat) (M : Observer E) {n : Nat} {e s : E}
    (found : scan N M n e = some s) :
    ∃ j < n, (absentStep N M)^[j] e = s ∧ retained N M s = true := by
  induction n generalizing e with
  | zero => simp [scan] at found
  | succ n ih =>
    by_cases h : retained N M e = true
    · simp only [scan, h, if_true, Option.some.injEq] at found
      subst s
      exact ⟨0, Nat.zero_lt_succ n, rfl, h⟩
    · simp only [scan, h] at found
      obtain ⟨j, hj, eqn, hit⟩ := ih found
      exact ⟨j + 1, by omega, by simpa only [Function.iterate_succ_apply] using eqn, hit⟩

private theorem scan_hit (N : Nat) (M : Observer E) {n j : Nat} {e : E}
    (lt : j < n) (hit : retained N M ((absentStep N M)^[j] e) = true) :
    scan N M n e = some ((absentStep N M)^[j] e) := by
  induction n generalizing e j with
  | zero => omega
  | succ n ih =>
    by_cases h : retained N M e = true
    · have eqn := orbit_after (j := 0) (by simpa using h) (Nat.zero_le j)
      simpa [scan, h] using congrArg some eqn.symm
    · cases j with
      | zero => simp only [Function.iterate_zero, id_eq] at hit; exact (h hit).elim
      | succ j =>
        simp only [scan, h]
        exact ih (by omega) (by simpa only [Function.iterate_succ_apply] using hit)

private theorem skip_hit (N : Nat) (M : Observer E) {e : E} {j : Nat}
    (hit : retained N M ((absentStep N M)^[j] e) = true) :
    skip N M e = some ((absentStep N M)^[j] e) := by
  obtain ⟨i, hi, hret⟩ := first_exit_bound N M e ⟨j, hit⟩
  rw [skip, scan_hit N M hi hret, orbit_hit_unique hret hit]

private theorem scan_stable (N : Nat) (M : Observer E) {n : Nat} (large : Fintype.card E ≤ n)
    (e : E) : scan N M n e = skip N M e := by
  cases h : scan N M n e with
  | some s =>
    obtain ⟨j, _, eqn, hit⟩ := scan_sound N M h
    rw [← eqn] at hit
    exact (skip_hit N M hit ▸ congrArg some eqn).symm
  | none =>
    cases hs : skip N M e with
    | none => rfl
    | some s =>
      obtain ⟨j, hj, eqn, hit⟩ := scan_sound N M hs
      rw [← eqn] at hit
      have found := scan_hit N M (lt_of_lt_of_le hj large) hit
      rw [h] at found
      contradiction

private theorem skip_retained (N : Nat) (M : Observer E) {e : E}
    (hit : retained N M e = true) : skip N M e = some e :=
  skip_hit N M (j := 0) hit

private theorem skip_removed (N : Nat) (M : Observer E) {e : E}
    (removed : retained N M e ≠ true) :
    skip N M e = skip N M (M.transition e .absent) := by
  have stable := scan_stable N M (n := Fintype.card E + 1) (by omega) e
  simpa [scan, absentStep, removed, skip] using stable.symm

private theorem skip_exact (N : Nat) (M : Observer E) (e : E) :
    (skip N M e = none ↔ ¬ ∃ j, retained N M ((absentStep N M)^[j] e) = true) ∧
    ∀ s, skip N M e = some s → ∃ j < Fintype.card E,
      (absentStep N M)^[j] e = s ∧ retained N M s = true ∧
      ∀ i < j, retained N M ((absentStep N M)^[i] e) ≠ true := by
  constructor
  · constructor
    · intro missing ⟨j, hit⟩
      have found := skip_hit N M hit
      rw [missing] at found
      contradiction
    · intro nohit
      cases hs : skip N M e with
      | none => rfl
      | some s =>
        obtain ⟨j, _, eqn, hit⟩ := scan_sound N M hs
        exact (nohit ⟨j, eqn ▸ hit⟩).elim
  · intro s found
    obtain ⟨k, _, eqn, hit⟩ := scan_sound N M found
    have ex : ∃ j, retained N M ((absentStep N M)^[j] e) = true := ⟨k, eqn ▸ hit⟩
    let j := Nat.find ex
    have first : retained N M ((absentStep N M)^[j] e) = true := Nat.find_spec ex
    obtain ⟨i, bound, hi⟩ := first_exit_bound N M e ex
    have short : j < Fintype.card E := lt_of_le_of_lt (Nat.find_min' ex hi) bound
    have same : (absentStep N M)^[j] e = s :=
      Option.some.inj ((skip_hit N M first).symm.trans found)
    exact ⟨j, short, same, hit, fun i lt => Nat.find_min ex lt⟩

/-- The independently installed native table has exactly the original carrier
and initial row. Every decoder is the literal raw-cache filter. -/
def normalized (N : Nat) (M : Observer E) : Observer E where
  e0 := M.e0
  action e := match skip N M e with | some s => M.action s | none => .inr false
  transition e y := match skip N M e with | some s => M.transition s y | none => e
  decoder e := project N (M.decoder e)
  decoded_nodup e := by
    have sub := (List.filter_sublist (p := fun (a : Sigma (fun _ : Address => Reply)) =>
      decide (a.1.length ≤ N - 1))
      (l := M.decoder e)).map Sigma.fst
    exact (M.decoded_nodup e).sublist sub

private instance bounded_word_decidable (N : Nat) (q : Address) : Decidable (q ∈ Q_N N) :=
  inferInstanceAs (Decidable (q.length ≤ N - 1))

private theorem project_cons (N : Nat) (q : Address) (y : Reply) (t : RawHistory) :
    project N (⟨q, y⟩ :: t) =
      if q ∈ Q_N N then ⟨q, y⟩ :: project N t else project N t := by
  by_cases h : q.length ≤ N - 1 <;> simp [project, Q_N, h]

private theorem project_singleton (N : Nat) (q : Address) (y : Reply) :
    project N [⟨q, y⟩] = if q ∈ Q_N N then [⟨q, y⟩] else [] := by
  rw [project_cons]; rfl

private theorem project_append (N : Nat) (h t : RawHistory) :
    project N (h ++ t) = project N h ++ project N t := List.filter_append _ _

private theorem project_query (N : Nat) (cache : RawHistory) (q : Address)
    (kept : q ∈ Q_N N) (U : Source) :
    queryReply (project N cache) q U = queryReply cache q U := by
  have pred : (fun a : Sigma (fun _ : Address => Reply) =>
      decide (decide (a.1.length ≤ N - 1) = true ∧ (a.1 == q) = true)) = (fun a => a.1 == q) := by
    funext a
    by_cases h : a.1 = q
    · simp [h, show q.length ≤ N - 1 from kept]
    · simp [h]
  simp only [queryReply, project, List.find?_filter, pred]

private theorem project_update (N : Nat) (cache : RawHistory) (q : Address) (y : Reply) :
    project N (cacheUpdate cache q y) =
      if q ∈ Q_N N then cacheUpdate (project N cache) q y else project N cache := by
  classical
  have member (kept : q ∈ Q_N N) :
      q ∈ (project N cache).map Sigma.fst ↔ q ∈ cache.map Sigma.fst := by
    simp only [List.mem_map, project, List.mem_filter, decide_eq_true_eq]
    constructor
    · rintro ⟨a, ⟨ha, _⟩, eqn⟩; exact ⟨a, ha, eqn⟩
    · rintro ⟨a, ha, eqn⟩
      exact ⟨a, ⟨ha, by simpa only [eqn] using (show q.length ≤ N - 1 from kept)⟩, eqn⟩
  by_cases kept : q ∈ Q_N N
  · simp only [if_pos kept, cacheUpdate, member kept]
    split
    · rfl
    · simp [project, List.filter_append, show q.length ≤ N - 1 from kept]
  · simp only [if_neg kept, cacheUpdate]
    split
    · rfl
    · simp [project, List.filter_append, show ¬ q.length ≤ N - 1 from kept]

private theorem removed_query (N : Nat) (M : Observer E) {e : E}
    (removed : retained N M e ≠ true) :
    ∃ q, M.action e = .inl q ∧ q ∉ Q_N N := by
  cases row : M.action e with
  | inl q => exact ⟨q, rfl, by simpa [retained, row, Q_N] using removed⟩
  | inr b => simp [retained, row] at removed

private theorem scan_actual (N : Nat) (M : Observer E) (U : Source)
    (allowed : Allowed N U) (legal : Legal M U)
    {n : Nat} {e s : E} {h : RawHistory} (pref : ActualPrefix M U e h)
    (found : scan N M n e = some s) :
    ∃ hs, ActualPrefix M U s hs ∧ project N hs = project N h ∧
      project N (M.decoder s) = project N (M.decoder e) := by
  induction n generalizing e h with
  | zero => simp [scan] at found
  | succ n ih =>
    by_cases hit : retained N M e = true
    · simp only [scan, hit, if_true, Option.some.injEq] at found
      subst s
      exact ⟨h, pref, rfl, rfl⟩
    · obtain ⟨q, row, outside⟩ := removed_query N M hit
      have reply := (outside_Q_N_absent N U allowed q outside).2
        (M.decoder e) (legal.2 e h pref).1
      have next := ActualPrefix.query pref row
      rw [reply.1] at next
      have upd := (legal.2 e h pref).2 q row
      rw [reply.1] at upd
      have filtered : project N (M.decoder (M.transition e .absent)) =
          project N (M.decoder e) := by
        rw [upd, project_update, if_neg outside]
      simp only [scan, hit, absentStep] at found
      obtain ⟨hs, ps, trace, cache⟩ := ih next found
      refine ⟨hs, ps, ?_, cache.trans filtered⟩
      simpa [project_append, project, show ¬ q.length ≤ N - 1 from outside] using trace

private theorem prefix_suffix (M : Observer E) (U : Source)
    (terminates : ∃ t f b, Run M U M.e0 t f b)
    {e : E} {h : RawHistory} (pref : ActualPrefix M U e h) :
    ∃ t f b, Run M U e t f b := by
  induction pref with
  | initial => exact terminates
  | @query e h q prior row ih =>
    obtain ⟨t, f, b, run⟩ := ih
    cases run with
    | halt other => simp only [row, Sum.inl_ne_inr] at other
    | @query _ f r t b other tail =>
      have eqn := Sum.inl.inj (row.symm.trans other)
      subst r
      exact ⟨t, f, b, tail⟩

private theorem run_exit (N : Nat) (M : Observer E) (U : Source)
    (allowed : Allowed N U) (legal : Legal M U)
    {e f : E} {h t : RawHistory} {b : Bool}
    (pref : ActualPrefix M U e h) (run : Run M U e t f b) :
    ∃ s, skip N M e = some s := by
  induction run generalizing h with
  | halt row => exact ⟨_, skip_retained N M (by simp [retained, row])⟩
  | @query e f q t b row tail ih =>
    by_cases kept : q ∈ Q_N N
    · exact ⟨e, skip_retained N M (by simpa [retained, row, Q_N] using kept)⟩
    · have absent := (outside_Q_N_absent N U allowed q kept).2
        (M.decoder e) (legal.2 e h pref).1
      have rem : retained N M e ≠ true := by simpa [retained, row, Q_N] using kept
      rw [skip_removed N M rem]
      simpa only [absent.1] using ih (ActualPrefix.query pref row)

private theorem entry_transport (N : Nat) (M : Observer E) (U : Source)
    {e s f : E} {t : RawHistory} {b : Bool}
    (same : skip N M e = skip N M s)
    (cache : project N (M.decoder e) = project N (M.decoder s))
    (run : Run (normalized N M) U s t f b) :
    ∃ g, Run (normalized N M) U e t g b ∧
      skip N M g = skip N M f ∧
      project N (M.decoder g) = project N (M.decoder f) := by
  have actions : (normalized N M).action e = (normalized N M).action s := by
    simp only [normalized, same]
  cases run with
  | halt row => exact ⟨e, Run.halt (actions.trans row), same, cache⟩
  | @query s f q t b row tail =>
    have next : ∀ y, (normalized N M).transition e y =
        (normalized N M).transition s y := by
      intro y
      cases hs : skip N M s with
      | some r => simp [normalized, same, hs]
      | none => simp [normalized, hs] at row
    have replies : queryReply ((normalized N M).decoder e) q U =
        queryReply ((normalized N M).decoder s) q U := congrArg (fun c => queryReply c q U) cache
    refine ⟨f, ?_, rfl, rfl⟩
    have newrun := Run.query (U := U) (e := e) (q := q) (t := t) (f := f) (b := b)
      (actions.trans row) (by simpa only [replies, next] using tail)
    simpa only [replies] using newrun

/-- Native execution of the independently installed table deletes precisely the
outside reports. The final entry need not be the old halt; its skip is that halt. -/
theorem normalize_run_from_actual_prefix (N : Nat) (M : Observer E) (U : Source)
    (allowed : Allowed N U) (legal : Legal M U)
    {e f : E} {h t : RawHistory} {b : Bool}
    (pref : ActualPrefix M U e h) (run : Run M U e t f b) :
    ∃ g, Run (normalized N M) U e (project N t) g b ∧
      skip N M g = some f ∧ project N (M.decoder g) = project N (M.decoder f) := by
  induction run generalizing h with
  | @halt e b row =>
    have hs := skip_retained N M (e := e) (by simp [retained, row])
    exact ⟨_, Run.halt (by simp [normalized, hs, row]), hs, rfl⟩
  | @query e f q t b row tail ih =>
    obtain ⟨g, newrun, final, cache⟩ := ih (ActualPrefix.query pref row)
    by_cases kept : q ∈ Q_N N
    · have hs := skip_retained N M (e := e) (by simpa [retained, row, Q_N] using kept)
      have reply := project_query N (M.decoder e) q kept U
      refine ⟨g, ?_, final, cache⟩
      rw [project_cons, if_pos kept]
      simpa only [normalized, hs, reply] using
        (Run.query (M := normalized N M) (U := U) (e := e) (q := q)
          (t := project N t) (f := g) (b := b) (by simp [normalized, hs, row])
          (by simpa [normalized, hs, reply] using newrun))
    · have absent := (outside_Q_N_absent N U allowed q kept).2
        (M.decoder e) (legal.2 e h pref).1
      have rem : retained N M e ≠ true := by simpa [retained, row, Q_N] using kept
      have eqcache : project N (M.decoder e) =
          project N (M.decoder (M.transition e .absent)) := by
        have upd := (legal.2 e h pref).2 q row
        rw [absent.1] at upd
        rw [upd, project_update, if_neg kept]
      rw [absent.1] at newrun
      obtain ⟨g', moved, sf, cf⟩ := entry_transport N M U (skip_removed N M rem) eqcache newrun
      refine ⟨g', ?_, sf.trans final, cf.trans cache⟩
      rw [project_cons, if_neg kept]
      exact moved

private theorem scan_pair (N : Nat) (M : Observer E) (inv : pairActionInvariant M)
    {e f : E} (prior : PairReach M e f) (n : Nat) :
    match scan N M n e, scan N M n f with
    | some s, some t => PairReach M s t
    | none, none => True
    | _, _ => False := by
  induction n generalizing e f with
  | zero => trivial
  | succ n ih =>
    have actions := inv prior
    have same : retained N M e = retained N M f := by simp only [retained, actions]
    by_cases hit : retained N M e = true
    · simp only [scan, hit, ← same, if_true]
      exact prior
    · simp only [scan, hit, ← same]
      obtain ⟨q, row, _⟩ := removed_query N M hit
      have pair := PairReach.step prior (y := Reply.absent) (z := Reply.absent) rfl
      have step : PairReach M (absentStep N M e) (absentStep N M f) := by
        simpa [absentStep, hit, ← same, barStep, ← actions, row] using pair
      exact ih step

private theorem pair_actions (N : Nat) (M : Observer E) (inv : pairActionInvariant M)
    {e f : E} (prior : PairReach M e f) :
    (normalized N M).action e = (normalized N M).action f := by
  have related := scan_pair N M inv prior (Fintype.card E)
  change match skip N M e, skip N M f with
    | some s, some t => PairReach M s t
    | none, none => True
    | _, _ => False at related
  cases he : skip N M e <;> cases hf : skip N M f <;>
    simp only [he, hf] at related
  · simp [normalized, he, hf]
  · simp only [normalized, he, hf]
    exact inv related

private theorem pair_step (N : Nat) (M : Observer E) (inv : pairActionInvariant M)
    {e f : E} (prior : PairReach M e f) {y z : Reply} (same : kappa y = kappa z) :
    PairReach M (barStep (normalized N M) e y) (barStep (normalized N M) f z) := by
  have related := scan_pair N M inv prior (Fintype.card E)
  change match skip N M e, skip N M f with
    | some s, some t => PairReach M s t
    | none, none => True
    | _, _ => False at related
  cases he : skip N M e <;> cases hf : skip N M f <;>
    simp only [he, hf] at related
  · simpa [barStep, normalized, he, hf] using prior
  · rename_i s t
    have actions := inv related
    cases row : M.action s with
    | inl q =>
      have pair := PairReach.step related same
      simpa [barStep, normalized, he, hf, ← actions, row] using pair
    | inr b => simpa [barStep, normalized, he, hf, ← actions, row] using prior

/-- Universal pair transport uses all four raw replies, including inconsistent,
wrong-address and posthalt histories; it has no actual-source restriction. -/
theorem normalized_pair_transport (N : Nat) (M : Observer E)
    (coarse : Function.FactorsThrough (historyAction M) kappa_hist) :
    (∀ {e f : E}, PairReach (normalized N M) e f → PairReach M e f) ∧
    Function.FactorsThrough (historyAction (normalized N M)) kappa_hist := by
  have inv : pairActionInvariant M :=
    (pairActionInvariant_iff_allHistoryFactorization M).mpr coarse
  have transport : ∀ {e f : E}, PairReach (normalized N M) e f → PairReach M e f := by
    intro e f reached
    induction reached with
    | initial => exact PairReach.initial
    | step prior same ih => exact pair_step N M inv ih same
  exact ⟨transport, (pairActionInvariant_iff_allHistoryFactorization _).mp
    (fun reached => pair_actions N M inv (transport reached))⟩

private theorem old_prefix_projection (N : Nat) (M : Observer E) (U : Source)
    (allowed : Allowed N U) (legal : Legal M U)
    {e : E} {h : RawHistory} (pref : ActualPrefix M U e h) :
    ∃ g, ActualPrefix (normalized N M) U g (project N h) ∧
      skip N M g = skip N M e ∧
      (normalized N M).decoder g = project N (M.decoder e) := by
  induction pref with
  | initial => exact ⟨M.e0, ActualPrefix.initial, rfl, rfl⟩
  | @query e h q prior row ih =>
    obtain ⟨g, pg, skips, caches⟩ := ih
    change project N (M.decoder g) = project N (M.decoder e) at caches
    by_cases kept : q ∈ Q_N N
    · have hs := skip_retained N M (e := e) (by simpa [retained, row, Q_N] using kept)
      have sg := skips.trans hs
      have reply : queryReply (project N (M.decoder g)) q U =
          queryReply (M.decoder e) q U := by rw [caches, project_query N _ q kept U]
      have next := ActualPrefix.query pg (q := q) (by simp [normalized, sg, row])
      refine ⟨M.transition e (queryReply (M.decoder e) q U), ?_, rfl, rfl⟩
      rw [project_append, project_singleton, if_pos kept]
      simpa only [reply, normalized, sg] using next
    · have rem : retained N M e ≠ true := by simpa [retained, row, Q_N] using kept
      have absent := (outside_Q_N_absent N U allowed q kept).2
        (M.decoder e) (legal.2 e h prior).1
      refine ⟨g, ?_, ?_, ?_⟩
      · simpa [project_append, project, show ¬ q.length ≤ N - 1 from kept] using pg
      · rw [absent.1]
        exact skips.trans (skip_removed N M rem)
      · rw [(legal.2 e h prior).2 q row, project_update, if_neg kept]
        exact caches

private theorem new_prefix_lift (N : Nat) (M : Observer E) (admissible : Admissible N M)
    (U : Source) (allowed : Allowed N U)
    {e : E} {h : RawHistory} (pref : ActualPrefix (normalized N M) U e h) :
    ∃ old, ActualPrefix M U e old ∧ project N old = h := by
  have legal := admissible.legal U allowed
  have terminates : ∃ t f b, Run M U M.e0 t f b := by
    obtain ⟨t, f, b, run, _⟩ := admissible.correct U allowed
    exact ⟨t, f, b, run⟩
  induction pref with
  | initial => exact ⟨[], ActualPrefix.initial, rfl⟩
  | @query e h q prior row ih =>
    obtain ⟨old, pe, proj⟩ := ih
    obtain ⟨t, f, b, run⟩ := prefix_suffix M U terminates pe
    obtain ⟨s, hs⟩ := run_exit N M U allowed legal pe run
    have oldrow : M.action s = .inl q := by simpa [normalized, hs] using row
    obtain ⟨old', ps, traces, caches⟩ := scan_actual N M U allowed legal pe hs
    obtain ⟨_, _, _, hit⟩ := scan_sound N M hs
    have kept : q ∈ Q_N N := by simpa [retained, oldrow, Q_N] using hit
    have reply : queryReply (project N (M.decoder e)) q U =
        queryReply (M.decoder s) q U := by
      rw [← caches, project_query N _ q kept U]
    refine ⟨old' ++ [⟨q, queryReply (M.decoder s) q U⟩], ?_, ?_⟩
    · simpa only [normalized, hs, reply] using ActualPrefix.query ps oldrow
    · rw [project_append, project_singleton, if_pos kept, traces, proj]
      change h ++ [⟨q, queryReply (M.decoder s) q U⟩] =
        h ++ [⟨q, queryReply (project N (M.decoder e)) q U⟩]
      rw [reply]

private theorem normalized_legal (N : Nat) (M : Observer E) (admissible : Admissible N M)
    (U : Source) (allowed : Allowed N U) : Legal (normalized N M) U := by
  have legal := admissible.legal U allowed
  refine ⟨by simp [normalized, legal.1, project], ?_⟩
  intro e h pref
  obtain ⟨old, pe, _⟩ := new_prefix_lift N M admissible U allowed pref
  refine ⟨?_, ?_⟩
  · intro a member
    exact (legal.2 e old pe).1 a (List.mem_filter.mp member).1
  · intro q row
    obtain ⟨t, f, b, run, _⟩ := admissible.correct U allowed
    obtain ⟨t', f', b', rest⟩ := prefix_suffix M U ⟨t, f, b, run⟩ pe
    obtain ⟨s, hs⟩ := run_exit N M U allowed legal pe rest
    obtain ⟨old', ps, _, caches⟩ := scan_actual N M U allowed legal pe hs
    have oldrow : M.action s = .inl q := by simpa [normalized, hs] using row
    obtain ⟨_, _, _, hit⟩ := scan_sound N M hs
    have kept : q ∈ Q_N N := by simpa [retained, oldrow, Q_N] using hit
    have reply : queryReply (project N (M.decoder e)) q U =
        queryReply (M.decoder s) q U := by rw [← caches, project_query N _ q kept U]
    change project N (M.decoder ((normalized N M).transition e
      (queryReply (project N (M.decoder e)) q U))) = _
    rw [show (normalized N M).transition e (queryReply (project N (M.decoder e)) q U) =
      M.transition s (queryReply (M.decoder s) q U) by simp [normalized, hs, reply]]
    rw [(legal.2 s old' ps).2 q oldrow, project_update, if_pos kept, caches, ← reply]
    rfl

/-- Each original literal address is charged once, irrespective of repetitions. -/
def charge (tau : Address → ℝ) (t : RawHistory) : ℝ := ∑ q ∈ paid t, tau q

/-- The unique terminating native run determines the fee. The default is used
only for tables without a terminating run on this source. -/
noncomputable def Fee (M : Observer E) (tau : Address → ℝ) (U : Source) : ℝ := by
  classical
  exact if total : ∃ t f b, Run M U M.e0 t f b then charge tau total.choose else 0

/-- Enumerate all original bounded sources using the existing finite fibers. -/
noncomputable def allowedSources (N : Nat) : Finset Source := by
  classical
  exact (ActualTreeReadoutAcquisition.boundedSources N).filter (Allowed N)

theorem composition_total (T : Source) :
    (GenealogicalFiberTransport.composition T).1 +
      (GenealogicalFiberTransport.composition T).2 = T.length := by
  let total : Source →ₙ* Multiplicative Nat :=
    { toFun := fun t => Multiplicative.ofAdd
        ((GenealogicalFiberTransport.composition t).1 +
          (GenealogicalFiberTransport.composition t).2)
      map_mul' := by
        intro s t
        change ((GenealogicalFiberTransport.composition s).1 +
          (GenealogicalFiberTransport.composition t).1) +
          ((GenealogicalFiberTransport.composition s).2 +
          (GenealogicalFiberTransport.composition t).2) =
          ((GenealogicalFiberTransport.composition s).1 +
          (GenealogicalFiberTransport.composition s).2) +
          ((GenealogicalFiberTransport.composition t).1 +
          (GenealogicalFiberTransport.composition t).2)
        omega }
  let len : Source →ₙ* Multiplicative Nat :=
    { toFun := fun t => Multiplicative.ofAdd t.length, map_mul' := fun _ _ => rfl }
  have equal : total = len := FreeMagma.hom_ext (by
    funext b
    cases b <;> rfl)
  exact congrArg Multiplicative.toAdd (DFunLike.congr_fun equal T)

theorem allowedSources_exact (N : Nat) (U : Source) :
    U ∈ allowedSources N ↔ Allowed N U := by
  classical
  refine ⟨fun h => (Finset.mem_filter.mp h).2, fun allowed => ?_⟩
  refine Finset.mem_filter.mpr ⟨?_, allowed⟩
  let a := (GenealogicalFiberTransport.composition U).1
  let b := (GenealogicalFiberTransport.composition U).2
  have bound : a + b ≤ N := by
    simpa only [a, b, composition_total] using (show U.length ≤ N from allowed)
  let (a b : Nat) : Fintype {t : Source //
      GenealogicalFiberTransport.composition t = (a, b)} :=
    GenealogicalFiberTransport.fiberFintype (a, b)
  change U ∈ (Finset.range (N + 1)).biUnion (fun a =>
    (Finset.range (N + 1 - a)).biUnion (fun b =>
      (Finset.univ : Finset (GenealogicalFiberTransport.Fiber (a, b))).image Subtype.val))
  refine Finset.mem_biUnion.mpr ⟨a, Finset.mem_range.mpr (by omega), ?_⟩
  refine Finset.mem_biUnion.mpr ⟨b, Finset.mem_range.mpr (by omega), ?_⟩
  exact Finset.mem_image.mpr ⟨⟨U, rfl⟩, Finset.mem_univ _, rfl⟩

theorem allowedSources_nonempty (N : Nat) (positive : 1 ≤ N) :
    (allowedSources N).Nonempty :=
  ⟨.of true, (allowedSources_exact N _).mpr positive⟩

/-- The attained finite maximum over exactly the original allowed source domain. -/
noncomputable def maxFee (N : Nat) (M : Observer E) (tau : Address → ℝ) : ℝ :=
  if nonempty : (allowedSources N).Nonempty then
    (allowedSources N).sup' nonempty (Fee M tau) else 0

/-- Full nominal-state price plus the same-source attained worst fee. -/
noncomputable def J_N (N : Nat) (M : Observer E) (tau : Address → ℝ) (kappa : ℝ) : ℝ :=
  kappa * (Fintype.card E : ℝ) + maxFee N M tau

theorem fee_run (M : Observer E) (tau : Address → ℝ) (U : Source)
    {t : RawHistory} {f : E} {b : Bool} (run : Run M U M.e0 t f b) :
    Fee M tau U = charge tau t := by
  have total : ∃ s g c, Run M U M.e0 s g c := ⟨t, f, b, run⟩
  rw [Fee, dif_pos total]
  obtain ⟨g, c, chosen⟩ := total.choose_spec
  rw [(run_deterministic M U chosen run).1]

private theorem charge_projection (N : Nat) (tau : Address → ℝ)
    (nonneg : ∀ q, 0 ≤ tau q) (t : RawHistory) :
    paid (project N t) = (paid t).filter (fun q => q ∈ Q_N N) ∧
    charge tau (project N t) ≤ charge tau t := by
  classical
  have paid_eq : paid (project N t) = (paid t).filter (fun q => q ∈ Q_N N) := by
    ext q
    simp only [paid, List.mem_toFinset, List.mem_map, project, List.mem_filter,
      decide_eq_true_eq, Finset.mem_filter]
    constructor
    · rintro ⟨a, ⟨ha, kept⟩, eqn⟩
      exact ⟨⟨a, ha, eqn⟩, by simpa only [eqn, Q_N, Set.mem_ofPred_eq] using kept⟩
    · rintro ⟨⟨a, ha, eqn⟩, kept⟩
      exact ⟨a, ⟨ha, by simpa only [eqn, Q_N, Set.mem_ofPred_eq] using kept⟩, eqn⟩
  refine ⟨paid_eq, ?_⟩
  unfold charge
  rw [paid_eq]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun q _ _ => nonneg q)

theorem maximum_exact (N : Nat) (positive : 1 ≤ N) (M : Observer E)
    (tau : Address → ℝ) :
    (∀ U, Allowed N U → Fee M tau U ≤ maxFee N M tau) ∧
    ∃ U, Allowed N U ∧ maxFee N M tau = Fee M tau U := by
  have ne := allowedSources_nonempty N positive
  simp only [maxFee, dif_pos ne]
  constructor
  · intro U allowed
    exact Finset.le_sup' (Fee M tau) ((allowedSources_exact N U).mpr allowed)
  · obtain ⟨U, member, eqn⟩ := Finset.exists_mem_eq_sup' ne (Fee M tau)
    exact ⟨U, (allowedSources_exact N U).mp member, eqn⟩

private theorem normalized_admissible (N : Nat) (M : Observer E)
    (admissible : Admissible N M) : Admissible N (normalized N M) := by
  refine ⟨admissible.budget_pos, normalized_legal N M admissible, ?_,
    (normalized_pair_transport N M admissible.coarse).2⟩
  intro U allowed
  obtain ⟨t, f, b, run, correct⟩ := admissible.correct U allowed
  obtain ⟨g, newrun, _, _⟩ := normalize_run_from_actual_prefix N M U allowed
    (admissible.legal U allowed) ActualPrefix.initial run
  exact ⟨project N t, g, b, newrun, correct⟩

private theorem sourcewise_domination (N : Nat) (M : Observer E)
    (admissible : Admissible N M) (tau : Address → ℝ) (nonneg : ∀ q, 0 ≤ tau q)
    (U : Source) (allowed : Allowed N U) :
    Fee (normalized N M) tau U ≤ Fee M tau U := by
  obtain ⟨t, f, b, run, _⟩ := admissible.correct U allowed
  obtain ⟨g, newrun, _, _⟩ := normalize_run_from_actual_prefix N M U allowed
    (admissible.legal U allowed) ActualPrefix.initial run
  rw [fee_run M tau U run, fee_run (normalized N M) tau U newrun]
  exact (charge_projection N tau nonneg t).2

private theorem joint_domination (N : Nat) (M : Observer E) (admissible : Admissible N M)
    (tau : Address → ℝ) (nonneg : ∀ q, 0 ≤ tau q) (kappa : ℝ) :
    J_N N (normalized N M) tau kappa ≤ J_N N M tau kappa := by
  have max_old := (maximum_exact N admissible.budget_pos M tau).1
  have max_new := (maximum_exact N admissible.budget_pos (normalized N M) tau).2
  obtain ⟨U, allowed, attained⟩ := max_new
  unfold J_N
  have fees : maxFee N (normalized N M) tau ≤ maxFee N M tau := by
    rw [attained]
    exact (sourcewise_domination N M admissible tau nonneg U allowed).trans
      (max_old U allowed)
  exact add_le_add le_rfl fees

def sourceStep (M : Observer E) (U : Source) (e : E) : E :=
  match M.action e with
  | .inl q => M.transition e (queryReply (M.decoder e) q U)
  | .inr _ => e

theorem run_orbit (M : Observer E) (U : Source)
    {e f : E} {t : RawHistory} {b : Bool} (run : Run M U e t f b) :
    (sourceStep M U)^[t.length] e = f ∧ M.action f = .inr b ∧
    ∀ i < t.length, ∃ q, M.action ((sourceStep M U)^[i] e) = .inl q := by
  induction run with
  | halt row => exact ⟨rfl, row, by simp⟩
  | @query e f q t b row tail ih =>
    refine ⟨?_, ih.2.1, ?_⟩
    · simpa only [List.length_cons, Function.iterate_succ_apply, sourceStep, row] using ih.1
    · intro i hi
      cases i with
      | zero => exact ⟨q, row⟩
      | succ i =>
        simpa only [Function.iterate_succ_apply, sourceStep, row] using ih.2.2 i (by simpa using hi)

theorem run_length_bound (M : Observer E) (U : Source)
    {e f : E} {t : RawHistory} {b : Bool} (run : Run M U e t f b) :
    t.length < Fintype.card E := by
  obtain ⟨terminal, halt, before⟩ := run_orbit M U run
  obtain ⟨mu, p, hp, bound, period⟩ :=
    finite_orbit_and_readout_eventually_periodic (sourceStep M U) M.action e
  have at_after {k : Nat} (le : t.length ≤ k) : (sourceStep M U)^[k] e = f := by
    rw [← Nat.sub_add_cancel le, Function.iterate_add_apply, terminal]
    exact Function.iterate_fixed (by simp [sourceStep, halt]) _
  have len_le : t.length ≤ mu := by
    by_contra bad
    let r := max mu (t.length - p)
    have hr : mu ≤ r := le_max_left _ _
    have lt : r < t.length := by dsimp [r]; omega
    have after : t.length ≤ r + p := by dsimp [r]; omega
    have equal := (period r hr).1
    rw [at_after after] at equal
    obtain ⟨q, query⟩ := before r lt
    rw [← equal, halt] at query
    contradiction
  omega

/-- All clauses concern the original source, literal raw histories and complete
nominal carrier. Correspondence and domination are conclusions, not ports. -/
structure NormalizationContract (N : Nat) (M H : Observer E) : Prop where
  initial : H.e0 = M.e0
  static_scan : ∀ e,
    (skip N M e = none ↔ ¬ ∃ j, retained N M ((absentStep N M)^[j] e) = true) ∧
    ∀ s, skip N M e = some s → ∃ j < Fintype.card E,
      (absentStep N M)^[j] e = s ∧ retained N M s = true ∧
      ∀ i < j, retained N M ((absentStep N M)^[i] e) ≠ true
  fallback : ∀ e, skip N M e = none →
    H.action e = .inr false ∧ ∀ y, H.transition e y = e
  decoder : ∀ e, H.decoder e = project N (M.decoder e) ∧
    (H.decoder e).Sublist (M.decoder e)
  requests : ∀ e q, H.action e = .inl q → q ∈ Q_N N
  admissible : Admissible N H
  old_prefix : ∀ U, Allowed N U → ∀ e h, ActualPrefix M U e h →
    ∃ g, ActualPrefix H U g (project N h) ∧ skip N M g = skip N M e ∧
      H.decoder g = project N (M.decoder e)
  new_prefix : ∀ U, Allowed N U → ∀ e h, ActualPrefix H U e h →
    ∃ old, ActualPrefix M U e old ∧ project N old = h
  old_run : ∀ U, Allowed N U → ∀ t f b, Run M U M.e0 t f b →
    ∃ g, Run H U H.e0 (project N t) g b ∧ skip N M g = some f ∧
      H.decoder g = project N (M.decoder f) ∧ t.length < Fintype.card E
  new_run : ∀ U, Allowed N U → ∀ s g b, Run H U H.e0 s g b →
    ∃ t f, Run M U M.e0 t f b ∧ s = project N t ∧ skip N M g = some f ∧
      H.decoder g = project N (M.decoder f)
  pairs : ∀ e f, PairReach H e f → PairReach M e f
  source_domain : ∀ U, U ∈ allowedSources N ↔ Allowed N U
  prices : ∀ tau : Address → ℝ, (∀ q, 0 ≤ tau q) →
    (∀ U, Allowed N U → Fee H tau U ≤ Fee M tau U) ∧
    (∃ U, Allowed N U ∧ maxFee N M tau = Fee M tau U) ∧
    (∃ U, Allowed N U ∧ maxFee N H tau = Fee H tau U) ∧
    ∀ kappa : ℝ, 0 < kappa → J_N N H tau kappa ≤ J_N N M tau kappa

/-- Every admissible original observer has a complete native normalization on
exactly the same E and e0, with ordered traces, every-prefix legality, raw cache
projection, unrestricted pair transport and attained original price domination. -/
theorem absent_normalization_contract (N : Nat) (M : Observer E)
    (admissible : Admissible N M) :
    ∃ H : Observer E, H = normalized N M ∧ NormalizationContract N M H := by
  refine ⟨normalized N M, rfl, ?_⟩
  refine ⟨rfl, skip_exact N M, ?_, ?_, ?_, normalized_admissible N M admissible, ?_, ?_, ?_, ?_,
    ?_, allowedSources_exact N, ?_⟩
  · intro e missing
    exact ⟨by simp [normalized, missing], fun y => by simp [normalized, missing]⟩
  · intro e
    exact ⟨rfl, List.filter_sublist⟩
  · intro e q row
    cases hs : skip N M e with
    | none => simp [normalized, hs] at row
    | some s =>
      obtain ⟨_, _, _, hit⟩ := scan_sound N M hs
      have oldrow : M.action s = .inl q := by simpa [normalized, hs] using row
      simpa [retained, oldrow, Q_N] using hit
  · intro U allowed e h pref
    exact old_prefix_projection N M U allowed (admissible.legal U allowed) pref
  · intro U allowed e h pref
    exact new_prefix_lift N M admissible U allowed pref
  · intro U allowed t f b run
    obtain ⟨g, nr, final, cache⟩ := normalize_run_from_actual_prefix N M U allowed
      (admissible.legal U allowed) ActualPrefix.initial run
    exact ⟨g, nr, final, cache, run_length_bound M U run⟩
  · intro U allowed s g b nr
    obtain ⟨t, f, c, run, _⟩ := admissible.correct U allowed
    obtain ⟨g', simrun, final, cache⟩ := normalize_run_from_actual_prefix N M U allowed
      (admissible.legal U allowed) ActualPrefix.initial run
    obtain ⟨traces, finals, bits⟩ := run_deterministic (normalized N M) U nr simrun
    subst g'
    subst c
    exact ⟨t, f, run, traces, final, cache⟩
  · intro e f pair
    exact (normalized_pair_transport N M admissible.coarse).1 pair
  · intro tau nonneg
    exact ⟨sourcewise_domination N M admissible tau nonneg,
      (maximum_exact N admissible.budget_pos M tau).2,
      (maximum_exact N admissible.budget_pos (normalized N M) tau).2,
      fun kappa _ => joint_domination N M admissible tau nonneg kappa⟩

end D5.S3.Arith.FibonacciAtomic.Observer.ActualObserverAbsorbingNormalization
