/- GID: D5/S3/Arith/FibonacciAtomic/Observer/ActualExactMarkedTables
   generality: G
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Original marks, primitive prefix checks and attained full-carrier exact minima. -/

import D5.S3.Arith.FibonacciAtomic.Observer.ActualObserverPrefixRigidity
import D5.S3.Arith.FibonacciAtomic.Observer.ActualCompletionPhaseReplay
import D5.S3.Arith.FibonacciAtomic.Observer.ActualCompletionHorizon
import D5.S3.Arith.FibonacciAtomic.Observer.ActualObserverFiniteChecks
import Mathlib.Data.Finset.Max

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.Observer.ActualExactMarkedTables

universe u
open GenealogicalFiberTransport (Source)
open ActualTreeReadoutAcquisition (Address Reply Strategy terminal readout paid)
open ActualCoarseReadoutHistory (kappa kappa_hist)
open ActualFiniteObserverAbsentElimination
open ActualObserverPrefixRigidity
open ActualExactSupportPruning
open ActualExactTraceCompiler
open ActualCompletionPhaseReplay
open ActualObserverBoundedLowerBounds (bounded_cache_control_lower_bounds)
open ActualObserverFiniteChecks (sourceCheck sourceCheck_iff)
open ActualObserverPairReach
open ActualObserverFiniteTable
open ActualObserverAbsorbingNormalization
open D5.S3.ConceptDynamics.Experiment.PassiveAdaptiveTranscriptUpperBound (PassiveProtocol)

variable {E : Type u} [Fintype E]

/-- Finite original phase observations, with malformed as the fixed ghost default. -/
abbrev PhaseMark {m : Nat} (F : Fin m → Source)
    (decode : CoarseHistory → Option (Fin m))
    (p : PassiveProtocol Address (fun _ => Option Bool)) (N : Nat) (π : Strategy) :=
  {label : PhaseLabel m // label ∈ insert .malformed (phaseAlphabet F decode p N π)}

/-- Only allowed actual prefixes prescribe the original parser's label. -/
def OriginalMarks {m : Nat} (F : Fin m → Source)
    (decode : CoarseHistory → Option (Fin m))
    (p : PassiveProtocol Address (fun _ => Option Bool)) (N : Nat)
    (M : Observer E) (mark : E → PhaseLabel m) : Prop :=
  ∀ U, Allowed N U → ∀ e h, ActualPrefix M U e h →
    mark e = (routePhase F decode p [] (kappa_hist h)).1

/-- Every exact competitor admits the concrete original labels on its existing
complete carrier. The observer, including unused nominal rows, is unchanged. -/
theorem same_carrier_original_marking {m : Nat} (F : Fin m → Source)
    (decode : CoarseHistory → Option (Fin m))
    (p : PassiveProtocol Address (fun _ => Option Bool)) (N : Nat) (π : Strategy)
    (M : Observer E) (admissible : Admissible N M) (exact : ExactTraces N π M) :
    ∃ mark : E → PhaseMark F decode p N π,
      OriginalMarks F decode p N M (fun e => (mark e).val) := by
  classical
  let visited (e : E) := ∃ h : RawHistory, ∃ U : Source,
    Allowed N U ∧ ActualPrefix M U e h
  have range (e : E) (visit : visited e) :
      (routePhase F decode p [] (kappa_hist visit.choose)).1 ∈
        phaseAlphabet F decode p N π := by
    obtain ⟨U, allowed, pref⟩ := visit.choose_spec
    obtain ⟨f, run⟩ := exact U allowed
    obtain ⟨s, _, equation⟩ := prefix_run_tail M U pref run
    exact Finset.mem_image.mpr ⟨kappa_hist visit.choose,
      strategy_prefix_mem N π allowed ⟨s, equation⟩, rfl⟩
  let mark (e : E) : PhaseMark F decode p N π :=
    if visit : visited e then
      ⟨(routePhase F decode p [] (kappa_hist visit.choose)).1,
        Finset.mem_insert_of_mem (range e visit)⟩
    else ⟨.malformed, Finset.mem_insert_self _ _⟩
  refine ⟨mark, ?_⟩
  intro U allowed e h pref
  have visit : visited e := ⟨h, U, allowed, pref⟩
  obtain ⟨V, allowedV, chosen⟩ := visit.choose_spec
  obtain ⟨f, runV⟩ := exact V allowedV
  have same := actualPrefix_history_rigid M U V (admissible.legal U allowed)
    pref chosen ((admissible.legal V allowedV).2 e _ chosen).1 runV
  simp only [mark, dif_pos visit, same]

/-- Primitive row tests at every prescribed prefix, including zero and the full
terminal prefix. The successors and cache updates are literal row equalities. -/
def PrefixCertificate (M : Observer E) (U : Source) (t : RawHistory) (b : Bool) : Prop :=
  (∀ j : Fin (t.length + 1),
    M.decoder (historyState M (t.take j.val)) = firstRaw (t.take j.val)) ∧
  (∀ j : Fin t.length,
    let a := t[j.val]
    let e := historyState M (t.take j.val)
    M.action e = .inl a.1 ∧ queryReply (M.decoder e) a.1 U = a.2 ∧
    historyState M (t.take (j.val + 1)) = M.transition e a.2 ∧
    M.decoder (M.transition e a.2) = cacheUpdate (M.decoder e) a.1 a.2) ∧
  M.action (historyState M t) = .inr b

/-- A closed finite pair set checks all coarse-equal raw reply pairs. Impossible
replies and contradictory cached hits are deliberately retained. -/
def PairCertificate (M : Observer E) : Prop :=
  ∃ R : Finset (E × E), (M.e0, M.e0) ∈ R ∧
    (∀ a ∈ R, M.action a.1 = M.action a.2) ∧
    ∀ a ∈ R, ∀ y z : Reply, kappa y = kappa z →
      (barStep M a.1 y, barStep M a.2 z) ∈ R

private theorem pair_certificate_iff (M : Observer E) :
    PairCertificate M ↔ Function.FactorsThrough (historyAction M) kappa_hist := by
  classical
  rw [← pairActionInvariant_iff_allHistoryFactorization]
  constructor
  · rintro ⟨R, initial, actions, closed⟩ e f reached
    apply actions (e, f)
    induction reached with
    | initial => exact initial
    | step prior equal ih => exact closed _ ih _ _ equal
  · intro invariant
    let R := Finset.univ.filter (fun a : E × E => PairReach M a.1 a.2)
    refine ⟨R, by simp [R, PairReach.initial], ?_, ?_⟩
    · intro a member
      exact invariant (Finset.mem_filter.mp member).2
    · intro a member y z equal
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        PairReach.step (Finset.mem_filter.mp member).2 equal⟩

private theorem certificate_prefixes (M : Observer E) (U : Source)
    (t : RawHistory) (b : Bool) (certificate : PrefixCertificate M U t b) :
    ∀ j ≤ t.length, ActualPrefix M U (historyState M (t.take j)) (t.take j) := by
  intro j bound
  induction j with
  | zero => exact ActualPrefix.initial
  | succ j ih =>
      have before : j < t.length := by omega
      have prior := ih (by omega)
      have guard := certificate.2.1 ⟨j, before⟩
      dsimp only at guard
      have next := ActualPrefix.query prior guard.1
      rw [guard.2.1] at next
      rw [← guard.2.2.1] at next
      simpa only [List.take_succ_eq_append_getElem before] using next

private theorem certificate_exact (M : Observer E) (U : Source)
    (t : RawHistory) (b : Bool) (certificate : PrefixCertificate M U t b)
    (checked : sourceCheck M U = true) : ∃ f, Run M U M.e0 t f b := by
  obtain ⟨_, s, f, c, run, _⟩ := (sourceCheck_iff M U).mp checked
  have pref := certificate_prefixes M U t b certificate t.length (le_refl _)
  simp only [List.take_length] at pref
  obtain ⟨r, rest, equation⟩ := prefix_run_tail M U pref run
  obtain ⟨trace, finish, bit⟩ := run_deterministic M U (Run.halt certificate.2.2) rest
  have same : t = s := by simpa only [← trace, List.append_nil] using equation
  exact ⟨f, by simpa only [same, bit] using run⟩

private theorem run_query_row (M : Observer E) (U : Source)
    {t : RawHistory} {f : E} {b : Bool} (run : Run M U M.e0 t f b)
    (j : Fin t.length)
    (pref : ActualPrefix M U (historyState M (t.take j.val)) (t.take j.val)) :
    M.action (historyState M (t.take j.val)) = .inl (t[j.val]).1 ∧
    queryReply (M.decoder (historyState M (t.take j.val))) (t[j.val]).1 U =
      (t[j.val]).2 := by
  obtain ⟨s, rest, equation⟩ := prefix_run_tail M U pref run
  have tail : s = t.drop j.val := List.append_cancel_left
    (equation.trans (List.take_append_drop j.val t).symm)
  subst s
  rw [List.drop_eq_getElem_cons j.isLt] at rest
  generalize element : t[j.val] = a at rest ⊢
  rcases a with ⟨q, y⟩
  cases rest with
  | query row next => exact ⟨row, rfl⟩

private theorem native_prefix_certificate (N : Nat) (π : Strategy) (M : Observer E)
    (admissible : Admissible N M) (exact : ExactTraces N π M)
    (U : Source) (allowed : Allowed N U) :
    PrefixCertificate M U (terminal π U).1 (terminal π U).2 := by
  obtain ⟨f, run⟩ := exact U allowed
  have legal := admissible.legal U allowed
  have prefixes := ((bounded_cache_control_lower_bounds N M admissible).2.1
    U allowed run).2.2
  refine ⟨?_, ?_, ?_⟩
  · intro j
    exact (actualPrefix_semantics M U legal (prefixes j.val (by omega))).2.1
  · intro j
    have pref := prefixes j.val (by omega)
    have guard := run_query_row M U run j pref
    have next := ActualPrefix.query pref guard.1
    rw [guard.2] at next
    have state := (actualPrefix_semantics M U legal next).1
    refine ⟨guard.1, guard.2, ?_, ?_⟩
    · simpa only [List.take_succ_eq_append_getElem j.isLt] using state
    · simpa only [guard.2] using (legal.2 _ _ pref).2 _ guard.1
  · have terminalPref := (run_from_actualPrefix M U run ActualPrefix.initial).1
    simp only [List.nil_append] at terminalPref
    rw [(actualPrefix_semantics M U legal terminalPref).1]
    exact (run_from_actualPrefix M U run ActualPrefix.initial).2

/-- Finite source tests and every-prefix literal guards, with the independent
unrestricted action graph. This predicate never decides Admissible or ExactTraces. -/
def ExactCertificate (N : Nat) (π : Strategy) (M : Observer E) : Prop :=
  1 ≤ N ∧ PairCertificate M ∧ ∀ U ∈ allowedSources N,
    sourceCheck M U = true ∧ PrefixCertificate M U (terminal π U).1 (terminal π U).2

/-- The primitive finite certificate is exactly the original native exact class. -/
theorem prescribed_prefix_certificate_iff (N : Nat) (π : Strategy) (M : Observer E) :
    ExactCertificate N π M ↔ Admissible N M ∧ ExactTraces N π M := by
  constructor
  · rintro ⟨positive, pair, sources⟩
    have checked U (allowed : Allowed N U) := sources U ((allowedSources_exact N U).mpr allowed)
    refine ⟨⟨positive, ?_, ?_, (pair_certificate_iff M).mp pair⟩, ?_⟩
    · intro U allowed
      exact ((sourceCheck_iff M U).mp (checked U allowed).1).1
    · intro U allowed
      exact ((sourceCheck_iff M U).mp (checked U allowed).1).2
    · intro U allowed
      exact certificate_exact M U _ _ (checked U allowed).2 (checked U allowed).1
  · rintro ⟨admissible, exact⟩
    refine ⟨admissible.budget_pos, (pair_certificate_iff M).mpr admissible.coarse, ?_⟩
    intro U member
    have allowed := (allowedSources_exact N U).mp member
    exact ⟨(sourceCheck_iff M U).mpr ⟨admissible.legal U allowed,
      admissible.correct U allowed⟩, native_prefix_certificate N π M admissible exact U allowed⟩

/-- Original marks are tested at every prescribed prefix, including the halt. -/
def MarkCertificate {m : Nat} (F : Fin m → Source)
    (decode : CoarseHistory → Option (Fin m))
    (p : PassiveProtocol Address (fun _ => Option Bool)) (N : Nat) (π : Strategy)
    (M : Observer E) (mark : E → PhaseLabel m) : Prop :=
  ∀ U ∈ allowedSources N, ∀ j : Fin ((terminal π U).1.length + 1),
    mark (historyState M ((terminal π U).1.take j.val)) =
      (routePhase F decode p [] (kappa_hist ((terminal π U).1.take j.val))).1

private theorem mark_certificate_iff {m : Nat} (F : Fin m → Source)
    (decode : CoarseHistory → Option (Fin m))
    (p : PassiveProtocol Address (fun _ => Option Bool)) (N : Nat) (π : Strategy)
    (M : Observer E) (mark : E → PhaseLabel m)
    (admissible : Admissible N M) (exact : ExactTraces N π M) :
    MarkCertificate F decode p N π M mark ↔ OriginalMarks F decode p N M mark := by
  constructor
  · intro checked U allowed e h pref
    obtain ⟨f, run⟩ := exact U allowed
    obtain ⟨s, _, equation⟩ := prefix_run_tail M U pref run
    have pre : h.IsPrefix (terminal π U).1 := ⟨s, equation⟩
    have take : (terminal π U).1.take h.length = h := by
      rw [← equation]
      simp
    have bound := pre.length_le
    have value := checked U ((allowedSources_exact N U).mpr allowed) ⟨h.length, by omega⟩
    rw [take, (actualPrefix_semantics M U (admissible.legal U allowed) pref).1] at value
    exact value
  · intro marks U member j
    have allowed := (allowedSources_exact N U).mp member
    obtain ⟨f, run⟩ := exact U allowed
    have pref := ((bounded_cache_control_lower_bounds N M admissible).2.1
      U allowed run).2.2 j.val (by omega)
    exact marks U allowed _ _ pref

/-- Nominal rows are restricted to the prescribed literal support, independently
of the budget N used to check sources. Unused nominal rows remain present. -/
def SupportedRows (Q : Finset Address) (M : Observer E) : Prop :=
  (∀ e q, M.action e = .inl q → q ∈ Q) ∧
  ∀ e a, a ∈ M.decoder e → a.1 ∈ Q

noncomputable def rawPool (N : Nat) (π : Strategy) (n : Nat) (positive : 0 < n) :
    Finset (NativeTable (supportWidth (prescribedSupport N π)) n) := by
  classical
  exact Finset.univ.filter (fun T =>
    SupportedRows (prescribedSupport N π) (tableObserver positive T) ∧
    ExactCertificate N π (tableObserver positive T))

noncomputable def markedPool {m : Nat} (F : Fin m → Source)
    (decode : CoarseHistory → Option (Fin m))
    (p : PassiveProtocol Address (fun _ => Option Bool)) (N : Nat) (π : Strategy)
    (n : Nat) (positive : 0 < n) :
    Finset (NativeTable (supportWidth (prescribedSupport N π)) n ×
      (Fin n → PhaseMark F decode p N π)) := by
  classical
  exact Finset.univ.filter (fun entry => entry.1 ∈ rawPool N π n positive ∧
    MarkCertificate F decode p N π (tableObserver positive entry.1)
      (fun e => (entry.2 e).val))

/-- At each full nominal cardinality, a raw retained table is precisely the
underlying table of an originally marked retained entry. -/
theorem raw_mem_iff_marked {m : Nat} (F : Fin m → Source)
    (decode : CoarseHistory → Option (Fin m))
    (p : PassiveProtocol Address (fun _ => Option Bool)) (N : Nat) (π : Strategy)
    (n : Nat) (positive : 0 < n)
    (T : NativeTable (supportWidth (prescribedSupport N π)) n) :
    T ∈ rawPool N π n positive ↔ ∃ mark, (T, mark) ∈ markedPool F decode p N π n positive := by
  classical
  constructor
  · intro member
    have native := (prescribed_prefix_certificate_iff N π _).mp
      (Finset.mem_filter.mp member).2.2
    obtain ⟨mark, original⟩ := same_carrier_original_marking F decode p N π
      (tableObserver positive T) native.1 native.2
    exact ⟨mark, Finset.mem_filter.mpr ⟨Finset.mem_univ _, member,
      (mark_certificate_iff F decode p N π _ _ native.1 native.2).mpr original⟩⟩
  · rintro ⟨mark, member⟩
    exact (Finset.mem_filter.mp member).2.1

/-- Every originally marked competitor has a retained marked table on its full
nominal cardinality. Its concrete actual observations transport under one bijection. -/
theorem marked_competitor_table_coverage {m : Nat} (F : Fin m → Source)
    (decode : CoarseHistory → Option (Fin m))
    (p : PassiveProtocol Address (fun _ => Option Bool)) (N : Nat) (π : Strategy)
    (M : Observer E) (mark : E → PhaseLabel m)
    (admissible : Admissible N M) (exact : ExactTraces N π M)
    (original : OriginalMarks F decode p N M mark) :
    ∃ (positive : 0 < Fintype.card E) (r : E ≃ Fin (Fintype.card E))
      (T : NativeTable (supportWidth (prescribedSupport N π)) (Fintype.card E))
      (labels : Fin (Fintype.card E) → PhaseMark F decode p N π),
      (T, labels) ∈ markedPool F decode p N π (Fintype.card E) positive ∧
      (∀ U, Allowed N U → ∀ e h,
        ActualPrefix (tableObserver positive T) U (r e) h ↔ ActualPrefix M U e h) ∧
      (∀ U, Allowed N U → ∀ e h, ActualPrefix M U e h →
        (tableObserver positive T).decoder (r e) = M.decoder e ∧
        (tableObserver positive T).action (r e) = M.action e ∧
        (labels (r e)).val = mark e) := by
  classical
  obtain ⟨positive, r, T, admT, exactT, prefixes, observations, requests, caches⟩ :=
    exact_competitor_table_coverage N π M admissible exact
  let labels (e : Fin (Fintype.card E)) : PhaseMark F decode p N π :=
    if member : mark (r.symm e) ∈ phaseAlphabet F decode p N π then
      ⟨mark (r.symm e), Finset.mem_insert_of_mem member⟩
    else ⟨.malformed, Finset.mem_insert_self _ _⟩
  have originalRange U (allowed : Allowed N U) e h (pref : ActualPrefix M U e h) :
      mark e ∈ phaseAlphabet F decode p N π := by
    rw [original U allowed e h pref]
    obtain ⟨f, run⟩ := exact U allowed
    obtain ⟨s, _, equation⟩ := prefix_run_tail M U pref run
    exact Finset.mem_image.mpr ⟨kappa_hist h,
      strategy_prefix_mem N π allowed ⟨s, equation⟩, rfl⟩
  have preserved U (allowed : Allowed N U) e h (pref : ActualPrefix M U e h) :
      (labels (r e)).val = mark e := by
    simp only [labels, Equiv.symm_apply_apply, dif_pos (originalRange U allowed e h pref)]
  have marksT : OriginalMarks F decode p N (tableObserver positive T)
      (fun e => (labels e).val) := by
    intro U allowed e h pref
    have old := (prefixes U allowed (r.symm e) h).mp
      (by simpa only [Equiv.apply_symm_apply] using pref)
    have same := preserved U allowed (r.symm e) h old
    simp only [Equiv.apply_symm_apply] at same
    exact same.trans (original U allowed _ _ old)
  have raw : T ∈ rawPool N π (Fintype.card E) positive :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨requests, caches⟩,
      (prescribed_prefix_certificate_iff N π _).mpr ⟨admT, exactT⟩⟩
  refine ⟨positive, r, T, labels,
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, raw,
      (mark_certificate_iff F decode p N π _ _ admT exactT).mpr marksT⟩, prefixes, ?_⟩
  intro U allowed e h pref
  exact ⟨(observations U allowed e h pref).1,
    (observations U allowed e h pref).2, preserved U allowed e h pref⟩

/-- Finite candidate state sizes use the original exact compiler cutoff. -/
noncomputable def feasibleSizes (N : Nat) (π : Strategy) : Finset Nat := by
  classical
  exact (Finset.range (strategyStateCard N π + 1)).filter
    (fun n => ∃ positive : 0 < n, (rawPool N π n positive).Nonempty)

/-- The attained worst address fee of the prescribed trace on the same entire
allowed-source domain. Repetitions are charged once through paid. -/
noncomputable def fixedTraceFee (N : Nat) (π : Strategy) (positive : 1 ≤ N)
    (tau : Address → ℝ) : ℝ :=
  (allowedSources N).sup' (allowedSources_nonempty N positive)
    (fun U => charge tau (terminal π U).1)

private theorem exact_max_fee (N : Nat) (π : Strategy) (positive : 1 ≤ N)
    (M : Observer E) (exact : ExactTraces N π M) (tau : Address → ℝ) :
    maxFee N M tau = fixedTraceFee N π positive tau := by
  classical
  simp only [maxFee, dif_pos (allowedSources_nonempty N positive), fixedTraceFee]
  apply Finset.sup'_congr (allowedSources_nonempty N positive) rfl
  intro U member
  obtain ⟨f, run⟩ := exact U ((allowedSources_exact N U).mp member)
  exact fee_run M tau U run

/-- Both original classes attain the same state minimum and fixed-trace price.
The marked witness is obtained by the new unchanged-carrier construction, while
complete coverage compares against every original finite nominal competitor. -/
theorem original_exact_marked_attainment {m : Nat} (F : Fin m → Source)
    (decode : CoarseHistory → Option (Fin m))
    (p : PassiveProtocol Address (fun _ => Option Bool)) (N : Nat) (π : Strategy)
    (positive : 1 ≤ N)
    (policy : π.policy = fun h => ActualJointResponseCostCore.controllerPolicy
      (ActualCoarseReadoutCompletion.compileRaw F decode p [])
      (ActualCoarseReadoutCompletion.encodeHistory (kappa_hist h))) :
    ∃ (k : Nat) (posK : 0 < k)
      (T : NativeTable (supportWidth (prescribedSupport N π)) k)
      (mark : Fin k → PhaseMark F decode p N π),
      k ≤ strategyStateCard N π ∧
      T ∈ rawPool N π k posK ∧ (T, mark) ∈ markedPool F decode p N π k posK ∧
      (∀ {Carrier : Type u} [Fintype Carrier] (M : Observer Carrier),
        Admissible N M → ExactTraces N π M → k ≤ Fintype.card Carrier) ∧
      (∀ U : Source, terminal π U = ActualJointResponseCostCore.controllerOutcome
        (ActualCoarseReadoutCompletion.compileRaw F decode p []) U) ∧
      ∀ (tau : Address → ℝ), (∀ q, 0 ≤ tau q) → ∀ (kappa : ℝ), 0 < kappa →
        J_N N (tableObserver posK T) tau kappa =
          kappa * (k : ℝ) + fixedTraceFee N π positive tau ∧
        (∀ {Carrier : Type u} [Fintype Carrier] (M : Observer Carrier),
          Admissible N M → ExactTraces N π M →
          kappa * (k : ℝ) + fixedTraceFee N π positive tau ≤ J_N N M tau kappa) ∧
        (∀ U, Allowed N U → charge tau (terminal π U).1 ≤ fixedTraceFee N π positive tau) ∧
        ∃ U, Allowed N U ∧ fixedTraceFee N π positive tau = charge tau (terminal π U).1 := by
  classical
  have coarse : Function.FactorsThrough π.policy kappa_hist := by
    intro h h' same
    simp only [policy, same]
  let baseline := strategyObserver N π positive
  have admB : Admissible N baseline := strategy_admissible N π positive coarse
  have exactB : ExactTraces N π baseline := strategy_exact_run N π positive coarse
  obtain ⟨posB, rB, TB, admTB, exactTB, _, _, requestsB, cachesB⟩ :=
    exact_competitor_table_coverage N π baseline admB exactB
  have rawB : TB ∈ rawPool N π _ posB :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨requestsB, cachesB⟩,
      (prescribed_prefix_certificate_iff N π _).mpr ⟨admTB, exactTB⟩⟩
  have cardB := strategy_state_card N π
  have sizesNonempty : (feasibleSizes N π).Nonempty := by
    refine ⟨Fintype.card (ExactState (strategyPrefixes N π)), Finset.mem_filter.mpr ⟨?_,
      posB, TB, rawB⟩⟩
    simp only [Finset.mem_range, cardB]
    omega
  let k := (feasibleSizes N π).min' sizesNonempty
  have memberK := Finset.min'_mem (feasibleSizes N π) sizesNonempty
  obtain ⟨boundK, posK, T, raw⟩ := Finset.mem_filter.mp memberK
  have limit : k ≤ strategyStateCard N π := by
    simp only [Finset.mem_range] at boundK
    omega
  obtain ⟨mark, marked⟩ := (raw_mem_iff_marked F decode p N π k posK T).mp raw
  have native := (prescribed_prefix_certificate_iff N π _).mp (Finset.mem_filter.mp raw).2.2
  have original := (mark_certificate_iff F decode p N π _ _ native.1 native.2).mp
    (Finset.mem_filter.mp marked).2.2
  have normalized : ∃ (pos : 0 < Fintype.card (Fin k))
      (S : NativeTable (supportWidth (prescribedSupport N π)) (Fintype.card (Fin k)))
      (labels : Fin (Fintype.card (Fin k)) → PhaseMark F decode p N π),
      (S, labels) ∈ markedPool F decode p N π (Fintype.card (Fin k)) pos := by
    obtain ⟨pos, r, S, labels, retained, _, _⟩ := marked_competitor_table_coverage
      F decode p N π (tableObserver posK T) (fun e => (mark e).val)
        native.1 native.2 original
    exact ⟨pos, S, labels, retained⟩
  rw [Fintype.card_fin] at normalized
  obtain ⟨posS, S, labels, markedS⟩ := normalized
  have rawS := (Finset.mem_filter.mp markedS).2.1
  have nativeS := (prescribed_prefix_certificate_iff N π _).mp (Finset.mem_filter.mp rawS).2.2
  have least {Carrier : Type u} [Fintype Carrier] (M : Observer Carrier)
      (adm : Admissible N M) (ex : ExactTraces N π M) : k ≤ Fintype.card Carrier := by
    by_cases small : Fintype.card Carrier ≤ strategyStateCard N π
    · obtain ⟨pos, r, R, admR, exactR, _, _, requestsR, cachesR⟩ :=
        exact_competitor_table_coverage N π M adm ex
      have rawR : R ∈ rawPool N π _ pos :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨requestsR, cachesR⟩,
          (prescribed_prefix_certificate_iff N π _).mpr ⟨admR, exactR⟩⟩
      have member : Fintype.card Carrier ∈ feasibleSizes N π :=
        Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), pos, R, rawR⟩
      exact Finset.min'_le _ _ member
    · omega
  refine ⟨k, posS, S, labels, limit, rawS, markedS, @least,
    (ActualCompletionHorizon.actual_completion_horizon F decode p N π positive policy).1, ?_⟩
  intro tau nonneg kappa positivePrice
  have price : J_N N (tableObserver posS S) tau kappa =
      kappa * (k : ℝ) + fixedTraceFee N π positive tau := by
    change kappa * (Fintype.card (Fin k) : ℝ) + maxFee N _ tau = _
    rw [Fintype.card_fin, exact_max_fee N π positive _ nativeS.2 tau]
  have maximum := maximum_exact N positive (tableObserver posS S) tau
  refine ⟨price, ?_, ?_, ?_⟩
  · intro Carrier finite M adm ex
    have count : (k : ℝ) ≤ (Fintype.card Carrier : ℝ) := Nat.cast_le.mpr (least M adm ex)
    simp only [J_N, exact_max_fee N π positive M ex tau]
    exact add_le_add (mul_le_mul_of_nonneg_left count (le_of_lt positivePrice)) (le_refl _)
  · intro U allowed
    obtain ⟨f, run⟩ := nativeS.2 U allowed
    have bound := maximum.1 U allowed
    rwa [fee_run _ tau U run, exact_max_fee N π positive _ nativeS.2 tau] at bound
  · obtain ⟨U, allowed, equation⟩ := maximum.2
    obtain ⟨f, run⟩ := nativeS.2 U allowed
    exact ⟨U, allowed, by rwa [fee_run _ tau U run,
      exact_max_fee N π positive _ nativeS.2 tau] at equation⟩

#print axioms same_carrier_original_marking
#print axioms prescribed_prefix_certificate_iff
#print axioms raw_mem_iff_marked
#print axioms marked_competitor_table_coverage
#print axioms original_exact_marked_attainment

end D5.S3.Arith.FibonacciAtomic.Observer.ActualExactMarkedTables
