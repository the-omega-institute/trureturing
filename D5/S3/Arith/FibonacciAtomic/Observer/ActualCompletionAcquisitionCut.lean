/- GID: D5/S3/Arith/FibonacciAtomic/Observer/ActualCompletionAcquisitionCut
   generality: G
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Actual raw acquisition cuts with first-mismatch provenance and persistent caches. -/

import D5.S3.Arith.FibonacciAtomic.Observer.ActualCompletionPhaseReplay
import D5.S3.Arith.FibonacciAtomic.Observer.ActualCompletionHorizon

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.Observer.ActualCompletionAcquisitionCut

open GenealogicalFiberTransport (Source)
open ActualTreeReadoutAcquisition (Address Reply Strategy terminal readout leaves
  acquisitionTrace acquisitionPolicy)
open ActualCoarseReadoutHistory (kappa kappa_hist)
open ActualCoarseReadoutCompletion (encodeHistory compileRaw completion_contract
  acquisition_prefix_representative)
open ActualJointResponseCostCore (controllerPolicy controllerOutcome verifyController)
open ActualImageSevenLeafSeparation (leafLabel seven_leaf_separation)
open ActualLeafHistoryRigidity (subtree)
open D5.S3.ConceptDynamics.Experiment.PassiveAdaptiveTranscriptUpperBound
  (PassiveProtocol runPassiveProtocol)
open ActualFiniteObserverAbsentElimination
open ActualExactTraceCompiler
open ActualCompletionPhaseReplay

/-- Actual reports preserve the order and repetitions of their literal requests. -/
def actualReports (U : Source) (qs : List Address) : RawHistory :=
  qs.map (fun q => ⟨q, readout q U⟩)

/-- The complete passive route with actual four-response reports, including absent. -/
def actualRoute (p : PassiveProtocol Address (fun _ => Option Bool)) (U : Source) : RawHistory :=
  (runPassiveProtocol (fun q W => leafLabel W q) p U).map
    (fun z => ⟨z.1, readout z.1 U⟩)

/-- The first failed literal leaf test, including its actual report in the verifier segment. -/
def FirstMismatch (V : Source) (qs : List Address) (U : Source) (v : RawHistory) : Prop :=
  ∃ (pre rest : List Address) (q : Address),
    qs = pre ++ q :: rest ∧
    (∀ r ∈ pre, readout r U = readout r V) ∧
    readout q U ≠ readout q V ∧ kappa (readout q U) ≠ leafLabel V q ∧
    v = actualReports U pre ++ [⟨q, readout q U⟩]

/-- The decoder retains its exact selected index even when prototypes repeat. -/
def RouteExit {m : Nat} (F : Fin m → Source)
    (decode : CoarseHistory → Option (Fin m)) (seen : CoarseHistory)
    (U : Source) (v : RawHistory) : Prop :=
  (decode seen = none ∧ v = []) ∨
    ∃ i : Fin m, decode seen = some i ∧ FirstMismatch (F i) (leaves (F i)) U v

/-- The route and first failure precede a fresh same-source acquisition prefix. -/
def AcquisitionCut {m : Nat} (F : Fin m → Source)
    (decode : CoarseHistory → Option (Fin m))
    (p : PassiveProtocol Address (fun _ => Option Bool))
    (U : Source) (h : RawHistory) (g : CoarseHistory) (v a : RawHistory) : Prop :=
  h = actualRoute p U ++ v ++ a ∧ a.IsPrefix (acquisitionTrace [] U) ∧
    g = kappa_hist a ∧ RouteExit F decode (kappa_hist (actualRoute p U)) U v

/-- Existence and the actual parent branch are certified inside the fresh suffix. -/
def AcquisitionGeometry (U : Source) (a : RawHistory) : Prop :=
  ∀ q : Address, acquisitionPolicy a = .inl q →
    (∃ T : Source, subtree q U = some T) ∧
    (kappa (readout q U) = none → ∃ X Y : Source, subtree q U = some (.mul X Y)) ∧
    (q ≠ [] → ∃ (w : Address) (d : Bool),
      q = w ++ [d] ∧ (⟨w, Reply.branch⟩ : Sigma (fun _ : Address => Reply)) ∈ a)

private theorem verify_acquisition_cut {m : Nat} (F : Fin m → Source) (i : Fin m)
    (qs : List Address) (seen : CoarseHistory) (U : Source) (x : RawHistory)
    (onlyLeaves : ∀ q ∈ qs, q ∈ leaves (F i))
    (pref : x.IsPrefix (controllerOutcome (verifyController (F i) qs) U).1) :
    (verifyPhase F i qs seen (kappa_hist x)).1 ≠ .malformed ∧
    ∀ g, (verifyPhase F i qs seen (kappa_hist x)).1 = .acquisition g →
      ∃ v a : RawHistory, x = v ++ a ∧ a.IsPrefix (acquisitionTrace [] U) ∧
        g = kappa_hist a ∧ FirstMismatch (F i) qs U v := by
  let repr : Reply → Reply := fun y => match kappa y with
    | some true => .alpha
    | some false => .beta
    | none => .branch
  have faithful (q : Address) (member : q ∈ leaves (F i)) (y : Reply) :
      repr y = readout q (F i) ↔ y = readout q (F i) := by
    have expected : repr (readout q (F i)) = readout q (F i) :=
      leaf_representative (F i) q member
    obtain ⟨b, label⟩ := ((seven_leaf_separation.1 (F i)).2 q).mp
      (List.mem_toFinset.mpr member)
    cases result : readout q (F i) <;> cases y <;> simp_all [repr, kappa, leafLabel]
  induction qs generalizing seen x with
  | nil =>
      simp only [verifyPhase]
      exact ⟨by simp, fun g impossible => by cases impossible⟩
  | cons q qs ih =>
      cases x with
      | nil =>
          simp only [kappa_hist, List.map_nil, verifyPhase]
          exact ⟨by simp, fun g impossible => by cases impossible⟩
      | cons report x =>
          have full : (controllerOutcome (verifyController (F i) (q :: qs)) U).1 =
              ⟨q, readout q U⟩ ::
                (controllerOutcome (if readout q U = readout q (F i) then
                  verifyController (F i) qs else .fallback) U).1 := rfl
          rw [full] at pref
          obtain ⟨rfl, tail⟩ := List.cons_prefix_cons.mp pref
          have member := onlyLeaves q List.mem_cons_self
          have restLeaves : ∀ r ∈ qs, r ∈ leaves (F i) :=
            fun r hr => onlyLeaves r (List.mem_cons_of_mem q hr)
          by_cases matched : readout q U = readout q (F i)
          · have test : repr (readout q U) = readout q (F i) :=
              (faithful q member _).mpr matched
            rw [if_pos matched] at tail
            obtain ⟨valid, cut⟩ := ih (seen ++ [⟨q, kappa (readout q U)⟩]) x restLeaves tail
            have parsed : verifyPhase F i (q :: qs) seen
                (kappa_hist (⟨q, readout q U⟩ :: x)) =
                verifyPhase F i qs (seen ++ [⟨q, kappa (readout q U)⟩]) (kappa_hist x) := by
              change (if q = q then
                if repr (readout q U) = readout q (F i) then _ else _ else _) = _
              rw [if_pos rfl, if_pos test]
              rfl
            rw [parsed]
            refine ⟨valid, ?_⟩
            intro g label
            obtain ⟨v, a, history, acquisition, suffix, pre, rest, q₀,
              split, successes, failure, coarseFailure, verifier⟩ := cut g label
            refine ⟨⟨q, readout q U⟩ :: v, a, ?_, acquisition, suffix,
              q :: pre, rest, q₀, ?_, ?_, failure, coarseFailure, ?_⟩
            · simp only [List.cons_append, history]
            · simp only [List.cons_append, split]
            · intro r hr
              rcases List.mem_cons.mp hr with rfl | hr
              · exact matched
              · exact successes r hr
            · simp only [actualReports, List.map_cons, List.cons_append] at verifier ⊢
              rw [verifier]
          · have test : repr (readout q U) ≠ readout q (F i) :=
              fun equal => matched ((faithful q member _).mp equal)
            have coarseFailure : kappa (readout q U) ≠ leafLabel (F i) q := by
              intro equal
              apply test
              change (match kappa (readout q U) with
                | some true => Reply.alpha | some false => Reply.beta | none => Reply.branch) = _
              rw [equal]
              exact leaf_representative (F i) q member
            rw [if_neg matched] at tail
            change x.IsPrefix (acquisitionTrace [] U) at tail
            have parsed : verifyPhase F i (q :: qs) seen
                (kappa_hist (⟨q, readout q U⟩ :: x)) =
                (.acquisition (kappa_hist x),
                  acquisitionPolicy (encodeHistory (kappa_hist x))) := by
              change (if q = q then
                if repr (readout q U) = readout q (F i) then _ else _ else _) = _
              rw [if_pos rfl, if_neg test]
              rfl
            rw [parsed]
            refine ⟨by simp, ?_⟩
            intro g label
            have suffix : g = kappa_hist x := PhaseLabel.acquisition.inj label.symm
            refine ⟨[⟨q, readout q U⟩], x, rfl, tail, suffix,
              [], qs, q, rfl, ?_, matched, coarseFailure, rfl⟩
            simp

private theorem route_acquisition_cut {m : Nat} (F : Fin m → Source)
    (decode : CoarseHistory → Option (Fin m))
    (p : PassiveProtocol Address (fun _ => Option Bool))
    (seen : CoarseHistory) (U : Source) (x : RawHistory)
    (pref : x.IsPrefix (controllerOutcome (compileRaw F decode p seen) U).1) :
    kappa_hist (actualRoute p U) = runPassiveProtocol (fun q W => leafLabel W q) p U ∧
    (routePhase F decode p seen (kappa_hist x)).1 ≠ .malformed ∧
    ∀ g, (routePhase F decode p seen (kappa_hist x)).1 = .acquisition g →
      ∃ v a : RawHistory, x = actualRoute p U ++ v ++ a ∧
        a.IsPrefix (acquisitionTrace [] U) ∧ g = kappa_hist a ∧
        RouteExit F decode (seen ++ kappa_hist (actualRoute p U)) U v := by
  induction p generalizing seen x with
  | stop =>
      have route : actualRoute .stop U = [] := rfl
      refine ⟨rfl, ?_⟩
      cases choice : decode seen with
      | none =>
          simp only [compileRaw, choice, controllerOutcome] at pref
          simp only [routePhase, choice]
          change PhaseLabel.acquisition (kappa_hist x) ≠ .malformed ∧ _
          refine ⟨by simp, ?_⟩
          intro g label
          refine ⟨[], x, rfl, pref, PhaseLabel.acquisition.inj label.symm, Or.inl ⟨?_, rfl⟩⟩
          simpa only [route, kappa_hist, List.map_nil, List.append_nil] using choice
      | some i =>
          have vpref : x.IsPrefix
              (controllerOutcome (verifyController (F i) (leaves (F i))) U).1 := by
            simpa only [compileRaw, choice] using pref
          obtain ⟨valid, cut⟩ := verify_acquisition_cut F i (leaves (F i)) [] U x
            (fun _ member => member) vpref
          refine ⟨?_, ?_⟩
          · simpa only [routePhase, choice] using valid
          · intro g label
            obtain ⟨v, a, history, acquisition, suffix, mismatch⟩ := cut g
              (by simpa only [routePhase, choice] using label)
            refine ⟨v, a, history, acquisition, suffix, Or.inr ⟨i, ?_, mismatch⟩⟩
            simpa only [route, kappa_hist, List.map_nil, List.append_nil] using choice
  | query q next ih =>
      let z := kappa (readout q U)
      have route : actualRoute (.query q next) U = ⟨q, readout q U⟩ :: actualRoute (next z) U := rfl
      cases x with
      | nil =>
          have child := ih z (seen ++ [⟨q, z⟩]) [] List.nil_prefix
          refine ⟨?_, ?_, ?_⟩
          · exact congrArg (List.cons ⟨q, leafLabel U q⟩) child.1
          · simp [routePhase, kappa_hist]
          · intro g impossible
            simp [routePhase, kappa_hist] at impossible
      | cons report x =>
          have full : (controllerOutcome (compileRaw F decode (.query q next) seen) U).1 =
              ⟨q, readout q U⟩ ::
                (controllerOutcome (compileRaw F decode (next z) (seen ++ [⟨q, z⟩])) U).1 := rfl
          rw [full] at pref
          obtain ⟨rfl, tail⟩ := List.cons_prefix_cons.mp pref
          obtain ⟨coarseRoute, valid, cut⟩ := ih z (seen ++ [⟨q, z⟩]) x tail
          have parsed : routePhase F decode (.query q next) seen
              (kappa_hist (⟨q, readout q U⟩ :: x)) =
              routePhase F decode (next z) (seen ++ [⟨q, z⟩]) (kappa_hist x) := by
            simp [routePhase, kappa_hist, z]
          refine ⟨?_, ?_, ?_⟩
          · exact congrArg (List.cons ⟨q, leafLabel U q⟩) coarseRoute
          · rw [parsed]; exact valid
          · intro g label
            obtain ⟨v, a, history, acquisition, suffix, exit⟩ := cut g (by rwa [parsed] at label)
            refine ⟨v, a, ?_, acquisition, suffix, ?_⟩
            · simpa only [route, List.cons_append] using
                congrArg (List.cons ⟨q, readout q U⟩) history
            · simpa only [route, kappa_hist, List.map_cons, List.append_assoc,
                List.singleton_append] using exit

/-- Every actual acquisition label comes after the full raw route and, when selected,
the first failed leaf test. The same cut controls the original native observer while
its exact ordered cache persists across the phase boundary. -/
theorem acquisition_provenance_contract {m : Nat} (F : Fin m → Source)
    (decode : CoarseHistory → Option (Fin m))
    (p : PassiveProtocol Address (fun _ => Option Bool)) (π : Strategy)
    (policy : π.policy = fun h =>
      controllerPolicy (compileRaw F decode p []) (encodeHistory (kappa_hist h))) :
    (∀ (U : Source) (h : RawHistory), h.IsPrefix (terminal π U).1 →
      (routePhase F decode p [] (kappa_hist h)).1 ≠ .malformed ∧
      ∀ g, (routePhase F decode p [] (kappa_hist h)).1 = .acquisition g →
        ∃ v a : RawHistory, AcquisitionCut F decode p U h g v a ∧
          routePhase F decode p [] (kappa_hist h) = (.acquisition g, acquisitionPolicy a) ∧
          π.policy h = acquisitionPolicy a ∧ AcquisitionGeometry U a) ∧
    (∀ (N : Nat) (positive : 1 ≤ N) (U : Source), Allowed N U →
      ∀ (e : ExactState (strategyPrefixes N π)) (h : RawHistory),
      ActualPrefix (strategyObserver N π positive) U e h →
        observerPhase F decode p N π e = (routePhase F decode p [] (kappa_hist h)).1 ∧
        observerPhase F decode p N π e ≠ .malformed ∧
        ∀ g, observerPhase F decode p N π e = .acquisition g →
          ∃ v a : RawHistory, AcquisitionCut F decode p U h g v a ∧
            routePhase F decode p [] (kappa_hist h) = (.acquisition g, acquisitionPolicy a) ∧
            (strategyObserver N π positive).action e = acquisitionPolicy a ∧
            AcquisitionGeometry U a ∧
            (strategyObserver N π positive).decoder e = firstRaw h ∧
            firstRaw h = a.foldl (fun cache report => cacheUpdate cache report.1 report.2)
              (firstRaw (actualRoute p U ++ v))) := by
  classical
  have coarse : Function.FactorsThrough π.policy kappa_hist := by
    intro h k equal
    simp only [policy, equal]
  have outcome := (ActualCompletionHorizon.actual_completion_horizon F decode p 1 π le_rfl policy).1
  obtain ⟨aux, auxiliary⟩ :=
    completion_contract 0 Fin.elim0 (fun i => Fin.elim0 i) .stop (fun _ => none)
  have geometry := auxiliary.2.2.2.2.2.1
  have raw (U : Source) (h : RawHistory) (pref : h.IsPrefix (terminal π U).1) :
      (routePhase F decode p [] (kappa_hist h)).1 ≠ .malformed ∧
      ∀ g, (routePhase F decode p [] (kappa_hist h)).1 = .acquisition g →
        ∃ v a : RawHistory, AcquisitionCut F decode p U h g v a ∧
          routePhase F decode p [] (kappa_hist h) = (.acquisition g, acquisitionPolicy a) ∧
          π.policy h = acquisitionPolicy a ∧ AcquisitionGeometry U a := by
    rw [outcome U] at pref
    obtain ⟨coarseRoute, valid, cut⟩ := route_acquisition_cut F decode p [] U h pref
    refine ⟨valid, ?_⟩
    intro g label
    obtain ⟨v, a, history, acquisition, suffix, exit⟩ := cut g label
    have representative := acquisition_prefix_representative U a acquisition
    have replay := phase_replay_contract F decode p 1 π le_rfl policy
    have reset : routePhase F decode p [] (kappa_hist h) =
        (.acquisition g, acquisitionPolicy a) := by
      rw [history]
      simp only [kappa_hist, List.map_append, List.append_assoc]
      change routePhase F decode p []
        (kappa_hist (actualRoute p U) ++ (kappa_hist v ++ kappa_hist a)) = _
      rw [coarseRoute, replay.2.1 U (kappa_hist v ++ kappa_hist a)]
      rw [← coarseRoute]
      rcases exit with ⟨noSelection, rfl⟩ |
        ⟨i, selected, pre, rest, q, split, successes, failure, different, verifier⟩
      · have choice : decode (kappa_hist (actualRoute p U)) = none := by
          simpa only [List.nil_append] using noSelection
        change routePhase F decode .stop (kappa_hist (actualRoute p U)) (kappa_hist a) = _
        rw [routePhase, choice]
        change ((PhaseLabel.acquisition (kappa_hist a) : PhaseLabel m),
          acquisitionPolicy (encodeHistory (kappa_hist a))) = _
        rw [representative, suffix]
      · have selected' : decode (kappa_hist (actualRoute p U)) = some i := by
          simpa only [List.nil_append] using selected
        simp only [routePhase, selected']
        have reports : kappa_hist (actualReports U pre) =
            pre.map (fun r => ⟨r, leafLabel (F i) r⟩) := by
          simp only [actualReports, kappa_hist, List.map_map, Function.comp_def]
          apply List.map_congr_left
          intro r member
          rw [successes r member]
          rfl
        rw [verifier]
        simp only [kappa_hist, List.map_append, List.map_cons, List.map_nil]
        change verifyPhase F i (leaves (F i)) []
          ((kappa_hist (actualReports U pre) ++ [⟨q, kappa (readout q U)⟩]) ++ kappa_hist a) = _
        rw [reports]
        rw [replay.2.2.1 i pre rest q (readout q U) (kappa_hist a) split different]
        rw [representative, suffix]
    have action : π.policy h = acquisitionPolicy a := by
      calc
        π.policy h = controllerPolicy (compileRaw F decode p [])
            (encodeHistory (kappa_hist h)) := congrFun policy h
        _ = (routePhase F decode p [] (kappa_hist h)).2 := (replay.1 _).symm
        _ = acquisitionPolicy a := congrArg Prod.snd reset
    refine ⟨v, a, ⟨history, acquisition, suffix, ?_⟩, reset, action, ?_⟩
    · simpa only [List.nil_append] using exit
    · intro q queried
      apply geometry U a q acquisition
      rwa [representative]
  refine ⟨raw, ?_⟩
  intro N positive U allowed e h pref
  have replay := phase_replay_contract F decode p N π positive policy
  obtain ⟨label, _, parsedAction⟩ := replay.2.2.2.2.2 U allowed e h pref
  obtain ⟨row, state, history, cache, original⟩ :=
    strategy_actual_prefix_replay N π positive coarse U allowed pref
  obtain ⟨valid, cut⟩ := raw U h original
  refine ⟨label, label ▸ valid, ?_⟩
  intro g acquisition
  obtain ⟨v, a, decomposition, parsed, action, geometry⟩ := cut g (label.symm.trans acquisition)
  have legal := (strategy_admissible N π positive coarse).legal U allowed
  have semantics := actualPrefix_semantics (strategyObserver N π positive) U legal pref
  have global : (strategyObserver N π positive).decoder e = firstRaw h := semantics.2.1
  refine ⟨v, a, decomposition, parsed, ?_, geometry, global, ?_⟩
  · exact (strategy_prefix_action N π positive coarse U allowed pref).trans action
  · rw [decomposition.1]
    exact List.foldl_append

#print axioms acquisition_provenance_contract

end D5.S3.Arith.FibonacciAtomic.Observer.ActualCompletionAcquisitionCut
