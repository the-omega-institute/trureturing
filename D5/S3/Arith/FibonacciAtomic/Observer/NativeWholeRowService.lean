/- GID: D5/S3/Arith/FibonacciAtomic/Observer/NativeWholeRowService
   generality: G
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/FibonacciAtomic/Observer/NativeWholeRowService.stationary_whole_fiber_service; instance=D5/S3/Arith/FibonacciAtomic/Observer/NativeWholeRowPlan.groundBindingInput
   digest: Continuous stationary execution of the complete native whole-row query plan. -/

import D5.S3.Arith.FibonacciAtomic.Observer.NativeWholeRowPlan

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096

namespace D5.S3.Arith.FibonacciAtomic.Observer.NativeWholeRowService

open GenealogicalFiberTransport (Source substitution)
open ActualTreeReadoutAcquisition (Address Reply readout)
open ActualLeafHistoryRigidity (subtree)
open ActualCutPartitionRecovery
open ActualCutPartitionDecoder
open NativeDepthPatterns (Pattern Frontier frontierAddress History)
open NativeCutFibers (Classes labels)
open NativeHistoryCells
open NativeSymbolicRecutting
open NativeGroundSeparation (Term evaluate)
open NativeTermUnification (Presentation finPresentation encode)
open NativeGroundSolutionSpace hiding Source
open Lambda Strata.Util
open DelayedOriginalReadout
open DelayedTemplateCertificate
open D5.S3.ConceptDynamics.Experiment.PassivePolicyNormalization (Hist execute)

/-- One controller, one chronological history and one final absorbing return. -/
def twoPhaseController {L : Type} (first : List Address)
    (second : Hist (fun _ : Address => Reply) → List Address)
    (finish : Hist (fun _ : Address => Reply) → L)
    (h : Hist (fun _ : Address => Reply)) : Sum Address L :=
  if h.length < first.length then
    match first[h.length]? with
    | some q => .inl q
    | none => .inr (finish h)
  else
    match (second (h.take first.length))[h.length - first.length]? with
    | some q => .inl q
    | none => .inr (finish h)

/-- Only finite common retained inputs and newly paid replies enter the selector. -/
structure StationaryProgram (L : Type) where
  first : List Address
  second : Hist (fun _ : Address => Reply) → List Address
  finish : Hist (fun _ : Address => Reply) → L
  admitted : Bool

/-- Preprocessing is materialized before the first physical action. -/
def compileService (C : LiteralRow) (Q : CutSet) (H : History) (N : Nat) :
    StationaryProgram Record :=
  let d := requiredDepth Q H
  let first := phaseOneQueries C d N
  let good := (analyze C Q H).passes
  let decode := fun h : Hist (fun _ : Address => Reply) =>
    selectedPatterns C d N ((h.take first.length).map Sigma.snd)
  let second := fun h : Hist (fun _ : Address => Reply) =>
    phaseTwoQueries Q (decode h) N
  let finish := fun h : Hist (fun _ : Address => Reply) =>
    if h.length == first.length + (second (h.take first.length)).length &&
        good && feasible (decode h) H && cellPass Q (decode h) then
      renderRecord Q (decode h) N ((h.drop first.length).map Sigma.snd)
    else (.of (.inl true), ∅)
  ⟨first,second,finish,good⟩

/-- The selector consumes the finite compiled common program and paid history. -/
def controller (program : StationaryProgram Record)
    (h : Hist (fun _ : Address => Reply)) : Sum Address Record :=
  if program.admitted then
    twoPhaseController program.first program.second program.finish h
  else .inr (.of (.inl true), ∅)


set_option maxHeartbeats 2000000 in
-- The finite dependent carrier and transcript proofs require extended elaboration fuel.
private theorem second_phase_suffix {L : Type} (first : List Address)
    (second : Hist (fun _ : Address => Reply) → List Address)
    (finish : Hist (fun _ : Address => Reply) → L) (u : Source)
    (initial : Hist (fun _ : Address => Reply)) (hlen : initial.length = first.length)
    (pre rest : List Address) (hs : second initial = pre ++ rest) :
    execute readout (twoPhaseController first second finish) (rest.length+1)
      (initial ++ listTrace pre u) u =
      some (listTrace rest u, finish (initial ++ listTrace (second initial) u)) := by
  induction rest generalizing pre with
  | nil =>
      have take : (initial ++ listTrace pre u).take first.length = initial := by
        rw [← hlen]; simp
      have stop : twoPhaseController first second finish (initial ++ listTrace pre u) =
          .inr (finish (initial ++ listTrace pre u)) := by
        simp [twoPhaseController, listTrace, hlen, take, hs]
      rw [execute,stop]
      simp [listTrace,hs]
  | cons q rest ih =>
      have take : (initial ++ listTrace pre u).take first.length = initial := by
        rw [← hlen]; simp
      have next : twoPhaseController first second finish (initial ++ listTrace pre u) = .inl q := by
        simp [twoPhaseController, listTrace, hlen, take, hs]
      change execute readout (twoPhaseController first second finish) ((rest.length+1)+1)
        (initial ++ listTrace pre u) u = _
      rw [execute,next]
      have newhist : (initial ++ listTrace pre u) ++ [(⟨q,readout q u⟩ : Sigma (fun _ : Address => Reply))] =
          initial ++ listTrace (pre ++ [q]) u := by simp [listTrace,List.append_assoc]
      have split : second initial = (pre ++ [q]) ++ rest := by simp [hs]
      dsimp only
      rw [newhist,ih (pre ++ [q]) split]
      simp [listTrace]

set_option maxHeartbeats 2000000 in
-- The finite dependent carrier and transcript proofs require extended elaboration fuel.
private theorem first_phase_suffix {L : Type} (first : List Address)
    (second : Hist (fun _ : Address => Reply) → List Address)
    (finish : Hist (fun _ : Address => Reply) → L) (u : Source)
    (h : Hist (fun _ : Address => Reply)) (pre rest : List Address)
    (hs : first = pre ++ rest) (hlen : h.length = pre.length) :
    execute readout (twoPhaseController first second finish)
      (rest.length + (second (h ++ listTrace rest u)).length + 1) h u =
      some (listTrace rest u ++ listTrace (second (h ++ listTrace rest u)) u,
        finish (h ++ listTrace rest u ++ listTrace (second (h ++ listTrace rest u)) u)) := by
  induction rest generalizing h pre with
  | nil =>
      have len : h.length = first.length := by simp [hs,hlen]
      simpa [listTrace] using second_phase_suffix first second finish u h len []
        (second h) (by simp)
  | cons q rest ih =>
      have next : twoPhaseController first second finish h = .inl q := by
        simp [twoPhaseController,hs,hlen]
      have fuel : (q :: rest).length + (second (h ++ listTrace (q :: rest) u)).length + 1 =
          (rest.length + (second ((h ++ [(⟨q,readout q u⟩ : Sigma (fun _ : Address => Reply))]) ++ listTrace rest u)).length + 1)+1 := by
        simp [listTrace,List.append_assoc,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
      rw [fuel,execute,next]
      have split : first = (pre ++ [q]) ++ rest := by simp [hs]
      have len : (h ++ [(⟨q,readout q u⟩ : Sigma (fun _ : Address => Reply))]).length = (pre ++ [q]).length := by simp [hlen]
      dsimp only
      rw [ih _ (pre ++ [q]) split len]
      simp [listTrace,List.append_assoc]

set_option maxHeartbeats 2000000 in
-- The finite dependent carrier and transcript proofs require extended elaboration fuel.
/-- The actual polymorphic executor runs both phases continuously and halts
once, paying the complete chronological list length without cache deductions. -/
theorem two_phase_execution {L : Type} (first : List Address)
    (second : Hist (fun _ : Address => Reply) → List Address)
    (finish : Hist (fun _ : Address => Reply) → L) (u : Source) :
    let one := listTrace first u
    let two := listTrace (second one) u
    execute readout (twoPhaseController first second finish)
      (first.length + (second one).length + 1) [] u = some (one ++ two,finish (one ++ two)) ∧
    (one ++ two).length = first.length + (second one).length ∧
    (one ++ two).map Sigma.fst = first ++ second one := by
  dsimp only
  refine ⟨?_,?_,?_⟩
  · simpa using first_phase_suffix first second finish u [] [] first (by simp) rfl
  · simp [listTrace]
  · simp [listTrace,List.map_map,Function.comp_def]


set_option maxHeartbeats 2000000 in
-- The finite dependent carrier and transcript proofs require extended elaboration fuel.
private theorem selected_pattern_of_cell {C : LiteralRow} {d : Nat}
    (η : Patterns C d) (v : Variables η → Source) (N : Nat) :
    selectedPatterns C d N ((phaseOneQueries C d N).map
      (fun q => readout q (substitution^[N] (evaluate v (wholeTerm η))))) = η := by
  have decoded := phase_one_patterns_correct C (oldValues η v) d N
  rw [←whole_evaluate η v] at decoded
  apply decoded.trans
  funext b
  have inv := congrArg Sigma.fst ((NativeDepthPatterns.depthEquiv d).right_inv
    ⟨η b,fun f => v ⟨b,f⟩⟩)
  exact inv

set_option maxHeartbeats 2000000 in
-- The finite dependent carrier and transcript proofs require extended elaboration fuel.
/-- The compiled source-free program attains the whole record on every lawful
filling in a feasible cell, continuously at the same stationary epoch. -/
theorem stationary_cell_service {C : LiteralRow} (Q : CutSet) (H : History)
    (hQ : CutPrefixFree Q) (good : (analyze C Q H).passes = true)
    (η : Patterns C (requiredDepth Q H)) (feasibleCell : feasible η H = true)
    (v : Variables η → Source) (legal : Diseq (delta η) v) (N : Nat) :
    let program := compileService C Q H N
    let u := evaluate v (wholeTerm η)
    ∃ fuel trace,
      execute readout (controller program) fuel [] (substitution^[N] u) =
        some (trace,literalRecord Q u) ∧ trace.length ≤ K0 C Q H := by
  dsimp only
  let d := requiredDepth Q H
  let u := evaluate v (wholeTerm η)
  let first := phaseOneQueries C d N
  let second := (compileService C Q H N).second
  let finish := (compileService C Q H N).finish
  let one := listTrace first (substitution^[N] u)
  have decoded : selectedPatterns C d N (one.map Sigma.snd) = η := by
    simpa only [one,first,listTrace,List.map_map,Function.comp_def,u,d] using selected_pattern_of_cell η v N
  have lengthOne : one.length = first.length := by simp [one,listTrace]
  have takeOne : one.take first.length = one := by rw [←lengthOne]; exact List.take_length
  have picked : second one = phaseTwoQueries Q η N := by
    change phaseTwoQueries Q (selectedPatterns C d N ((one.take first.length).map Sigma.snd)) N = _
    rw [takeOne,decoded]
  let two := listTrace (second one) (substitution^[N] u)
  have takeBoth : (one ++ two).take first.length = one := by
    rw [←lengthOne]; exact List.take_left
  have decodeBoth : selectedPatterns C d N (((one ++ two).take first.length).map Sigma.snd) = η := by
    rw [takeBoth,decoded]
  have cellpass : cellPass Q η = true :=
    List.all_eq_true.mp good η (List.mem_filter.mpr ⟨all_patterns_complete C d η,feasibleCell⟩)
  let dec := fun h : Hist (fun _ : Address => Reply) => selectedPatterns C d N ((h.take first.length).map Sigma.snd)
  have decBoth : dec (one ++ two) = η := decodeBoth
  have complete : finish (one ++ two) = literalRecord Q u := by
    have lengthTwo : two.length = (phaseTwoQueries Q η N).length := by simp [two,listTrace,picked]
    have lengthBoth : (one ++ two).length = first.length + (phaseTwoQueries Q η N).length := by simp [lengthOne,lengthTwo]
    change (if (one ++ two).length == first.length + (second ((one ++ two).take first.length)).length &&
      (analyze C Q H).passes && feasible (dec (one ++ two)) H && cellPass Q (dec (one ++ two)) then
      renderRecord Q (dec (one ++ two)) N (((one ++ two).drop first.length).map Sigma.snd)
      else (.of (.inl true),∅)) = literalRecord Q u
    rw [decBoth,takeBoth,picked,lengthBoth]
    simp only [beq_self_eq_true,good,feasibleCell,cellpass,Bool.true_and,Bool.true_eq,ite_true]
    rw [←lengthOne,List.drop_left]
    have replies : two.map Sigma.snd = (phaseTwoQueries Q η N).map
        (fun q => readout q (substitution^[N] u)) := by simp [two,listTrace,picked,List.map_map,Function.comp_def]
    rw [replies]
    exact selected_cell_record_correct Q H hQ η cellpass v legal N
  have admitted : controller (compileService C Q H N) = twoPhaseController first second finish := by
    funext hist
    change (if (analyze C Q H).passes then twoPhaseController first second finish hist
      else .inr (.of (.inl true),∅)) = _
    rw [good]
    rfl
  have run := two_phase_execution first second finish (substitution^[N] u)
  refine ⟨first.length+(second one).length+1,one++two,?_,?_⟩
  · rw [admitted]
    exact run.1.trans (congrArg (fun r => some (one++two,r)) complete)
  · have mem : η ∈ feasiblePatterns C d H := by simp [feasiblePatterns,feasibleCell]
    have budget := two_phase_uniform_bound C Q H η mem N
    rw [List.length_append,lengthOne]
    have lenTwo : two.length = (second one).length := by simp [two,listTrace]
    rw [lenTwo,picked]
    exact budget

set_option maxHeartbeats 2000000 in
-- The finite dependent carrier and transcript proofs require extended elaboration fuel.
/-- Whole-fiber stationary correctness uses the actual exact native cell/source
bijection. No source or valuation is an input to the compiled program. -/
theorem stationary_whole_fiber_service (P Q : CutSet) (hP : CutPrefixFree P)
    (hQ : CutPrefixFree Q) (base : Source) (H : History)
    (good : (analyze (canonicalRow P base) Q H).passes = true) (N : Nat)
    (u : Source) (old : canonicalRow P u = canonicalRow P base)
    (history : NativeDepthPatterns.Consistent H u) :
    ∃ fuel trace,
      execute readout (controller (compileService (canonicalRow P base) Q H N)) fuel []
        (substitution^[N] u) = some (trace,literalRecord Q u) ∧
      trace.length ≤ K0 (canonicalRow P base) Q H := by
  let cell := (historyCellEquiv P hP base Q H).symm ⟨u,old,history⟩
  have source := congrArg Subtype.val ((historyCellEquiv P hP base Q H).apply_symm_apply ⟨u,old,history⟩)
  have feasibleCell : feasible cell.1.val H = true := (Finset.mem_filter.mp cell.1.property).2
  have run := stationary_cell_service Q H hQ good cell.1.val feasibleCell cell.2.val
    ((delta_legal cell.1.val cell.2.val).mpr cell.2.property) N
  have eq : evaluate cell.2.val (wholeTerm cell.1.val) = u := source
  simpa only [eq] using run

end D5.S3.Arith.FibonacciAtomic.Observer.NativeWholeRowService
