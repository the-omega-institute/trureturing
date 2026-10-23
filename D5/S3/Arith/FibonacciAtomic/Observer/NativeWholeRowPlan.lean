/- GID: D5/S3/Arith/FibonacciAtomic/Observer/NativeWholeRowPlan
   generality: G
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/FibonacciAtomic/Observer/NativeWholeRowService.stationary_whole_fiber_service; instance=D5/S3/Arith/FibonacciAtomic/Observer/NativeWholeRowPlan.groundBindingInput
   digest: Finite whole-cell criterion, paid query plans and complete record correctness. -/

import D5.S3.Arith.FibonacciAtomic.Observer.NativeHistoryCells
import D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace
import D5.S3.Arith.FibonacciAtomic.Observer.DelayedTemplateCertificate
import Mathlib.Data.List.Pi
import Mathlib.Data.List.NodupEquivFin

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

/-- Structural left-to-right enumeration, including the unique depth-zero frontier. -/
def frontierList : {d : Nat} → (p : Pattern d) → List (Frontier p)
  | 0, _ => [()]
  | _+1, .inl _ => []
  | _+1, .inr p => (frontierList p.1).map Sum.inl ++ (frontierList p.2).map Sum.inr

set_option maxHeartbeats 2000000 in
-- The finite dependent carrier and transcript proofs require extended elaboration fuel.
theorem frontier_complete {d : Nat} (p : Pattern d) (x : Frontier p) :
    x ∈ frontierList p := by
  induction d with
  | zero => cases p; cases x; exact List.mem_cons_self
  | succ d ih => cases p with
    | inl b => exact PEmpty.elim x
    | inr p => cases x with
      | inl x => exact List.mem_append_left _ (List.mem_map.mpr ⟨x, ih p.1 x, rfl⟩)
      | inr x => exact List.mem_append_right _ (List.mem_map.mpr ⟨x, ih p.2 x, rfl⟩)

/-- Class order comes from the retained numeric names, not source values. -/
def classList (C : LiteralRow) : List (Classes C) :=
  ((labels C).sort (· ≤ ·)).attach.map (fun b => ⟨b.val, (Finset.mem_sort _).mp b.property⟩)

set_option maxHeartbeats 2000000 in
-- The finite dependent carrier and transcript proofs require extended elaboration fuel.
theorem class_complete (C : LiteralRow) (b : Classes C) : b ∈ classList C := by
  apply List.mem_map.mpr
  refine ⟨⟨b.val, (Finset.mem_sort _).mpr b.property⟩, by simp, ?_⟩
  rfl

def variableList {C : LiteralRow} {d : Nat} (η : Patterns C d) : List (Variables η) :=
  ((classList C).flatMap (fun b => (frontierList (η b)).map (Sigma.mk b))).dedup

set_option maxHeartbeats 2000000 in
-- The finite dependent carrier and transcript proofs require extended elaboration fuel.
theorem variable_complete {C : LiteralRow} {d : Nat} (η : Patterns C d)
    (x : Variables η) : x ∈ variableList η := by
  rw [variableList, List.mem_dedup]
  exact List.mem_flatMap.mpr ⟨x.1, class_complete C x.1,
    List.mem_map.mpr ⟨x.2, frontier_complete (η x.1) x.2, rfl⟩⟩

/-- The list-index equivalence computes both directions without choice. -/
def presentation {C : LiteralRow} {d : Nat} (η : Patterns C d) : Presentation (Variables η) :=
  (finPresentation (variableList η).length).transport
    (List.Nodup.getEquivOfForallMemList (variableList η)
      (by unfold variableList; exact List.nodup_dedup _) (variable_complete η)).symm

def patternList : (d : Nat) → List (Pattern d)
  | 0 => [()]
  | d+1 => [.inl false, .inl true] ++
      (patternList d).flatMap (fun l => (patternList d).map (fun r => .inr (l,r)))

set_option maxHeartbeats 2000000 in
-- The finite dependent carrier and transcript proofs require extended elaboration fuel.
theorem pattern_complete (d : Nat) (p : Pattern d) : p ∈ patternList d := by
  induction d with
  | zero => cases p; exact List.mem_cons_self
  | succ d ih => cases p with
    | inl b =>
        cases b
        · exact List.mem_append_left _ List.mem_cons_self
        · exact List.mem_append_left _ (List.mem_cons_of_mem _ List.mem_cons_self)
    | inr p => exact List.mem_append_right _ (List.mem_flatMap.mpr
        ⟨p.1, ih p.1, List.mem_map.mpr ⟨p.2, ih p.2, rfl⟩⟩)

def allPatterns (C : LiteralRow) (d : Nat) : List (Patterns C d) :=
  ((classList C).pi (fun _ => patternList d)).map
    (fun f b => f b (class_complete C b))

set_option maxHeartbeats 2000000 in
-- The finite dependent carrier and transcript proofs require extended elaboration fuel.
theorem all_patterns_complete (C : LiteralRow) (d : Nat) (η : Patterns C d) :
    η ∈ allPatterns C d := by
  exact List.mem_map.mpr ⟨fun b _ => η b,
    (List.mem_pi _ _).mpr (fun b _ => pattern_complete d (η b)), rfl⟩

/-- The executable list has exactly the same feasible members as the supplied finset. -/
def feasibleList (C : LiteralRow) (d : Nat) (H : History) : List (Patterns C d) :=
  (allPatterns C d).filter (fun η => feasible η H)

set_option maxHeartbeats 2000000 in
-- The finite dependent carrier and transcript proofs require extended elaboration fuel.
private theorem feasible_list_exact (C : LiteralRow) (d : Nat) (H : History)
    (η : Patterns C d) : η ∈ feasibleList C d H ↔ η ∈ feasiblePatterns C d H := by
  simp [feasibleList, feasiblePatterns, all_patterns_complete]

/-- Every distinct old class pair participates, including classes outside a chosen equation. -/
def delta {C : LiteralRow} {d : Nat} (η : Patterns C d) : Equations (Variables η) :=
  ((classList C).flatMap (fun b => ((classList C).filter (fun c => b.val < c.val)).map
    (fun c => (oldTerm η b, oldTerm η c))))

inductive PairKind where
  | nativeFailure | oldCollapse | groundBindings | feasibleNonground
  deriving DecidableEq, Repr

structure PairPlan (X : Type) where
  first : Address
  second : Address
  kind : PairKind
  bindings : List (X × Source)

def boundList {X : Type} (p : Presentation X) (S : SubstInfo) : List X :=
  p.enumeration.filter (fun x => p.code x ∈ S.subst.keys)

def collapse {X : Type} [DecidableEq X] (p : Presentation X) (S : SubstInfo)
    (Δ : Equations X) : Bool :=
  Δ.any (fun e => substitute (action p S) e.1 == substitute (action p S) e.2)

def allGround {X : Type} (p : Presentation X) (S : SubstInfo) : Bool :=
  (boundList p S).all (fun x => (termVars (action p S x)).isEmpty)

def groundBindings {X : Type} (p : Presentation X) (S : SubstInfo) : List (X × Source) :=
  (boundList p S).map (fun x =>
    (x, (groundDecoder (LMonoTy.subst S.subst (.ftvar (p.code x)))).getD (.of true)))

/-- Old collapse is decided before groundness; aliases are genuine bound keys. -/
def planPair {X : Type} [DecidableEq X] (p : Presentation X) (Δ : Equations X)
    (q r : Address) (s t : Term X) : PairPlan X :=
  match (encodeEquations p [(s,t)]).unify SubstInfo.empty with
  | .error _ => ⟨q,r,.nativeFailure,[]⟩
  | .ok S =>
      if collapse p S Δ then ⟨q,r,.oldCollapse,[]⟩
      else if allGround p S then ⟨q,r,.groundBindings,groundBindings p S⟩
      else ⟨q,r,.feasibleNonground,[]⟩

/-- Unordered distinct reached pairs are visited once in address order. -/
def pairPlans {C : LiteralRow} {d : Nat} (Q : CutSet) (η : Patterns C d) :
    List (PairPlan (Variables η)) :=
  let t := wholeTerm η
  let js := symbolicOrdered Q t
  js.flatMap (fun q => (js.filter (fun r => q < r)).map (fun r =>
    planPair (presentation η) (delta η) q r
      ((termAt q t).getD (.of (.inl true))) ((termAt r t).getD (.of (.inl true)))))

def exteriorVariables {X : Type} : SymbolicExterior X → List X
  | .of (.inl (.inr x)) => [x]
  | .of _ => []
  | .mul l r => exteriorVariables l ++ exteriorVariables r

def cellPass {C : LiteralRow} {d : Nat} (Q : CutSet) (η : Patterns C d) : Bool :=
  (exteriorVariables (symbolicExterior Q [] (wholeTerm η))).isEmpty &&
    (pairPlans Q η).all (fun p => p.kind != .feasibleNonground)

def cellBudget {C : LiteralRow} {d : Nat} (Q : CutSet) (η : Patterns C d) : Nat :=
  ((pairPlans Q η).map (fun p => (p.bindings.map (fun b => b.2.length)).sum)).sum

structure Analysis where
  rawCells : Nat
  feasibleCells : Nat
  passes : Bool
  templateMaximum : Nat
  deriving Repr

/-- Whole criterion, not a pair helper or an oracle supplied as a premise. -/
def analyze (C : LiteralRow) (Q : CutSet) (H : History) : Analysis :=
  let d := requiredDepth Q H
  let es := feasibleList C d H
  ⟨(allPatterns C d).length, es.length,
    es.all (cellPass Q), (es.map (cellBudget Q)).foldr max 0⟩

def K0 (C : LiteralRow) (Q : CutSet) (H : History) : Nat :=
  2 * (labels C).card * (2 ^ requiredDepth Q H - 1) + (analyze C Q H).templateMaximum

/-- Concrete complete-row input with one unrestricted old class and a known sibling. -/
def groundBindingInput : LiteralRow × CutSet × History :=
  let g : Source := .mul (.mul (.of true) (.of false)) (.mul (.of false) (.of true))
  (.mul (.of (.inr 0)) (FreeMagma.map Sum.inl g), {[false], [true]}, [])

/-- All relative original addresses strictly below d, including absent positions. -/
def prefixAddresses : Nat → List Address
  | 0 => []
  | d+1 => [[]] ++ (prefixAddresses d).map (false :: ·) ++
      (prefixAddresses d).map (true :: ·)

/-- Minimum retained occurrence of a class, computed only from the complete row. -/
def representative (C : LiteralRow) (b : Classes C) : Address :=
  (((holeAddresses [] C).toFinset.sort (· ≤ ·)).find?
    (fun p => holeLabel p C == some b.val)).getD []

def phaseOneTasks (C : LiteralRow) (d : Nat) : List (Classes C × Address) :=
  (classList C).flatMap (fun b => (prefixAddresses d).map (fun s => (b,s)))

def taskQueries (C : LiteralRow) (N : Nat) (task : Classes C × Address) : List Address :=
  (originalQueries N task.2).map (representative C task.1 ++ ·)

def phaseOneQueries (C : LiteralRow) (d N : Nat) : List Address :=
  (phaseOneTasks C d).flatMap (taskQueries C N)

def taskOffset (C : LiteralRow) (d N : Nat) (task : Classes C × Address) : Nat :=
  (((phaseOneTasks C d).take ((phaseOneTasks C d).idxOf task)).map
    (fun t => (taskQueries C N t).length)).sum

/-- Internal original replies are decoded from actual paid current-epoch replies. -/
def phaseOneReply (C : LiteralRow) (d N : Nat) (rs : List Reply)
    (b : Classes C) (s : Address) : Reply :=
  originalDecode N s ((rs.drop (taskOffset C d N (b,s))).take (originalQueries N s).length)

/-- Malformed reply inputs use a fixed concrete leaf; no unknown source fallback. -/
def decodePattern (reply : Address → Reply) : (d : Nat) → Address → Pattern d
  | 0, _ => ()
  | d+1, a => match reply a with
    | .alpha => .inl true
    | .beta | .absent => .inl false
    | .branch => .inr (decodePattern reply d (a ++ [false]),
        decodePattern reply d (a ++ [true]))

def selectedPatterns (C : LiteralRow) (d N : Nat) (rs : List Reply) : Patterns C d :=
  fun b => decodePattern (phaseOneReply C d N rs b) d []

def bindingAddress {C : LiteralRow} {d : Nat} (η : Patterns C d)
    (x : Variables η) : Address :=
  representative C x.1 ++ frontierAddress (η x.1) x.2

def bindingQueries {C : LiteralRow} {d : Nat} (η : Patterns C d) (N : Nat)
    (b : Variables η × Source) : List Address :=
  (templateQueries N b.2).map (bindingAddress η b.1 ++ ·)

def planQueries {C : LiteralRow} {d : Nat} (η : Patterns C d) (N : Nat)
    (p : PairPlan (Variables η)) : List Address :=
  p.bindings.flatMap (bindingQueries η N)

def phaseTwoQueries {C : LiteralRow} {d : Nat} (Q : CutSet) (η : Patterns C d)
    (N : Nat) : List Address := (pairPlans Q η).flatMap (planQueries η N)

def bindingsCheck {X : Type} (N : Nat) : List (X × Source) → List Reply → Bool
  | [], rs => rs.isEmpty
  | (_,g) :: bs, rs => templateCheck N g (rs.take (templateQueries N g).length) &&
      bindingsCheck N bs (rs.drop (templateQueries N g).length)

def planCheck {X : Type} (N : Nat) (p : PairPlan X) (rs : List Reply) : Bool :=
  p.kind == .groundBindings && bindingsCheck N p.bindings rs

def pairReplies {C : LiteralRow} {d : Nat} (η : Patterns C d) (N : Nat) :
    List (PairPlan (Variables η)) → List Reply → List (Address × Address × Bool)
  | [], _ => []
  | p :: ps, rs =>
      let n := (planQueries η N p).length
      (p.first,p.second,planCheck N p (rs.take n)) :: pairReplies η N ps (rs.drop n)

def relationReply (verdicts : List (Address × Address × Bool)) (q r : Address) : Bool :=
  q == r || verdicts.any (fun p => p.2.2 &&
    ((p.1 == q && p.2.1 == r) || (p.1 == r && p.2.1 == q)))

abbrev Record := HoleExterior × Finset (Address × Address)

/-- Full concrete exterior plus all reached ordered equality pairs. -/
def renderRecord {C : LiteralRow} {d : Nat} (Q : CutSet) (η : Patterns C d)
    (N : Nat) (rs : List Reply) : Record :=
  let js := symbolicOrdered Q (wholeTerm η)
  let rel := pairReplies η N (pairPlans Q η) rs
  (exteriorFill (fun _ => .of true) (symbolicExterior Q [] (wholeTerm η)),
    (js.toFinset.product js.toFinset).filter (fun p => relationReply rel p.1 p.2))

/-- Canonical names are least reached indices, rather than dense class ranks. -/
def recordRow (r : Record) : LiteralRow :=
  let js := (exteriorHoles [] r.1).toFinset.sort (· ≤ ·)
  FreeMagma.lift (fun b => .of (match b with
    | .inl b => .inl b
    | .inr p => .inr (js.findIdx (fun q => (q,p) ∈ r.2)))) r.1

set_option maxHeartbeats 2000000 in
-- The finite dependent carrier and transcript proofs require extended elaboration fuel.
/-- Delta is the complete old-class injectivity condition, not selected marginal constraints. -/
theorem delta_legal {C : LiteralRow} {d : Nat} (η : Patterns C d)
    (v : Variables η → Source) : Diseq (delta η) v ↔ Function.Injective (oldValues η v) := by
  have member (b c : Classes C) (lt : b.val < c.val) :
      (oldTerm η b,oldTerm η c) ∈ delta η := by
    exact List.mem_flatMap.mpr ⟨b,class_complete C b,List.mem_map.mpr
      ⟨c,List.mem_filter.mpr ⟨class_complete C c, by simpa using lt⟩,rfl⟩⟩
  have evaluateOld (b : Classes C) : NativeTermUnification.evaluate v (oldTerm η b) = oldValues η v b := oldTerm_evaluate η v b
  constructor
  · intro legal b c eq
    by_contra ne
    have valne : b.val ≠ c.val := fun he => ne (Subtype.ext he)
    rcases lt_or_gt_of_ne valne with lt | lt
    · exact legal _ (member b c lt) (by simpa only [evaluateOld] using eq)
    · exact legal _ (member c b lt) (by simpa only [evaluateOld] using eq.symm)
  · intro inj e he
    obtain ⟨b,hb,he⟩ := List.mem_flatMap.mp he
    obtain ⟨c,hc,rfl⟩ := List.mem_map.mp he
    have lt : b.val < c.val := by simpa using (List.mem_filter.mp hc).2
    intro eq
    have cls := inj (by simpa only [evaluateOld] using eq)
    have vals := congrArg Subtype.val cls
    omega

set_option maxHeartbeats 2000000 in
-- The finite dependent carrier and transcript proofs require extended elaboration fuel.
theorem prefix_addresses_count (d : Nat) : (prefixAddresses d).length = 2^d-1 := by
  induction d with
  | zero => simp [prefixAddresses]
  | succ d ih =>
      have pos := Nat.one_le_two_pow (n := d)
      simp only [prefixAddresses, List.length_append, List.length_cons, List.length_nil,
        List.length_map, ih, Nat.pow_succ]
      omega

set_option maxHeartbeats 2000000 in
-- The finite dependent carrier and transcript proofs require extended elaboration fuel.
private theorem class_list_count (C : LiteralRow) : (classList C).length = (labels C).card := by
  simp [classList]

set_option maxHeartbeats 2000000 in
-- The finite dependent carrier and transcript proofs require extended elaboration fuel.
/-- Phase one pays for every actual list entry; repeated addresses remain charged. -/
theorem phase_one_uniform_bound (C : LiteralRow) (d N : Nat) :
    (phaseOneQueries C d N).length ≤ 2 * (labels C).card * (2^d-1) := by
  have task_bound (task : Classes C × Address) : (taskQueries C N task).length ≤ 2 := by
    simpa only [taskQueries, List.length_map, listTrace, List.length_map] using
      (original_decoder_service N task.2 (.of true)).2.1
  have flat_bound (ts : List (Classes C × Address)) :
      (ts.flatMap (taskQueries C N)).length ≤ 2*ts.length := by
    induction ts with
    | nil => simp
    | cons t ts ih =>
        simp only [List.flatMap_cons, List.length_append, List.length_cons]
        have hb := task_bound t
        omega
  have count : (phaseOneTasks C d).length = (labels C).card * (2^d-1) := by
    simp [phaseOneTasks, List.length_flatMap, prefix_addresses_count, class_list_count]
  exact (flat_bound _).trans_eq (by rw [count]; ring)

set_option maxHeartbeats 2000000 in
-- The finite dependent carrier and transcript proofs require extended elaboration fuel.
private theorem phase_two_count {C : LiteralRow} {d : Nat} (Q : CutSet)
    (η : Patterns C d) (N : Nat) :
    (phaseTwoQueries Q η N).length = cellBudget Q η := by
  have binding (b : Variables η × Source) : (bindingQueries η N b).length = b.2.length := by
    simpa [bindingQueries] using (delayed_template_resources N b.2).2.1
  simp only [phaseTwoQueries, List.length_flatMap, planQueries, List.length_flatMap,
    binding, cellBudget]

set_option maxHeartbeats 2000000 in
-- The finite dependent carrier and transcript proofs require extended elaboration fuel.
private theorem fold_max_member (xs : List Nat) (n : Nat) (hn : n ∈ xs) :
    n ≤ xs.foldr max 0 := by
  induction xs with
  | nil => simp at hn
  | cons a xs ih =>
      rcases List.mem_cons.mp hn with he | he
      · subst a; exact Nat.le_max_left _ _
      · exact (ih he).trans (Nat.le_max_right _ _)

set_option maxHeartbeats 2000000 in
-- The finite dependent carrier and transcript proofs require extended elaboration fuel.
/-- The displayed common budget is independent of the certified epoch. -/
theorem two_phase_uniform_bound (C : LiteralRow) (Q : CutSet) (H : History)
    (η : Patterns C (requiredDepth Q H)) (mem : η ∈ feasiblePatterns C (requiredDepth Q H) H)
    (N : Nat) :
    (phaseOneQueries C (requiredDepth Q H) N).length +
      (phaseTwoQueries Q η N).length ≤ K0 C Q H := by
  have one := phase_one_uniform_bound C (requiredDepth Q H) N
  have hm : cellBudget Q η ∈ (feasibleList C (requiredDepth Q H) H).map (cellBudget Q) :=
    List.mem_map.mpr ⟨η,(feasible_list_exact _ _ _ _).mpr mem,rfl⟩
  have two := fold_max_member _ _ hm
  rw [phase_two_count]
  change _ ≤ 2*(labels C).card*(2^requiredDepth Q H-1) +
    ((feasibleList C (requiredDepth Q H) H).map (cellBudget Q)).foldr max 0
  omega

set_option maxHeartbeats 2000000 in
-- The finite dependent carrier and transcript proofs require extended elaboration fuel.
theorem labels_witness (C : LiteralRow) (n : Nat) (hn : n ∈ labels C)
    (a : Address) : ∃ p : Address, a ++ p ∈ holeAddresses a C ∧ holeLabel p C = some n := by
  induction C generalizing a with
  | of z => cases z with
    | inl b => simp [labels] at hn
    | inr m =>
        have eq : n = m := by simpa [labels] using hn
        subst m
        exact ⟨[],by simp [holeAddresses],rfl⟩
  | mul l r ihl ihr =>
      rcases Finset.mem_union.mp hn with hl | hr
      · obtain ⟨p,hp,he⟩ := ihl hl (a ++ [false])
        refine ⟨false :: p,?_,he⟩
        exact List.mem_append_left _ (by simpa [List.append_assoc] using hp)
      · obtain ⟨p,hp,he⟩ := ihr hr (a ++ [true])
        refine ⟨true :: p,?_,he⟩
        exact List.mem_append_right _ (by simpa [List.append_assoc] using hp)

set_option maxHeartbeats 2000000 in
-- The finite dependent carrier and transcript proofs require extended elaboration fuel.
private theorem representative_label (C : LiteralRow) (b : Classes C) :
    holeLabel (representative C b) C = some b.val := by
  obtain ⟨p,hp,he⟩ := labels_witness C b.val b.property []
  let ps := (holeAddresses [] C).toFinset.sort (· ≤ ·)
  have member : p ∈ ps := by simpa [ps] using hp
  have found : (ps.find? (fun p => holeLabel p C == some b.val)).isSome := by
    rw [List.isSome_find?]
    exact List.any_eq_true.mpr ⟨p,member,by simpa using he⟩
  obtain ⟨q,hq⟩ := Option.isSome_iff_exists.mp found
  have label : holeLabel q C = some b.val := by
    simpa using (List.find?_some hq)
  simpa [representative,ps,hq] using label

set_option maxHeartbeats 2000000 in
-- The finite dependent carrier and transcript proofs require extended elaboration fuel.
theorem representative_subtree (C : LiteralRow) (v : Classes C → Source)
    (b : Classes C) :
    subtree (representative C b) (evaluateRow (NativeCutFibers.extend C v) C) = some (v b) := by
  have label := representative_label C b
  have hat : rowAt (representative C b) C = some (.of (.inr b.val)) := by
    cases ht : rowAt (representative C b) C with
    | none => simp [holeLabel,ht] at label
    | some t => cases t with
      | mul l r => simp [holeLabel,ht] at label
      | of z => cases z with
        | inl z => simp [holeLabel,ht] at label
        | inr n =>
            have eq : n = b.val := by simpa [holeLabel,ht] using label
            rw [eq]
  simpa [evaluateRow,NativeCutFibers.extend,b.property] using
    NativeCutFibers.rowAt_evaluate C (NativeCutFibers.extend C v) _ _ hat

set_option maxHeartbeats 2000000 in
-- The finite dependent carrier and transcript proofs require extended elaboration fuel.
private theorem prefixed_replies (N : Nat) (a : Address) (u t : Source)
    (present : subtree a u = some t) (qs : List Address) :
    ((qs.map (a ++ ·)).map (fun q => readout q (substitution^[N] u))) =
      qs.map (fun q => readout q (substitution^[N] t)) := by
  have transport := NativeDepthPatterns.original_present_transport N a u t present
  have readAt := ActualLeafHistoryRigidity.actual_address_geometry.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  simp only [List.map_map,Function.comp_def]
  apply List.map_congr_left
  intro q hq
  rw [readAt,transport]

set_option maxHeartbeats 2000000 in
-- The finite dependent carrier and transcript proofs require extended elaboration fuel.
private theorem task_replies (C : LiteralRow) (v : Classes C → Source)
    (N : Nat) (b : Classes C) (s : Address) :
    originalDecode N s ((taskQueries C N (b,s)).map
      (fun q => readout q (substitution^[N] (evaluateRow (NativeCutFibers.extend C v) C)))) =
      readout s (v b) := by
  rw [taskQueries,prefixed_replies N _ _ _ (representative_subtree C v b)]
  exact original_decoder_correct N s (v b)


set_option maxHeartbeats 2000000 in
-- The finite dependent carrier and transcript proofs require extended elaboration fuel.
private theorem block_slice {A B : Type} [BEq A] [LawfulBEq A] [DecidableEq A]
    (xs : List A) (f : A → List B) (a : A) (ha : a ∈ xs) :
    ((xs.flatMap f).drop (((xs.take (xs.idxOf a)).map (fun x => (f x).length)).sum)).take
      (f a).length = f a := by
  induction xs with
  | nil => simp at ha
  | cons b xs ih =>
      by_cases eq : b = a
      · subst b
        simp
      · have mem : a ∈ xs := (List.mem_cons.mp ha).resolve_left (Ne.symm eq)
        rw [List.idxOf_cons_ne xs eq]
        simp only [List.take_succ_cons,List.map_cons,List.sum_cons,List.flatMap_cons]
        rw [List.drop_append]
        simp only [Nat.add_sub_cancel_left,List.drop_eq_nil_of_le (Nat.le_add_right _ _),List.nil_append]
        exact ih mem

set_option maxHeartbeats 2000000 in
-- The finite dependent carrier and transcript proofs require extended elaboration fuel.
private theorem phase_one_replies_correct (C : LiteralRow) (v : Classes C → Source)
    (d N : Nat) (b : Classes C) (s : Address) (hs : s ∈ prefixAddresses d) :
    phaseOneReply C d N
      ((phaseOneQueries C d N).map (fun q => readout q
        (substitution^[N] (evaluateRow (NativeCutFibers.extend C v) C)))) b s = readout s (v b) := by
  have member : (b,s) ∈ phaseOneTasks C d := List.mem_flatMap.mpr
    ⟨b,class_complete C b,List.mem_map.mpr ⟨s,hs,rfl⟩⟩
  unfold phaseOneReply taskOffset phaseOneQueries
  rw [← List.map_drop,← List.map_take]
  have counts : (taskQueries C N (b,s)).length = (originalQueries N s).length := by
    simp [taskQueries]
  rw [← counts]
  have slice := block_slice (phaseOneTasks C d) (taskQueries C N) (b,s) member
  exact (congrArg (fun qs : List Address => originalDecode N s (qs.map
    (fun q => readout q (substitution^[N] (evaluateRow (NativeCutFibers.extend C v) C))))) slice).trans
      (task_replies C v N b s)

set_option maxHeartbeats 2000000 in
-- The finite dependent carrier and transcript proofs require extended elaboration fuel.
theorem prefix_addresses_member (d : Nat) (s : Address) :
    s ∈ prefixAddresses d ↔ s.length < d := by
  induction d generalizing s with
  | zero => simp [prefixAddresses]
  | succ d ih => cases s with
    | nil => simp [prefixAddresses]
    | cons b s => cases b <;> simp [prefixAddresses,ih,Nat.succ_lt_succ_iff]

set_option maxHeartbeats 2000000 in
-- The finite dependent carrier and transcript proofs require extended elaboration fuel.
private theorem decode_pattern_bounded (d : Nat) (reply : Address → Reply)
    (a : Address) (t : Source) (same : ∀ s, s.length < d → reply (a ++ s) = readout s t) :
    decodePattern reply d a = (NativeDepthPatterns.decompose d t).1 := by
  induction d generalizing a t with
  | zero => rfl
  | succ d ih =>
      have root : reply a = readout [] t := by simpa using same [] (by simp)
      cases t with
      | of b => cases b <;> simp only [decodePattern,root,readout,NativeDepthPatterns.decompose] <;> rfl
      | mul l r =>
          have left : ∀ s, s.length < d → reply ((a ++ [false]) ++ s) = readout s l := by
            intro s hs
            rw [List.append_assoc]
            change reply (a ++ (false :: s)) = _
            rw [same (false :: s) (by simp; omega)]
            rfl
          have right : ∀ s, s.length < d → reply ((a ++ [true]) ++ s) = readout s r := by
            intro s hs
            rw [List.append_assoc]
            change reply (a ++ (true :: s)) = _
            rw [same (true :: s) (by simp; omega)]
            rfl
          rw [decodePattern,root]
          change Sum.inr (decodePattern reply d (a ++ [false]),decodePattern reply d (a ++ [true])) = _
          rw [ih _ _ left,ih _ _ right]
          rfl

set_option maxHeartbeats 2000000 in
-- The finite dependent carrier and transcript proofs require extended elaboration fuel.
/-- The paid first phase reconstructs the genuine unique old-class patterns,
including early leaves and all originally absent relative addresses. -/
theorem phase_one_patterns_correct (C : LiteralRow) (v : Classes C → Source) (d N : Nat) :
    selectedPatterns C d N
      ((phaseOneQueries C d N).map (fun q => readout q
        (substitution^[N] (evaluateRow (NativeCutFibers.extend C v) C)))) =
      fun b => (NativeDepthPatterns.decompose d (v b)).1 := by
  funext b
  apply decode_pattern_bounded
  intro s hs
  simpa using phase_one_replies_correct C v d N b s ((prefix_addresses_member d s).mpr hs)


set_option maxHeartbeats 2000000 in
-- The finite dependent carrier and transcript proofs require extended elaboration fuel.
private theorem binding_subtree {C : LiteralRow} {d : Nat} (η : Patterns C d)
    (v : Variables η → Source) (x : Variables η) :
    subtree (bindingAddress η x) (evaluate v (wholeTerm η)) = some (v x) := by
  have rep := representative_subtree C (oldValues η v) x.1
  have whole := whole_evaluate η v
  have appendSubtree := ActualLeafHistoryRigidity.actual_address_geometry.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  rw [bindingAddress,appendSubtree,whole,rep]
  exact (NativeDepthPatterns.frontier_geometry d (η x.1)).2.1 (fun f => v ⟨x.1,f⟩) x.2

set_option maxHeartbeats 2000000 in
-- The finite dependent carrier and transcript proofs require extended elaboration fuel.
private theorem bindings_check_correct {C : LiteralRow} {d : Nat} (η : Patterns C d)
    (v : Variables η → Source) (N : Nat) (bs : List (Variables η × Source)) :
    bindingsCheck N bs ((bs.flatMap (bindingQueries η N)).map
      (fun q => readout q (substitution^[N] (evaluate v (wholeTerm η))))) = true ↔
      ∀ b ∈ bs, v b.1 = b.2 := by
  induction bs with
  | nil => simp [bindingsCheck]
  | cons b bs ih =>
      have pref := prefixed_replies N (bindingAddress η b.1) _ _ (binding_subtree η v b.1)
        (templateQueries N b.2)
      have count : ((bindingQueries η N b).map
        (fun q => readout q (substitution^[N] (evaluate v (wholeTerm η))))).length =
          (templateQueries N b.2).length := by simp [bindingQueries]
      simp only [List.flatMap_cons,List.map_append,bindingsCheck]
      rw [←count,List.take_left,List.drop_left]
      rw [show ((bindingQueries η N b).map
        (fun q => readout q (substitution^[N] (evaluate v (wholeTerm η))))) =
        (templateQueries N b.2).map (fun q => readout q (substitution^[N] (v b.1))) from pref]
      simp only [Bool.and_eq_true_iff,(delayed_template_service N b.2 (v b.1)).2.1,ih,
        List.forall_mem_cons]

set_option maxHeartbeats 2000000 in
-- The finite dependent carrier and transcript proofs require extended elaboration fuel.
private theorem bound_list_exact {X : Type} (p : Presentation X) (S : SubstInfo) (x : X) :
    x ∈ boundList p S ↔ x ∈ D p S := by
  simp [boundList,D,p.complete x]

set_option maxHeartbeats 2000000 in
-- The finite dependent carrier and transcript proofs require extended elaboration fuel.
private theorem embedded_ground {X : Type} (p : Presentation X) (g : Source) :
    encode p (FreeMagma.map Sum.inl g) = NativeTermUnification.encodeGround g := by
  induction g with
  | of b => rfl
  | mul l r hl hr =>
      change NativeTermUnification.pair (encode p (FreeMagma.map Sum.inl l))
        (encode p (FreeMagma.map Sum.inl r)) = _
      rw [hl,hr]
      rfl

set_option maxHeartbeats 2000000 in
-- The finite dependent carrier and transcript proofs require extended elaboration fuel.
theorem evaluate_embedded {X : Type} (v : X → Source) (g : Source) :
    NativeTermUnification.evaluate v (FreeMagma.map Sum.inl g) = g := by
  induction g with
  | of b => rfl
  | mul l r hl hr =>
      change (NativeTermUnification.evaluate v (FreeMagma.map Sum.inl l)).mul
        (NativeTermUnification.evaluate v (FreeMagma.map Sum.inl r)) = _
      rw [hl,hr]

set_option maxHeartbeats 2000000 in
-- The finite dependent carrier and transcript proofs require extended elaboration fuel.
private theorem ground_action_value {X : Type} (p : Presentation X) (E : Equations X)
    (S : SubstInfo) (hok : (encodeEquations p E).unify SubstInfo.empty = .ok S)
    (x : X) (ground : termVars (action p S x) = []) (v : X → Source) :
    NativeTermUnification.evaluate v (action p S x) =
      (groundDecoder (LMonoTy.subst S.subst (.ftvar (p.code x)))).getD (.of true) := by
  obtain ⟨g,hg,uniq⟩ := ((parameterization p E S hok).ground_exact x).mp ground
  have encoded := (groundDecoder_exact _ g).mp hg
  have term : action p S x = FreeMagma.map Sum.inl g := by
    unfold action
    rw [←encoded,←embedded_ground p g,NativeTermUnification.decode_encode]
    rfl
  rw [term,evaluate_embedded,hg]
  rfl

set_option maxHeartbeats 2000000 in
-- The finite dependent carrier and transcript proofs require extended elaboration fuel.
private theorem ground_bindings_solve {X : Type} (p : Presentation X) (E : Equations X)
    (S : SubstInfo) (hok : (encodeEquations p E).unify SubstInfo.empty = .ok S)
    (ground : allGround p S = true) (v : X → Source) :
    Sol E v ↔ ∀ b ∈ groundBindings p S, v b.1 = b.2 := by
  have empty (x : X) (hx : x ∈ D p S) : termVars (action p S x) = [] := by
    have h := List.all_eq_true.mp ground x ((bound_list_exact p S x).mpr hx)
    simpa using h
  constructor
  · intro sol b hb
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hb
    have hd := (bound_list_exact p S x).mp hx
    have ext := congrFun (Ext_restriction p E S hok v sol) x
    rw [Ext_evaluate_action] at ext
    rw [ground_action_value p E S hok x (empty x hd)] at ext
    exact ext.symm
  · intro checks
    have same : Ext p E S hok (restriction p S v) = v := by
      funext x
      rw [Ext_evaluate_action]
      by_cases hd : x ∈ D p S
      · rw [ground_action_value p E S hok x (empty x hd)]
        exact (checks _ (List.mem_map.mpr ⟨x,(bound_list_exact p S x).mpr hd,rfl⟩)).symm
      · rw [action_identity p S x hd]
        change NativeGroundSolutionSpace.fill p S (restriction p S v) x = v x
        change p.code x ∉ S.subst.keys at hd
        simp [NativeGroundSolutionSpace.fill,hd,restriction]
    rw [←same]
    exact Ext_sol p E S hok (restriction p S v)


set_option maxHeartbeats 2000000 in
-- The finite dependent carrier and transcript proofs require extended elaboration fuel.
private theorem solution_action_fix {X : Type} (p : Presentation X) (E : Equations X)
    (S : SubstInfo) (hok : (encodeEquations p E).unify SubstInfo.empty = .ok S)
    (v : X → Source) (sol : Sol E v) (x : X) :
    NativeTermUnification.evaluate v (action p S x) = v x := by
  have fixed := congrFun (Ext_restriction p E S hok v sol) x
  exact (evaluate_restrictTerm p S v (action p S x)
    (fun y hy => action_support p E S hok x y hy)).symm.trans fixed

set_option maxHeartbeats 2000000 in
-- The finite dependent carrier and transcript proofs require extended elaboration fuel.
private theorem collapsed_pair_impossible {X : Type} [DecidableEq X]
    (p : Presentation X) (Δ : Equations X) (A B : Term X) (S : SubstInfo)
    (hok : (encodeEquations p [(A,B)]).unify SubstInfo.empty = .ok S)
    (collapsed : collapse p S Δ = true) (v : X → Source) (legal : Diseq Δ v) :
    NativeTermUnification.evaluate v A ≠ NativeTermUnification.evaluate v B := by
  intro eq
  have sol : Sol [(A,B)] v := by simpa [Sol] using eq
  have fixed : (fun x => NativeTermUnification.evaluate v (action p S x)) = v :=
    funext (solution_action_fix p [(A,B)] S hok v sol)
  obtain ⟨e,he,same⟩ := List.any_eq_true.mp collapsed
  have syntactic : substitute (action p S) e.1 = substitute (action p S) e.2 := by
    simpa using same
  have ground := congrArg (NativeTermUnification.evaluate v) syntactic
  rw [substitute_evaluate,substitute_evaluate,fixed] at ground
  exact legal e he ground

set_option maxHeartbeats 2000000 in
-- The finite dependent carrier and transcript proofs require extended elaboration fuel.
/-- Actual template replies decide a passing pair on the entire legal cell.
The source valuation appears only in this correctness statement. -/
theorem pair_plan_correct {C : LiteralRow} {d : Nat} (η : Patterns C d)
    (v : Variables η → Source) (legal : Diseq (delta η) v) (q r : Address)
    (A B : Term (Variables η))
    (passing : (planPair (presentation η) (delta η) q r A B).kind ≠ .feasibleNonground)
    (N : Nat) :
    let plan := planPair (presentation η) (delta η) q r A B
    planCheck N plan ((planQueries η N plan).map
      (fun a => readout a (substitution^[N] (evaluate v (wholeTerm η))))) = true ↔
      NativeTermUnification.evaluate v A = NativeTermUnification.evaluate v B := by
  dsimp only
  cases hs : (encodeEquations (presentation η) [(A,B)]).unify SubstInfo.empty with
  | error e =>
      have impossible : NativeTermUnification.evaluate v A ≠ NativeTermUnification.evaluate v B := by
        intro eq
        have sol : Sol [(A,B)] v := by simpa [Sol] using eq
        obtain ⟨S,success⟩ := native_complete (presentation η) [(A,B)] v sol
        rw [hs] at success
        cases success
      simp [planPair,hs,planCheck,impossible]
  | ok S =>
      by_cases collapsed : collapse (presentation η) S (delta η) = true
      · have impossible := collapsed_pair_impossible (presentation η) (delta η) A B S hs collapsed v legal
        simp [planPair,hs,collapsed,planCheck,impossible]
      · have no : collapse (presentation η) S (delta η) = false := Bool.eq_false_of_not_eq_true collapsed
        by_cases grounded : allGround (presentation η) S = true
        · have tested := bindings_check_correct η v N (groundBindings (presentation η) S)
          have semantic := ground_bindings_solve (presentation η) [(A,B)] S hs grounded v
          simpa [planPair,hs,no,grounded,planCheck,planQueries,Sol] using tested.trans semantic.symm
        · simp [planPair,hs,no,grounded] at passing


set_option maxHeartbeats 2000000 in
-- The finite dependent carrier and transcript proofs require extended elaboration fuel.
private theorem pair_replies_map {C : LiteralRow} {d : Nat} (η : Patterns C d)
    (N : Nat) (ps : List (PairPlan (Variables η))) (reply : Address → Reply) :
    pairReplies η N ps ((ps.flatMap (planQueries η N)).map reply) =
      ps.map (fun p => (p.first,p.second,planCheck N p ((planQueries η N p).map reply))) := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
      have take : (((planQueries η N p).map reply) ++
          ((ps.flatMap (planQueries η N)).map reply)).take (planQueries η N p).length =
          (planQueries η N p).map reply := by
        have raw : (((planQueries η N p).map reply) ++
          ((ps.flatMap (planQueries η N)).map reply)).take ((planQueries η N p).map reply).length =
          (planQueries η N p).map reply := List.take_left
        simpa only [List.length_map] using raw
      have drop : (((planQueries η N p).map reply) ++
          ((ps.flatMap (planQueries η N)).map reply)).drop (planQueries η N p).length =
          (ps.flatMap (planQueries η N)).map reply := by
        have raw : (((planQueries η N p).map reply) ++
          ((ps.flatMap (planQueries η N)).map reply)).drop ((planQueries η N p).map reply).length =
          (ps.flatMap (planQueries η N)).map reply := List.drop_left
        simpa only [List.length_map] using raw
      simp only [List.flatMap_cons,List.map_append,pairReplies,take,drop,ih,List.map_cons]

set_option maxHeartbeats 2000000 in
-- The finite dependent carrier and transcript proofs require extended elaboration fuel.
private theorem plan_addresses {X : Type} [DecidableEq X] (p : Presentation X)
    (Δ : Equations X) (q r : Address) (A B : Term X) :
    (planPair p Δ q r A B).first = q ∧ (planPair p Δ q r A B).second = r := by
  unfold planPair
  split <;> first | exact ⟨rfl,rfl⟩ | (split_ifs <;> exact ⟨rfl,rfl⟩)

set_option maxHeartbeats 2000000 in
-- The finite dependent carrier and transcript proofs require extended elaboration fuel.
private theorem exterior_independent {X : Type} (E : SymbolicExterior X)
    (empty : exteriorVariables E = []) (v w : X → Source) : exteriorFill v E = exteriorFill w E := by
  induction E with
  | of z => cases z with
    | inr a => rfl
    | inl z => cases z with
      | inl b => rfl
      | inr x => simp [exteriorVariables] at empty
  | mul l r ihl ihr =>
      have halves : exteriorVariables l = [] ∧ exteriorVariables r = [] := by
        simpa [exteriorVariables] using empty
      exact congrArg₂ FreeMagma.mul (ihl halves.1) (ihr halves.2)

set_option maxHeartbeats 2000000 in
-- The finite dependent carrier and transcript proofs require extended elaboration fuel.
private theorem plan_recut_correct {C : LiteralRow} (Q : CutSet) (H : History)
    (hQ : CutPrefixFree Q) (η : Patterns C (requiredDepth Q H))
    (pass : cellPass Q η = true) (v : Variables η → Source) (legal : Diseq (delta η) v)
    (N : Nat) (plan : PairPlan (Variables η)) (hp : plan ∈ pairPlans Q η) :
    planCheck N plan ((planQueries η N plan).map
      (fun a => readout a (substitution^[N] (evaluate v (wholeTerm η))))) = true ↔
      subtree plan.first (evaluate v (wholeTerm η)) = subtree plan.second (evaluate v (wholeTerm η)) := by
  obtain ⟨q,hq,hp⟩ := List.mem_flatMap.mp hp
  obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hp
  have rmem := (List.mem_filter.mp hr).1
  have info (a : Address) (ha : a ∈ symbolicOrdered Q (wholeTerm η)) :
      a ∈ Q ∧ (termAt a (wholeTerm η)).isSome := by
    simpa only [symbolicOrdered,Finset.mem_sort,Finset.mem_filter] using ha
  obtain ⟨A,aq⟩ := Option.isSome_iff_exists.mp (info q hq).2
  obtain ⟨B,ar⟩ := Option.isSome_iff_exists.mp (info r rmem).2
  have pairmem : planPair (presentation η) (delta η) q r A B ∈ pairPlans Q η := by
    exact List.mem_flatMap.mpr ⟨q,hq,List.mem_map.mpr ⟨r,hr,by simp [aq,ar]⟩⟩
  have passing : (planPair (presentation η) (delta η) q r A B).kind ≠ .feasibleNonground := by
    have all := List.all_eq_true.mp ((Bool.and_eq_true_iff.mp pass).2) _ pairmem
    simpa using all
  have qactual := (recutCell Q H hQ η v).subtrees q (info q hq).1
  have ractual := (recutCell Q H hQ η v).subtrees r (info r rmem).1
  simp only [aq,ar,Option.map_some] at qactual ractual
  simp only [aq,ar,Option.getD_some]
  have addresses := plan_addresses (presentation η) (delta η) q r A B
  rw [addresses.1,addresses.2,qactual,ractual,Option.some.injEq]
  exact pair_plan_correct η v legal q r A B passing N

set_option maxHeartbeats 2000000 in
-- The finite dependent carrier and transcript proofs require extended elaboration fuel.
/-- Complete rendered record for a passing feasible cell, with all ordered
pairs and the independent concrete exterior. -/
theorem selected_cell_record_correct {C : LiteralRow} (Q : CutSet) (H : History)
    (hQ : CutPrefixFree Q) (η : Patterns C (requiredDepth Q H))
    (pass : cellPass Q η = true) (v : Variables η → Source) (legal : Diseq (delta η) v)
    (N : Nat) :
    renderRecord Q η N ((phaseTwoQueries Q η N).map
      (fun a => readout a (substitution^[N] (evaluate v (wholeTerm η))))) =
      literalRecord Q (evaluate v (wholeTerm η)) := by
  let u := evaluate v (wholeTerm η)
  let ps := pairPlans Q η
  let verdict (p : PairPlan (Variables η)) := planCheck N p
    ((planQueries η N p).map (fun a => readout a (substitution^[N] u)))
  have certified (p : PairPlan (Variables η)) (hp : p ∈ ps) :
      verdict p = true ↔ subtree p.first u = subtree p.second u :=
    plan_recut_correct Q H hQ η pass v legal N p hp
  have actual := (recutCell Q H hQ η v).actual
  rw [←actual]
  apply Prod.ext
  · apply exterior_independent
    simpa using (Bool.and_eq_true_iff.mp pass).1
  · simp only [renderRecord,phaseTwoQueries,pair_replies_map,symbolicRecord,symbolicPartition]
    apply Finset.filter_congr
    intro pair hp
    have reached : pair.1 ∈ symbolicOrdered Q (wholeTerm η) ∧
        pair.2 ∈ symbolicOrdered Q (wholeTerm η) := by
      simpa only [Finset.product_eq_sprod,Finset.mem_product,List.mem_toFinset] using hp
    have atsame (q r : Address) (eq : q = r) : subtree q u = subtree r u := eq ▸ rfl
    have qmem : pair.1 ∈ Q := (Finset.mem_filter.mp ((Finset.mem_sort (· ≤ ·)).mp reached.1)).1
    have rmem : pair.2 ∈ Q := (Finset.mem_filter.mp ((Finset.mem_sort (· ≤ ·)).mp reached.2)).1
    rw [←(recutCell Q H hQ η v).subtrees pair.1 qmem,
      ←(recutCell Q H hQ η v).subtrees pair.2 rmem]
    rw [relationReply,Bool.or_eq_true_iff,List.any_eq_true]
    constructor
    · rintro (diagonal | ⟨z,hz,yes⟩)
      · have eq : pair.1 = pair.2 := by simpa using diagonal
        exact atsame _ _ eq
      · obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hz
        have yes' : verdict p = true ∧
          ((p.first = pair.1 ∧ p.second = pair.2) ∨
            (p.first = pair.2 ∧ p.second = pair.1)) := by simpa using yes
        have eq := (certified p hp).mp yes'.1
        rcases yes'.2 with ⟨l,r⟩ | ⟨l,r⟩
        · simpa [l,r] using eq
        · simpa [l,r] using eq.symm
    · intro eq
      by_cases diagonal : pair.1 = pair.2
      · exact Or.inl (by simpa using diagonal)
      · right
        have make (q r : Address) (hq : q ∈ symbolicOrdered Q (wholeTerm η))
            (hr : r ∈ symbolicOrdered Q (wholeTerm η)) (lt : q < r)
            (eq : subtree q u = subtree r u)
            (ends : (q = pair.1 ∧ r = pair.2) ∨ (q = pair.2 ∧ r = pair.1)) :
            ∃ z ∈ (ps.map (fun p => (p.first,p.second,verdict p))),
              z.2.2 && ((z.1 == pair.1 && z.2.1 == pair.2) ||
                (z.1 == pair.2 && z.2.1 == pair.1)) = true := by
          let p := planPair (presentation η) (delta η) q r
            ((termAt q (wholeTerm η)).getD (.of (.inl true)))
            ((termAt r (wholeTerm η)).getD (.of (.inl true)))
          have member : p ∈ ps := List.mem_flatMap.mpr
            ⟨q,hq,List.mem_map.mpr ⟨r,List.mem_filter.mpr ⟨hr,by simpa using lt⟩,rfl⟩⟩
          have addr : p.first = q ∧ p.second = r := plan_addresses (presentation η) (delta η) q r
            ((termAt q (wholeTerm η)).getD (.of (.inl true)))
            ((termAt r (wholeTerm η)).getD (.of (.inl true)))
          have result : verdict p = true := (certified p member).mpr (by simpa only [p,addr.1,addr.2] using eq)
          refine ⟨(p.first,p.second,verdict p),List.mem_map.mpr ⟨p,member,rfl⟩,?_⟩
          simp only [result,Bool.true_and]
          rw [addr.1,addr.2]
          rcases ends with ⟨l,r⟩ | ⟨l,r⟩ <;> simp [l,r]
        rcases lt_or_gt_of_ne diagonal with lt | lt
        · have found := make pair.1 pair.2 reached.1 reached.2 lt eq (Or.inl ⟨rfl,rfl⟩)
          simpa [plan_addresses] using found
        · have found := make pair.2 pair.1 reached.2 reached.1 lt eq.symm (Or.inr ⟨rfl,rfl⟩)
          simpa [plan_addresses] using found


end D5.S3.Arith.FibonacciAtomic.Observer.NativeWholeRowService
