/- GID: D5/S3/Arith/FibonacciAtomic/Observer/FiniteMenu/NativeSharedMooreSynthesis
   generality: I
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/Observer/FiniteMenu/NativeSharedMooreSynthesis
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: kind=checker; basis=terminal=atom:ff3bb899d5b2f33fe3e1101ad891ee1b39341870f099d20613050e0974f781d7; instance=D5/S3/Arith/FibonacciAtomic/Observer/FiniteMenu/NativeSharedMooreSynthesis.cyclicInput
   digest: Shared counted Moore tables transfer at identical export, state and invocation budgets and admit finite synthesis on every actual row fiber. -/

import D5.S3.Arith.FibonacciAtomic.Observer.NativeSixSourceMoore
import D5.S3.Arith.FibonacciAtomic.Observer.NativeFiniteRootMinimax
import Mathlib.Data.Set.Card

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096

namespace D5.S3.Arith.FibonacciAtomic.Observer.FiniteMenu.NativeSharedMooreSynthesis

open GenealogicalFiberTransport (Source substitution)
open ActualTreeReadoutAcquisition (Address Reply readout)
open ActualCutPartitionRecovery (LiteralRow CutSet CutPrefixFree canonicalRow evaluateRow)
open NativeCutFibers
open NativeClassRootImage
open NativeClassRootPadding
open NativeClassRootSimulation (Chart firstClass classReply firstClass_reply)
open NativeFullRootFeasibility (target actual_type native_full_root_feasibility)
open NativeFiniteRootMinimax (chartList computedTarget finite_root_minimax)
open NativeSixSourceMoore (Controller Run)

universe u v w

/-- The bounded evaluator charges exactly one invocation at each running state.
Its mathematical trace is returned for verification, not stored by the machine. -/
def evaluate {Q : Type u} {H : Type v} (step : Q → Q ⊕ H) (n : Nat) :
    Q ⊕ H → Option (H × List Q)
  | .inr h => some (h,[])
  | .inl s => match n with
    | 0 => none
    | n+1 => (evaluate step n (step s)).map (fun p => (p.1,s::p.2))

@[simp] theorem evaluate_halt {Q : Type u} {H : Type v}
    (step : Q → Q ⊕ H) (n : Nat) (h : H) :
    evaluate step n (.inr h) = some (h,[]) := by cases n <;> rfl

private theorem evaluate_length {Q : Type u} {H : Type v} (step : Q → Q ⊕ H)
    {n : Nat} {k : Q ⊕ H} {h : H} {tr : List Q}
    (ev : evaluate step n k = some (h,tr)) : tr.length ≤ n := by
  induction n generalizing k tr with
  | zero =>
      cases k with
      | inl s => simp [evaluate] at ev
      | inr z => cases Option.some.inj ev; exact Nat.zero_le _
  | succ n ih =>
      cases k with
      | inr z => cases Option.some.inj ev; exact Nat.zero_le _
      | inl s =>
          obtain ⟨⟨z,ts⟩,ht,hp⟩ := Option.map_eq_some_iff.mp ev
          cases hp
          simpa using Nat.succ_le_succ (ih ht)

/-- The executable evaluator is equivalent to the original native Run, with
its entire running-state list and the inclusive invocation budget. -/
theorem native_evaluate_iff {Q : Type u} {H : Type v} (M : Controller Q H)
    (t : Source) (n : Nat) (k : Q ⊕ H) (h : H) (tr : List Q) :
    evaluate (fun s => M.next s (readout (M.addr s) t)) n k = some (h,tr) ↔
      Run M t k tr h ∧ tr.length ≤ n := by
  constructor
  · intro ev
    refine ⟨?_,evaluate_length _ ev⟩
    induction n generalizing k tr with
    | zero =>
        cases k with
        | inl s => simp [evaluate] at ev
        | inr z => cases Option.some.inj ev; exact .halt _
    | succ n ih =>
        cases k with
        | inr z => cases Option.some.inj ev; exact .halt _
        | inl s =>
            obtain ⟨⟨z,ts⟩,ht,hp⟩ := Option.map_eq_some_iff.mp ev
            cases hp
            exact .read s (ih _ _ ht)
  · rintro ⟨run,budget⟩
    induction run generalizing n with
    | halt h => exact evaluate_halt _ _ _
    | @read s ts h tail ih =>
        cases n with
        | zero => simp at budget
        | succ n =>
            have hb : ts.length ≤ n := by simpa using budget
            simp only [evaluate,ih n hb,Option.map_some]

/-- The root comparison has precisely the same disjoint carriers, fixed
whole outputs and four reply transitions. There is no constant/free port. -/
structure RootTable (C : LiteralRow) (Q : Type u) (H : Type v) where
  coord : Q → Classes C
  next : Q → Reply → Q ⊕ H
  out : H → LiteralRow

def rootStep {C : LiteralRow} {Q : Type u} {H : Type v}
    (T : RootTable C Q H) (θ : Classes C → Option Bool) (s : Q) : Q ⊕ H :=
  T.next s (rootReply (θ (T.coord s)))

def install {C : LiteralRow} {Q : Type u} {H : Type v}
    (T : RootTable C Q H) : Controller Q H where
  addr s := NativeWholeRowService.representative C (T.coord s)
  next := T.next
  out := T.out

/-- This is finite local computation on the actually acquired class terms;
the resulting state itself is the entire exported code. -/
def exportCode {P : CutSet} (hP : CutPrefixFree P) (u₀ : Source)
    {S : Type u} (c : Chart (canonicalRow P (substitution u₀)) → S)
    (v : ImageValues (canonicalRow P (substitution u₀))) : S :=
  c ⟨types _ v.val.val,actual_type P hP (substitution u₀) v⟩

/-- The acquired full class values are in bijection with the original actual
origins. The normalized exported value is the complete initial control. -/
def NativeFeasible (P : CutSet) (C : LiteralRow) (r K q : Nat) : Prop :=
  ∃ (Q H : Type) (_ : Fintype Q) (_ : Fintype H) (M : Controller Q H)
    (code : ImageValues C → Q ⊕ H),
    (Set.range code).ncard ≤ r ∧ Fintype.card (Q ⊕ H) ≤ K ∧
    ∀ (v : ImageValues C) (u : OriginFiber P C),
      substitution u.val = evaluateRow (extend C v.val.val) C →
      ∃ h tr, Run M (substitution u.val) (code v) tr h ∧
        M.out h = canonicalRow P u.val ∧ tr.length ≤ q

def RootFeasible (C : LiteralRow) (r K q : Nat) : Prop :=
  ∃ (Q H : Type) (_ : Fintype Q) (_ : Fintype H) (T : RootTable C Q H)
    (c : Chart C → Q ⊕ H),
    (Set.range c).ncard ≤ r ∧ Fintype.card (Q ⊕ H) ≤ K ∧
    ∀ θ, ∃ h tr, evaluate (rootStep T θ.val) q (c θ) = some (h,tr) ∧
      T.out h = target C θ.val

/-- The bound ranges over every installed running state, including unused
states. It is not an input bound on admissible native words. -/
def installedWordBound {Q : Type u} {H : Type v} [Fintype Q]
    (M : Controller Q H) : Nat := by
  classical
  exact Finset.univ.sup (fun s => (M.addr s).length)

private theorem word_le_bound {Q : Type u} {H : Type v} [Fintype Q]
    (M : Controller Q H) (s : Q) : (M.addr s).length ≤ installedWordBound M := by
  classical
  exact Finset.le_sup (f := fun s => (M.addr s).length) (Finset.mem_univ s)

private def replyType : Reply → Option Bool
  | .alpha => some true | .beta => some false | _ => none

def paidCoord (C : LiteralRow) (d₀ : Classes C) (a : Address) : Classes C :=
  match firstClass C a with | .inl _ => d₀ | .inr p => p.1

def paidReply (C : LiteralRow) (a : Address) (z : Reply) : Reply :=
  match firstClass C a with
  | .inl y => y
  | .inr p => classReply p.2 (replyType z)

private theorem paid_response (C : LiteralRow) (d₀ : Classes C) (a : Address)
    (θ : Classes C → Option Bool) :
    queryReply (typeExtend C θ) a C =
      paidReply C a (rootReply (θ (paidCoord C d₀ a))) := by
  rw [firstClass_reply]
  cases hc : firstClass C a with
  | inl y => simp only [paidReply,hc]
  | inr p =>
      simp only [paidReply,paidCoord,hc]
      cases θ p.1 with
      | none => rfl
      | some b => cases b <;> rfl

def paidTable {Q : Type u} {H : Type v} (C : LiteralRow)
    (d₀ : Classes C) (M : Controller Q H) : RootTable C Q H where
  coord s := paidCoord C d₀ (M.addr s)
  next s z := M.next s (paidReply C (M.addr s) z)
  out := M.out

/-- One truthful actual origin per attained type, one common paid recoding,
and equality of the complete bounded state path at every fuel and entry.
There is no acyclicity or reachability restriction on installed states. -/
theorem paid_native_recode {Q : Type u} {H : Type v} [Fintype Q]
    (P : CutSet) (hP : CutPrefixFree P) (u₀ : Source)
    (d₀ : Classes (canonicalRow P (substitution u₀))) (M : Controller Q H) :
    let C := canonicalRow P (substitution u₀)
    ∃ (values : Chart C → ImageValues C) (origins : Chart C → OriginFiber P C),
      (∀ θ, substitution (origins θ).val = evaluateRow (extend C (values θ).val.val) C ∧
        types C (values θ).val.val = θ.val ∧
        DeepValues C (installedWordBound M) (values θ).val.val ∧
        target C θ.val = canonicalRow P (origins θ).val) ∧
      (∀ θ n k, evaluate (rootStep (paidTable C d₀ M) θ.val) n k =
        evaluate (fun s => M.next s (readout (M.addr s) (substitution (origins θ).val))) n k) := by
  classical
  dsimp only
  let C := canonicalRow P (substitution u₀)
  have witnesses (θ : Chart C) := padded_native_query_chart P hP (substitution u₀)
    (installedWordBound M) θ.val θ.property
  choose values origins image typesEq deep replies using witnesses
  refine ⟨values,origins,?_,?_⟩
  · intro θ
    refine ⟨image θ,typesEq θ,deep θ,?_⟩
    have factor := (native_full_root_feasibility P hP u₀ 1 0 (by decide)).1
      (values θ) (origins θ) (image θ)
    simpa only [typesEq θ] using factor.2.2
  · intro θ n k
    have steps : rootStep (paidTable C d₀ M) θ.val =
        fun s => M.next s (readout (M.addr s) (substitution (origins θ).val)) := by
      funext s
      rw [replies θ (M.addr s) (word_le_bound M s),paid_response C d₀]
      rfl
    rw [steps]

/-- Installing the representative literal addresses preserves the entire
state path on every original actual origin, and the actual export range is
exactly the range of the attained coloring. -/
theorem install_full_fiber {Q : Type u} {H : Type v}
    (P : CutSet) (hP : CutPrefixFree P) (u₀ : Source)
    (T : RootTable (canonicalRow P (substitution u₀)) Q H)
    (c : Chart (canonicalRow P (substitution u₀)) → Q ⊕ H) :
    (Set.range (exportCode hP u₀ c) = Set.range c) ∧
    (∀ (v : ImageValues (canonicalRow P (substitution u₀)))
      (u : OriginFiber P (canonicalRow P (substitution u₀))),
      substitution u.val = evaluateRow (extend (canonicalRow P (substitution u₀)) v.val.val)
        (canonicalRow P (substitution u₀)) →
      target (canonicalRow P (substitution u₀))
        (types (canonicalRow P (substitution u₀)) v.val.val) = canonicalRow P u.val ∧
      ∀ n k, evaluate (fun s => (install T).next s
          (readout ((install T).addr s) (substitution u.val))) n k =
        evaluate (rootStep T (types _ v.val.val)) n k) := by
  constructor
  · ext s
    constructor
    · rintro ⟨v,rfl⟩; exact ⟨_,rfl⟩
    · rintro ⟨θ,rfl⟩
      obtain ⟨v,u,image,ht,_,_⟩ := padded_native_query_chart P hP (substitution u₀) 0 θ.val θ.property
      exact ⟨v,congrArg c (Subtype.ext ht)⟩
  · intro v u image
    have bridge := native_full_root_feasibility P hP u₀ 1 0 (by decide)
    refine ⟨(bridge.1 v u image).2.2,?_⟩
    intro n k
    have steps : (fun s => (install T).next s
        (readout ((install T).addr s) (substitution u.val))) =
        rootStep T (types _ v.val.val) := by
      funext s
      rw [image]
      exact congrArg (T.next s) ((bridge.2.2.1 v (T.coord s)).2)
    rw [steps]

noncomputable def referenceValues (P : CutSet) (hP : CutPrefixFree P)
    (u₀ : Source) : ImageValues (canonicalRow P (substitution u₀)) :=
  ⟨recover P hP _ ⟨substitution u₀,rfl⟩,
    ⟨u₀,(recover_fill P hP _ ⟨substitution u₀,rfl⟩).symm⟩⟩

noncomputable def referenceType (P : CutSet) (hP : CutPrefixFree P)
    (u₀ : Source) : Chart (canonicalRow P (substitution u₀)) :=
  ⟨types _ (referenceValues P hP u₀).val.val,
    actual_type P hP (substitution u₀) (referenceValues P hP u₀)⟩

private theorem root_sufficient (P : CutSet) (hP : CutPrefixFree P)
    (u₀ : Source) (r K q : Nat)
    (feasible : RootFeasible (canonicalRow P (substitution u₀)) r K q) :
    NativeFeasible P (canonicalRow P (substitution u₀)) r K q := by
  rcases feasible with ⟨Q,H,fQ,fH,T,c,cap,states,correct⟩
  let _ := fQ
  let _ := fH
  have bridge := install_full_fiber P hP u₀ T c
  refine ⟨Q,H,fQ,fH,install T,exportCode hP u₀ c,?_,states,?_⟩
  · rw [bridge.1]; exact cap
  · intro v u image
    let θ : Chart _ := ⟨types _ v.val.val,actual_type P hP (substitution u₀) v⟩
    obtain ⟨h,tr,ev,out⟩ := correct θ
    have path := (bridge.2 v u image).2 q (c θ)
    rw [← path] at ev
    -- The equality is oriented toward the root evaluator.
    refine ⟨h,tr,?_,out.trans (bridge.2 v u image).1,?_⟩
    · exact ((native_evaluate_iff (install T) (substitution u.val) q _ h tr).mp ev).1
    · exact ((native_evaluate_iff (install T) (substitution u.val) q _ h tr).mp ev).2

/-- Exact joint export/state/call feasibility, on the full infinite fiber.
For no classes the necessity construction has one halt and no running state. -/
theorem shared_moore_feasibility (P : CutSet) (hP : CutPrefixFree P)
    (u₀ : Source) (r K q : Nat) (hr : 1 ≤ r) (hK : 1 ≤ K) :
    NativeFeasible P (canonicalRow P (substitution u₀)) r K q ↔
      RootFeasible (canonicalRow P (substitution u₀)) r K q := by
  classical
  constructor
  · intro feasible
    let C := canonicalRow P (substitution u₀)
    by_cases hd : Nonempty (Classes C)
    · obtain ⟨d₀⟩ := hd
      rcases feasible with ⟨Q,H,fQ,fH,M,code,cap,states,correct⟩
      let _ := fQ
      let _ := fH
      obtain ⟨values,origins,truth,paths⟩ := paid_native_recode P hP u₀ d₀ M
      let c : Chart C → Q ⊕ H := fun θ => code (values θ)
      refine ⟨Q,H,fQ,fH,paidTable C d₀ M,c,?_,states,?_⟩
      · exact (Set.ncard_le_ncard (by rintro s ⟨θ,rfl⟩; exact ⟨values θ,rfl⟩)).trans cap
      · intro θ
        obtain ⟨h,tr,run,out,budget⟩ := correct (values θ) (origins θ) (truth θ).1
        refine ⟨h,tr,?_,out.trans (truth θ).2.2.2.symm⟩
        rw [paths]
        exact (native_evaluate_iff M _ q _ h tr).mpr ⟨run,budget⟩
    · have empty : IsEmpty (Classes C) := ⟨fun d => hd ⟨d⟩⟩
      let _ := empty
      let θ₀ := referenceType P hP u₀
      let T : RootTable C Empty Unit := {
        coord := fun s => nomatch s
        next := fun s => nomatch s
        out := fun _ => target C θ₀.val }
      refine ⟨Empty,Unit,inferInstance,inferInstance,T,fun _ => .inr (),?_,?_,?_⟩
      · have eq : Set.range (fun _ : Chart C => (Sum.inr () : Empty ⊕ Unit)) = {Sum.inr ()} := by
          ext s
          simp only [Set.mem_range,Set.mem_singleton_iff]
          exact ⟨fun ⟨_,h⟩ => h.symm,fun h => ⟨θ₀,h.symm⟩⟩
        rw [eq,Set.ncard_singleton]
        exact hr
      · simpa using hK
      · intro θ
        refine ⟨(),[],evaluate_halt _ _ _,?_⟩
        exact congrArg (target C) (Subsingleton.elim θ₀.val θ.val)
  · exact root_sufficient P hP u₀ r K q

private theorem evaluate_unique {Q : Type u} {H : Type v} (step : Q → Q ⊕ H)
    {n m : Nat} {k : Q ⊕ H} {p p' : H × List Q}
    (a : evaluate step n k = some p) (b : evaluate step m k = some p') : p = p' := by
  induction n generalizing m k p p' with
  | zero =>
      cases k with
      | inl s => simp [evaluate] at a
      | inr h =>
          rw [evaluate_halt] at a b
          exact (Option.some.inj a).symm.trans (Option.some.inj b)
  | succ n ih =>
      cases k with
      | inr h =>
          rw [evaluate_halt] at a b
          exact (Option.some.inj a).symm.trans (Option.some.inj b)
      | inl s =>
          cases m with
          | zero => simp [evaluate] at b
          | succ m =>
              obtain ⟨x,hx,rfl⟩ := Option.map_eq_some_iff.mp a
              obtain ⟨y,hy,rfl⟩ := Option.map_eq_some_iff.mp b
              exact congrArg (fun p : H × List Q => (p.1,s::p.2)) (ih hx hy)

theorem evaluate_exact {Q : Type u} {H : Type v} (step : Q → Q ⊕ H)
    {n : Nat} {k : Q ⊕ H} {h : H} {tr : List Q}
    (ev : evaluate step n k = some (h,tr)) :
    evaluate step tr.length k = some (h,tr) := by
  induction n generalizing k tr with
  | zero => cases k <;> simp_all [evaluate]
  | succ n ih =>
      cases k with
      | inr z => cases Option.some.inj ev; rfl
      | inl s =>
          obtain ⟨⟨z,ts⟩,ht,hp⟩ := Option.map_eq_some_iff.mp ev
          cases hp
          simp only [List.length_cons,evaluate,ih ht,Option.map_some]

private theorem evaluate_suffix {Q : Type u} {H : Type v} (step : Q → Q ⊕ H)
    {n : Nat} {k : Q ⊕ H} {h : H} {tr : List Q}
    (ev : evaluate step n k = some (h,tr)) {s : Q} (hs : s ∈ tr) :
    ∃ ts, evaluate step ts.length (.inl s) = some (h,ts) ∧ ts.length ≤ tr.length := by
  induction n generalizing k tr with
  | zero => cases k <;> simp_all [evaluate]
  | succ n ih =>
      cases k with
      | inr z => cases Option.some.inj ev; simp at hs
      | inl a =>
          obtain ⟨⟨z,ts⟩,ht,hp⟩ := Option.map_eq_some_iff.mp ev
          cases hp
          rcases List.mem_cons.mp hs with he | hm
          · subst s
            exact ⟨a::ts,evaluate_exact step ev,le_rfl⟩
          · obtain ⟨us,hu,hl⟩ := ih ht hm
            exact ⟨us,hu,by simp only [List.length_cons]; omega⟩

/-- Termination excludes a repeated running state on one fixed stationary
input. Different inputs may still contribute opposite edges to the union. -/
theorem terminating_path_nodup {Q : Type u} {H : Type v} (step : Q → Q ⊕ H)
    {n : Nat} {k : Q ⊕ H} {h : H} {tr : List Q}
    (ev : evaluate step n k = some (h,tr)) : tr.Nodup := by
  induction n generalizing k tr with
  | zero => cases k <;> simp_all [evaluate]
  | succ n ih =>
      cases k with
      | inr z => cases Option.some.inj ev; exact List.nodup_nil
      | inl s =>
          obtain ⟨⟨z,ts⟩,ht,hp⟩ := Option.map_eq_some_iff.mp ev
          cases hp
          apply List.nodup_cons.mpr
          refine ⟨?_,ih ht⟩
          intro hs
          obtain ⟨us,hu,hl⟩ := evaluate_suffix _ ht hs
          have same := evaluate_unique step ev hu
          have lengths := congrArg (fun p : H × List Q => p.2.length) same
          simp only [List.length_cons] at lengths
          omega

/-- All functions on an explicitly enumerated finite domain. No choice-based
finite-type equivalence occurs in this executable definition. -/
def functions {A : Type u} {B : Type v} [DecidableEq A]
    (xs : List A) (complete : ∀ a, a ∈ xs) (ys : List B) : List (A → B) :=
  (xs.pi (fun _ => ys)).map (fun f a => f a (complete a))

private theorem functions_complete {A : Type u} {B : Type v} [DecidableEq A]
    (xs : List A) (complete : ∀ a, a ∈ xs) (ys : List B) (f : A → B)
    (hf : ∀ a, f a ∈ ys) : f ∈ functions xs complete ys := by
  apply List.mem_map.mpr
  exact ⟨fun a _ => f a,(List.mem_pi _ _).mpr (fun a _ => hf a),rfl⟩

private theorem finComplete (n : Nat) (i : Fin n) : i ∈ List.finRange n := by simp
private def replyList : List Reply := [.alpha,.beta,.branch,.absent]
private theorem reply_complete (z : Reply) : z ∈ replyList := by cases z <;> simp [replyList]

def states (a b : Nat) : List (Fin a ⊕ Fin b) :=
  (List.finRange a).map Sum.inl ++ (List.finRange b).map Sum.inr

private theorem states_complete (a b : Nat) (s : Fin a ⊕ Fin b) : s ∈ states a b := by
  cases s <;> simp [states]

/-- Canonical running/halting partitions of every total size through K.
Arbitrary partitions are represented by separately reindexing both parts. -/
structure Candidate (C : LiteralRow) (a b : Nat) where
  table : RootTable C (Fin a) (Fin b)
  color : Chart C → Fin a ⊕ Fin b

def outputList (C : LiteralRow) : List LiteralRow :=
  (chartList C).map (fun θ => computedTarget C θ.val)

def tables (C : LiteralRow) (a b : Nat) : List (RootTable C (Fin a) (Fin b)) :=
  (functions (List.finRange a) (finComplete a) (NativeWholeRowService.classList C)).flatMap
    (fun coord => (functions (List.finRange a) (finComplete a)
      (functions replyList reply_complete (states a b))).flatMap
      (fun next => (functions (List.finRange b) (finComplete b) (outputList C)).map
        (fun out => ⟨coord,next,out⟩)))

def candidates (C : LiteralRow) (a b : Nat) : List (Candidate C a b) :=
  (tables C a b).flatMap (fun T =>
    (functions (chartList C) ((finite_root_minimax C []).2.2.2.2.1) (states a b)).map
      (fun c => ⟨T,c⟩))

def check {C : LiteralRow} {a b : Nat} (A : Candidate C a b) (r q : Nat) : Bool :=
  decide (((chartList C).map A.color).toFinset.card ≤ r) &&
    (chartList C).all (fun θ => match evaluate (rootStep A.table θ.val) q (A.color θ) with
      | none => false
      | some p => decide (A.table.out p.1 = computedTarget C θ.val))

def Checked {C : LiteralRow} {a b : Nat} (A : Candidate C a b) (r q : Nat) : Prop :=
  (Set.range A.color).ncard ≤ r ∧ ∀ θ, ∃ h tr,
    evaluate (rootStep A.table θ.val) q (A.color θ) = some (h,tr) ∧
      A.table.out h = target C θ.val

private theorem color_range {C : LiteralRow} {S : Type u} [DecidableEq S]
    (c : Chart C → S) :
    Set.range c = (↑((chartList C).map c).toFinset : Set S) := by
  ext s
  simp only [Set.mem_range,Finset.mem_coe,List.mem_toFinset,List.mem_map]
  constructor
  · rintro ⟨θ,rfl⟩
    exact ⟨θ,(finite_root_minimax C []).2.2.2.2.1 θ,rfl⟩
  · rintro ⟨θ,_,h⟩; exact ⟨θ,h⟩

theorem check_spec {C : LiteralRow} {a b : Nat}
    (A : Candidate C a b) (r q : Nat) : check A r q = true ↔ Checked A r q := by
  rw [check,Bool.and_eq_true,decide_eq_true_eq]
  have rangeCard : (Set.range A.color).ncard = ((chartList C).map A.color).toFinset.card := by
    rw [color_range,Set.ncard_coe_finset]
  rw [← rangeCard]
  apply and_congr_right
  intro _
  rw [List.all_eq_true]
  constructor
  · intro all θ
    have checked := all θ ((finite_root_minimax C []).2.2.2.2.1 θ)
    cases ev : evaluate (rootStep A.table θ.val) q (A.color θ) with
    | none => simp only [ev,Bool.false_eq_true] at checked
    | some p =>
        refine ⟨p.1,p.2,rfl,?_⟩
        have out : A.table.out p.1 = computedTarget C θ.val := by simpa only [ev,decide_eq_true_eq] using checked
        exact out.trans ((finite_root_minimax C []).2.2.2.2.2 θ.val)
  · intro good θ _
    obtain ⟨h,tr,ev,out⟩ := good θ
    simp only [ev,decide_eq_true_eq]
    exact out.trans ((finite_root_minimax C []).2.2.2.2.2 θ.val).symm

theorem candidate_complete {C : LiteralRow} {a b : Nat}
    (T : RootTable C (Fin a) (Fin b)) (c : Chart C → Fin a ⊕ Fin b)
    (out : ∀ h, T.out h ∈ outputList C) :
    (⟨T,c⟩ : Candidate C a b) ∈ candidates C a b := by
  apply List.mem_flatMap.mpr
  refine ⟨T,?_,List.mem_map.mpr ⟨c,functions_complete _ _ _ c (fun θ => states_complete a b (c θ)),rfl⟩⟩
  apply List.mem_flatMap.mpr
  refine ⟨T.coord,functions_complete _ _ _ _ (fun s => NativeWholeRowService.class_complete C (T.coord s)),?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨T.next,functions_complete _ _ _ _ (fun s => functions_complete _ _ _ _
    (fun z => states_complete a b (T.next s z))),?_⟩
  exact List.mem_map.mpr ⟨T.out,functions_complete _ _ _ _ out,by cases T; rfl⟩

theorem evaluate_reindex {Q : Type u} {H : Type v}
    {Q' : Type w} {H' : Type} (e : Q ≃ Q') (f : H ≃ H')
    (step : Q → Q ⊕ H) (step' : Q' → Q' ⊕ H')
    (same : ∀ s, step' (e s) = Sum.map e f (step s)) (n : Nat) (k : Q ⊕ H) :
    evaluate step' n (Sum.map e f k) =
      (evaluate step n k).map (fun p => (f p.1,p.2.map e)) := by
  induction n generalizing k with
  | zero => cases k <;> rfl
  | succ n ih =>
      cases k with
      | inr h => rfl
      | inl s =>
          simp only [Sum.map_inl,evaluate,same,ih,Option.map_map]
          rfl

/-- Arbitrary finite carriers, arbitrary unused outputs, and all installed
states reduce to an actually enumerated candidate. Only unreachable halt
outputs are replaced; every attained complete path is preserved. -/
theorem arbitrary_carrier_completeness {C : LiteralRow} (θ₀ : Chart C)
    {Q : Type u} {H : Type v} [Fintype Q] [Fintype H]
    (T : RootTable C Q H) (c : Chart C → Q ⊕ H) (r q : Nat)
    (cap : (Set.range c).ncard ≤ r)
    (correct : ∀ θ, ∃ h tr, evaluate (rootStep T θ.val) q (c θ) = some (h,tr) ∧
      T.out h = target C θ.val) :
    ∃ A ∈ candidates C (Fintype.card Q) (Fintype.card H),
      check A r q = true := by
  classical
  let e := Fintype.equivFin Q
  let f := Fintype.equivFin H
  let out (h : H) := if T.out h ∈ outputList C then T.out h else computedTarget C θ₀.val
  have outmem (h : H) : out h ∈ outputList C := by
    dsimp only [out]
    split_ifs with hh
    · exact hh
    · exact List.mem_map.mpr ⟨θ₀,(finite_root_minimax C []).2.2.2.2.1 θ₀,rfl⟩
  let T' : RootTable C (Fin (Fintype.card Q)) (Fin (Fintype.card H)) :=
    ⟨fun s => T.coord (e.symm s),
     fun s z => Sum.map e f (T.next (e.symm s) z),fun h => out (f.symm h)⟩
  let c' : Chart C → Fin (Fintype.card Q) ⊕ Fin (Fintype.card H) := fun θ => Sum.map e f (c θ)
  let A : Candidate C (Fintype.card Q) (Fintype.card H) := ⟨T',c'⟩
  refine ⟨A,candidate_complete T' c' (fun h => outmem _),(check_spec A r q).mpr ⟨?_,?_⟩⟩
  · have rangeEq : Set.range c' = (Sum.map e f) '' Set.range c := by
      ext s; simp only [Set.mem_range,Set.mem_image]; constructor
      · rintro ⟨θ,rfl⟩; exact ⟨c θ,⟨θ,rfl⟩,rfl⟩
      · rintro ⟨s,⟨θ,rfl⟩,rfl⟩; exact ⟨θ,rfl⟩
    change (Set.range c').ncard ≤ r
    rw [rangeEq,Set.ncard_image_of_injective _ (Sum.map_injective.mpr ⟨e.injective,f.injective⟩)]
    exact cap
  · intro θ
    obtain ⟨h,tr,ev,output⟩ := correct θ
    have mapped := evaluate_reindex e f (rootStep T θ.val) (rootStep T' θ.val)
      (by intro s; simp [rootStep,T']) q (c θ)
    refine ⟨f h,tr.map e,?_,?_⟩
    · simpa only [ev,Option.map_some] using mapped
    · change out (f.symm (f h)) = target C θ.val
      rw [f.symm_apply_apply]
      have hm : T.out h ∈ outputList C := List.mem_map.mpr
        ⟨θ,(finite_root_minimax C []).2.2.2.2.1 θ,
          ((finite_root_minimax C []).2.2.2.2.2 θ.val).trans output.symm⟩
      simp only [out,if_pos hm,output]

def targetCount (C : LiteralRow) : Nat := (outputList C).toFinset.card

private theorem target_range (C : LiteralRow) :
    Set.range (fun θ : Chart C => target C θ.val) =
      (↑(outputList C).toFinset : Set LiteralRow) := by
  ext row
  simp only [Set.mem_range,Finset.mem_coe,List.mem_toFinset,outputList,List.mem_map]
  constructor
  · rintro ⟨θ,rfl⟩
    exact ⟨θ,(finite_root_minimax C []).2.2.2.2.1 θ,
      (finite_root_minimax C []).2.2.2.2.2 θ.val⟩
  · rintro ⟨θ,_,h⟩
    exact ⟨θ,((finite_root_minimax C []).2.2.2.2.2 θ.val).symm.trans h⟩

/-- Every distinct complete attained output needs a distinct fixed-output
halt; unused and equal-output halts remain counted. -/
theorem complete_output_lower {C : LiteralRow} {Q : Type u} {H : Type v}
    [Fintype H] (T : RootTable C Q H) (c : Chart C → Q ⊕ H) (q : Nat)
    (correct : ∀ θ, ∃ h tr, evaluate (rootStep T θ.val) q (c θ) = some (h,tr) ∧
      T.out h = target C θ.val) : targetCount C ≤ Fintype.card H := by
  classical
  have sub : Set.range (fun θ : Chart C => target C θ.val) ⊆ Set.range T.out := by
    rintro row ⟨θ,rfl⟩
    obtain ⟨h,_,_,out⟩ := correct θ
    exact ⟨h,out⟩
  have rangeBound : (Set.range T.out).ncard ≤ Fintype.card H := by
    simpa only [Set.image_univ,Set.ncard_univ,Nat.card_eq_fintype_card] using
      (Set.ncard_image_le (f := T.out) (s := Set.univ))
  have card := (Set.ncard_le_ncard sub).trans rangeBound
  simpa only [target_range,Set.ncard_coe_finset,targetCount,Nat.card_eq_fintype_card] using card

/-- Exact zero-call feasibility uses one actual exported code and one halt
for each attained complete output. It retains no output decoder. -/
theorem zero_call_endpoint (C : LiteralRow) (r K : Nat) :
    RootFeasible C r K 0 ↔ targetCount C ≤ r ∧ targetCount C ≤ K := by
  classical
  constructor
  · rintro ⟨Q,H,fQ,fH,T,c,cap,states,correct⟩
    let _ := fQ
    let _ := fH
    have halts := complete_output_lower T c 0 correct
    have targetAt (θ : Chart C) : ∃ h, c θ = .inr h ∧ T.out h = target C θ.val := by
      obtain ⟨h,tr,ev,out⟩ := correct θ
      cases hk : c θ with
      | inl s => simp [hk,evaluate] at ev
      | inr z =>
          rw [hk,evaluate_halt] at ev
          cases Option.some.inj ev
          exact ⟨_,rfl,out⟩
    let decode : Q ⊕ H → LiteralRow := fun s => match s with
      | .inl _ => .of (.inl true) | .inr h => T.out h
    have sub : Set.range (fun θ : Chart C => target C θ.val) ⊆ decode '' Set.range c := by
      rintro row ⟨θ,rfl⟩
      obtain ⟨h,hc,ho⟩ := targetAt θ
      exact ⟨c θ,⟨θ,rfl⟩,by simp only [hc,decode,ho]⟩
    have record := (Set.ncard_le_ncard sub).trans (Set.ncard_image_le (f := decode)
      (s := Set.range c))
    have rangeBound : targetCount C ≤ r := by
      rw [target_range,Set.ncard_coe_finset] at record
      exact record.trans cap
    have total : Fintype.card Q + Fintype.card H ≤ K := by simpa using states
    exact ⟨rangeBound,by omega⟩
  · rintro ⟨record,states⟩
    let Y := {row : LiteralRow // row ∈ (outputList C).toFinset}
    let T : RootTable C Empty Y := {
      coord := fun s => nomatch s
      next := fun s => nomatch s
      out := Subtype.val }
    let c : Chart C → Empty ⊕ Y := fun θ => .inr ⟨target C θ.val,
      by
        apply List.mem_toFinset.mpr
        exact List.mem_map.mpr ⟨θ,(finite_root_minimax C []).2.2.2.2.1 θ,
          (finite_root_minimax C []).2.2.2.2.2 θ.val⟩⟩
    have cards : Fintype.card (Empty ⊕ Y) = targetCount C := by
      simp only [Fintype.card_sum,Fintype.card_of_isEmpty,Nat.zero_add]
      exact Fintype.card_coe _
    refine ⟨Empty,Y,inferInstance,inferInstance,T,c,?_,?_,?_⟩
    · exact (Set.ncard_le_card _).trans (by simpa only [Nat.card_eq_fintype_card,cards] using record)
    · rw [cards]; exact states
    · intro θ; exact ⟨_,[],rfl,rfl⟩

/-- The sum type enumerates all positive total sizes up to K; no address
length is an argument. The state labels retain even unused installed entries. -/
def boundedCandidates (C : LiteralRow) (K : Nat) :
    List (Sigma fun a => Sigma fun b => Candidate C a b) :=
  (List.range (K+1)).flatMap (fun a =>
    ((List.range (K+1)).filter (fun b => decide (1 ≤ a+b ∧ a+b ≤ K))).flatMap
      (fun b => (candidates C a b).map (fun A => ⟨a,b,A⟩)))

def synthesize (C : LiteralRow) (r K q : Nat) :
    Option (Sigma fun a => Sigma fun b => Candidate C a b) :=
  if targetCount C ≤ K ∧ (q ≠ 0 ∨ targetCount C ≤ r) then
    (boundedCandidates C K).find? (fun A => check A.2.2 r q)
  else none

theorem bounded_mem {C : LiteralRow} {K a b : Nat} {A : Candidate C a b}
    (pos : 1 ≤ a+b) (bound : a+b ≤ K) (mem : A ∈ candidates C a b) :
    (⟨a,b,A⟩ : Sigma fun a => Sigma fun b => Candidate C a b) ∈ boundedCandidates C K := by
  apply List.mem_flatMap.mpr
  refine ⟨a,List.mem_range.mpr (by omega),List.mem_flatMap.mpr ⟨b,?_,?_⟩⟩
  · exact List.mem_filter.mpr ⟨List.mem_range.mpr (by omega),decide_eq_true ⟨pos,bound⟩⟩
  · exact List.mem_map.mpr ⟨A,mem,rfl⟩

theorem bounded_size {C : LiteralRow} {K : Nat}
    {A : Sigma fun a => Sigma fun b => Candidate C a b}
    (mem : A ∈ boundedCandidates C K) : 1 ≤ A.1+A.2.1 ∧ A.1+A.2.1 ≤ K := by
  obtain ⟨a,_,hm⟩ := List.mem_flatMap.mp mem
  obtain ⟨b,hb,hm⟩ := List.mem_flatMap.mp hm
  obtain ⟨B,_,eq⟩ := List.mem_map.mp hm
  cases eq
  exact of_decide_eq_true (List.mem_filter.mp hb).2

/-- A returned finite table installs actual representative queries and an
actually computed acquired-root export on the entire original origin fiber. -/
theorem synthesize_sound (P : CutSet) (hP : CutPrefixFree P) (u₀ : Source)
    (r K q : Nat) (A : Sigma fun a => Sigma fun b =>
      Candidate (canonicalRow P (substitution u₀)) a b)
    (found : synthesize (canonicalRow P (substitution u₀)) r K q = some A) :
    (Set.range (exportCode hP u₀ A.2.2.color)).ncard ≤ r ∧
    Fintype.card (Fin A.1 ⊕ Fin A.2.1) ≤ K ∧
    ∀ (v : ImageValues (canonicalRow P (substitution u₀)))
      (u : OriginFiber P (canonicalRow P (substitution u₀))),
      substitution u.val = evaluateRow (extend (canonicalRow P (substitution u₀)) v.val.val)
        (canonicalRow P (substitution u₀)) →
      ∃ h tr, Run (install A.2.2.table) (substitution u.val)
        (exportCode hP u₀ A.2.2.color v) tr h ∧
        A.2.2.table.out h = canonicalRow P u.val ∧ tr.length ≤ q := by
  have guard : targetCount (canonicalRow P (substitution u₀)) ≤ K ∧
      (q ≠ 0 ∨ targetCount (canonicalRow P (substitution u₀)) ≤ r) := by
    by_contra hg
    simp only [synthesize,if_neg hg] at found
    contradiction
  rw [synthesize,if_pos guard] at found
  have rawChecked : check A.2.2 r q = true :=
    List.find?_some (a := A)
      (p := fun B : Sigma fun a => Sigma fun b =>
        Candidate (canonicalRow P (substitution u₀)) a b => check B.2.2 r q) found
  have checked : Checked A.2.2 r q := (check_spec A.2.2 r q).mp rawChecked
  have size := (bounded_size (List.mem_of_find?_eq_some (a := A) found)).2
  have bridge := install_full_fiber P hP u₀ A.2.2.table A.2.2.color
  refine ⟨?_,by simpa using size,?_⟩
  · rw [bridge.1]; exact checked.1
  · intro v u image
    let θ : Chart _ := ⟨types _ v.val.val,actual_type P hP (substitution u₀) v⟩
    obtain ⟨h,tr,ev,out⟩ := checked.2 θ
    rw [← (bridge.2 v u image).2 q (A.2.2.color θ)] at ev
    obtain ⟨run,budget⟩ := (native_evaluate_iff _ _ _ _ _ _).mp ev
    exact ⟨h,tr,run,out.trans (bridge.2 v u image).1,budget⟩

/-- The executable finite procedure decides arbitrary-address native joint
feasibility at the identical three upper budgets. No word bound is supplied. -/
theorem finite_shared_synthesis (P : CutSet) (hP : CutPrefixFree P)
    (u₀ : Source) (r K q : Nat) (hr : 1 ≤ r) (hK : 1 ≤ K) :
    (synthesize (canonicalRow P (substitution u₀)) r K q).isSome = true ↔
      NativeFeasible P (canonicalRow P (substitution u₀)) r K q := by
  classical
  constructor
  · intro hs
    obtain ⟨A,hA⟩ := Option.isSome_iff_exists.mp hs
    have sound := synthesize_sound P hP u₀ r K q A hA
    exact ⟨Fin A.1,Fin A.2.1,inferInstance,inferInstance,install A.2.2.table,
      exportCode hP u₀ A.2.2.color,sound⟩
  · intro feasible
    have root := (shared_moore_feasibility P hP u₀ r K q hr hK).mp feasible
    rcases root with ⟨Q,H,fQ,fH,T,c,cap,states,correct⟩
    let _ := fQ
    let _ := fH
    let θ₀ := referenceType P hP u₀
    obtain ⟨A,mem,checked⟩ := arbitrary_carrier_completeness θ₀ T c r q cap correct
    have pos : 1 ≤ Fintype.card Q + Fintype.card H := by
      have nonempty : Nonempty (Q ⊕ H) := ⟨c θ₀⟩
      let _ := nonempty
      have hp := Fintype.card_pos (α := Q ⊕ H)
      simp only [Fintype.card_sum] at hp
      omega
    have bound : Fintype.card Q+Fintype.card H ≤ K := by simpa using states
    have inList := bounded_mem pos bound mem
    by_contra no
    have none : synthesize (canonicalRow P (substitution u₀)) r K q = none := by
      cases h : synthesize (canonicalRow P (substitution u₀)) r K q <;> simp_all
    have lower := complete_output_lower T c q correct
    have total : Fintype.card Q + Fintype.card H ≤ K := by simpa using states
    have guard : targetCount (canonicalRow P (substitution u₀)) ≤ K ∧
        (q ≠ 0 ∨ targetCount (canonicalRow P (substitution u₀)) ≤ r) := by
      refine ⟨by omega,?_⟩
      by_cases hq : q = 0
      · right
        subst q
        exact ((zero_call_endpoint _ r K).mp ⟨Q,H,fQ,fH,T,c,cap,states,correct⟩).1
      · exact Or.inl hq
    rw [synthesize,if_pos guard] at none
    have rejects := List.find?_eq_none.mp none
    exact (rejects _ inList) checked
/-- The one-hole example uses two running states and a single complete-output
halt. Beta and branch inputs traverse opposite orders of the same states. -/
def cyclicInput : Candidate (.of (.inr 0)) 2 1 where
  table := {
    coord := fun _ => ⟨0,by simp [labels]⟩
    next := fun s z => if s = 0 then
      (if z = .beta then .inl 1 else .inr 0)
      else (if z = .branch then .inl 0 else .inr 0)
    out := fun _ => .of (.inr 0) }
  color θ := if θ.val ⟨0,by simp [labels]⟩ = some false then .inl 0 else .inl 1

#print axioms native_evaluate_iff
#print axioms paid_native_recode
#print axioms install_full_fiber
#print axioms shared_moore_feasibility
#print axioms terminating_path_nodup
#print axioms arbitrary_carrier_completeness
#print axioms complete_output_lower
#print axioms zero_call_endpoint
#print axioms check_spec
#print axioms synthesize_sound
#print axioms finite_shared_synthesis
#print axioms synthesize

end D5.S3.Arith.FibonacciAtomic.Observer.FiniteMenu.NativeSharedMooreSynthesis
