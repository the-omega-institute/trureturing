/- GID: D5/S3/Arith/FibonacciAtomic/Observer/NativeFibonacciStaticScan
   generality: G
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/Observer/NativeFibonacciStaticScan
   mirror-E: none(waiver:unbounded-static-scan)
   anchors: []
   utility: none
   digest: A complete paid static scan retains every native reply and admits the full Fibonacci word encoding. -/

import D5.S3.Arith.FibonacciAtomic.Observer.NativeFibonacciActiveTable
import Mathlib.Data.List.Range
import Mathlib.Data.Fintype.Prod
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Intervals

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4000

namespace D5.S3.Arith.FibonacciAtomic.Observer.NativeFibonacciStaticScan
open GenealogicalFiberTransport (Source substitution)
open ActualTreeReadoutAcquisition (Address Reply readout)
open NativeSerialMachine (Op Event Trace Config Run nativeStep)
open NativeControlConjugacy
open D5.S1.Words.AdmissibleWords.AdmissibleCount

/-- All installed states, including states with empty actual support. -/
inductive Control (M : Nat) where
  | q : Fin (M+1) → Bool → Control M
  | b : Fin M → Bool → Bool → Control M
  | c : Fin M → Bool → Control M
  deriving DecidableEq

def start (M : Nat) : Control M := .q ⟨0, by omega⟩ false
def endpoint (M : Nat) (a : Bool) : Control M := .q ⟨M, by omega⟩ a

/-- Only beta at a scheduled data occurrence contributes one. -/
def psi : Reply → Bool | .beta => true | _ => false

def program (ps : List Address) : Control ps.length → Op (Control ps.length) Bool
  | .q i a => if hi : i.val < ps.length then
      .read ps[i.val] (fun y => .b ⟨i.val,hi⟩ a (xor a (psi y)))
    else .stop a
  | .b i a b => .read [] (fun _ => if a = b then .c i b else .b i b b)
  | .c i b => .read [] (fun _ => .q i.succ b)

/-- The inclusion is used for geometry, independently of active dispatch. -/
def embed {M : Nat} : Control M → NativeActiveParityExecution.Control M
  | .q i a => .q i a | .b i a b => .b i a b | .c i b => .c i b

private theorem embed_injective {M : Nat} : Function.Injective (@embed M) := by
  intro a b h
  cases a <;> cases b <;> simp_all [embed]

noncomputable def encode {M : Nat} (c : Control M) : Fin (NativeFibonacciActiveTable.dimension M+7) → Bool :=
  NativeFibonacciActiveTable.encode (NativeFibonacciActiveTable.path M) (embed c)
def Installed (M : Nat) := Set.range (@encode M)
private theorem encode_injective (M : Nat) : Function.Injective (@encode M) :=
  ((NativeFibonacciActiveTable.native_fibonacci_active_table M (fun _ => []) 0).2.2.1).comp embed_injective
noncomputable def encodingEquiv (M : Nat) : Control M ≃ Installed M :=
  Equiv.ofInjective encode (encode_injective M)
noncomputable def encodedProgram (ps : List Address) :
    Installed ps.length → Op (Installed ps.length) Bool :=
  reindex (encodingEquiv ps.length) (program ps)

private def controlEquiv (M : Nat) : Control M ≃
    ((Fin (M+1) × Bool) ⊕ ((Fin M × Bool × Bool) ⊕ (Fin M × Bool))) where
  toFun c := match c with
    | .q i a => .inl (i,a) | .b i a b => .inr (.inl (i,a,b)) | .c i b => .inr (.inr (i,b))
  invFun c := match c with
    | .inl (i,a) => .q i a | .inr (.inl (i,a,b)) => .b i a b | .inr (.inr (i,b)) => .c i b
  left_inv := by intro c; cases c <;> rfl
  right_inv := by rintro (⟨i,a⟩ | (⟨i,a,b⟩ | ⟨i,b⟩)) <;> rfl
instance (M : Nat) : Fintype (Control M) := Fintype.ofEquiv _ (controlEquiv M).symm

/-- Every typed Read row changes one bit; the only Stops have fixed payload. -/
def AllRows (ps : List Address) : Prop :=
  ∀ c, match program ps c with
    | .stop a => c = endpoint ps.length a
    | .read _ k => ∀ y, hammingDist (encode c) (encode (k y)) = 1
    | _ => False

private theorem all_rows (ps : List Address) : AllRows ps := by
  have rows := (NativeFibonacciActiveTable.native_fibonacci_active_table ps.length (fun _ => []) 0).2.2.2.2.2.1
  intro c
  cases c with
  | q i a =>
      by_cases hi : i.val < ps.length
      · simp only [program, hi, ↓reduceDIte]
        intro y
        have ra := rows (.q i a)
        simp only [NativeFibonacciActiveTable.nativeProgram, hi, ↓reduceDIte] at ra
        have ha := ra Reply.alpha
        have hb := ra Reply.beta
        cases y with
        | beta => simpa [encode, embed, NativeActiveParityExecution.dispatch, NativeActiveParityExecution.chi, psi, NativeFibonacciActiveTable.IsPilot] using hb
        | alpha => simpa [encode, embed, NativeActiveParityExecution.dispatch, NativeActiveParityExecution.chi, psi, NativeFibonacciActiveTable.IsPilot] using ha
        | absent => simpa [encode, embed, NativeActiveParityExecution.dispatch, NativeActiveParityExecution.chi, psi, NativeFibonacciActiveTable.IsPilot] using ha
        | branch => simpa [encode, embed, NativeActiveParityExecution.dispatch, NativeActiveParityExecution.chi, psi, NativeFibonacciActiveTable.IsPilot] using ha
      · have endval : i.val = ps.length := by have := i.isLt; omega
        simp only [program, hi, ↓reduceDIte]
        exact congrArg (fun k => Control.q k a) (Fin.ext endval)
  | b i a b =>
      have r := rows (.b i a b)
      simp only [NativeFibonacciActiveTable.nativeProgram] at r
      simp only [program]
      intro y
      by_cases same : a = b <;> simpa [encode, embed, NativeFibonacciActiveTable.IsPilot, same] using r y
  | c i b =>
      have r := rows (.c i b)
      simp only [NativeFibonacciActiveTable.nativeProgram] at r
      simp only [program]
      intro y
      have idx : (⟨i.val+1, by omega⟩ : Fin (ps.length+1)) = i.succ := Fin.ext rfl
      simpa [encode, embed, NativeFibonacciActiveTable.IsPilot, NativeActiveParityExecution.next, idx] using r y

/-- The first event is data; repeated root events retain their occurrence identity. -/
def block (u : Source) (epoch : Nat) (p : Address) : Trace :=
  .read epoch p (readout p u) ::
    List.replicate (2 + NativeActiveParityExecution.bit (psi (readout p u))) (.read epoch [] (readout [] u))
def scanTrace (u : Source) (epoch : Nat) (ps : List Address) : Trace := ps.flatMap (block u epoch)
def accumulate (u : Source) (a : Bool) (ps : List Address) : Bool :=
  ps.foldl (fun b p => xor b (psi (readout p u))) a

private theorem latch_route (ps : List Address) (i : Fin ps.length)
    (a b : Bool) (epoch : Nat) (u : Source) (tail : Trace) (out : Bool)
    (suffix : Run (program ps) (.q i.succ b) epoch u tail out) :
    Run (program ps) (.b i a b) epoch u
      (List.replicate (2 + NativeActiveParityExecution.bit (xor a b)) (.read epoch [] (readout [] u)) ++ tail) out := by
  have diag (b : Bool) (r : Run (program ps) (.q i.succ b) epoch u tail out) :
      Run (program ps) (.b i b b) epoch u
        (.read epoch [] (readout [] u) :: .read epoch [] (readout [] u) :: tail) out :=
    .read (k := fun _ => .c i b) (by simp [program]) rfl
      (.read (k := fun _ => .q i.succ b) rfl rfl r)
  by_cases equal : a = b
  · subst a
    simpa [NativeActiveParityExecution.bit] using diag b suffix
  · have r := Run.read (c := Control.b i a b) (k := fun _ => Control.b i b b)
      (by simp [program, equal]) (rfl : readout [] u = readout [] u) (diag b suffix)
    cases a <;> cases b <;>
      simp_all [NativeActiveParityExecution.bit, List.replicate_succ, List.replicate_zero]

private theorem execute_suffix (ps pre tail : List Address) (split : ps = pre ++ tail)
    (a : Bool) (epoch : Nat) (u : Source) :
    Run (program ps) (.q ⟨pre.length, by simp [split]⟩ a) epoch u
      (scanTrace u epoch tail) (accumulate u a tail) := by
  induction tail generalizing pre a with
  | nil => exact .stop (by simp [program, split, accumulate, scanTrace])
  | cons p tail ih =>
      have small : pre.length < ps.length := by simp [split]
      let idx : Fin ps.length := ⟨pre.length,small⟩
      have next := ih (pre ++ [p]) (by simpa only [List.append_assoc, List.singleton_append] using split)
        (xor a (psi (readout p u)))
      have routed := latch_route ps idx a (xor a (psi (readout p u))) epoch u
        (scanTrace u epoch tail) (accumulate u (xor a (psi (readout p u))) tail)
        (by simpa [idx] using next)
      have cancel : xor a (xor a (psi (readout p u))) = psi (readout p u) := by
        cases a <;> cases psi (readout p u) <;> rfl
      rw [cancel] at routed
      apply Run.read (k := fun y => .b idx a (xor a (psi y)))
        (by simp [program, small, idx, split]) rfl
      simpa only [scanTrace, List.flatMap_cons, block, List.cons_append, accumulate,
        List.foldl_cons, List.flatMap_def, List.append_eq] using routed

private theorem execute (ps : List Address) (u : Source) (epoch : Nat) :
    Run (program ps) (start ps.length) epoch u (scanTrace u epoch ps) (accumulate u false ps) := by
  simpa [start] using execute_suffix ps [] ps rfl false epoch u

abbrev FirstHalt := @NativeFibonacciActiveTable.FirstHalt

private theorem trace_length (ps : List Address) (u : Source) (epoch : Nat) :
    (scanTrace u epoch ps).length = 3*ps.length +
      (ps.map (fun p => NativeActiveParityExecution.bit (psi (readout p u)))).sum := by
  induction ps with
  | nil => simp [scanTrace]
  | cons p ps ih => simp [scanTrace, block, ih]; omega

private theorem trace_reads (ps : List Address) (u : Source) (epoch : Nat) :
    ∀ event ∈ scanTrace u epoch ps, ∃ p, event = .read epoch p (readout p u) := by
  intro event mem
  obtain ⟨p,_,inblock⟩ := List.mem_flatMap.mp mem
  simp only [block, List.mem_cons, List.mem_replicate] at inblock
  rcases inblock with equal | ⟨_,equal⟩
  · exact ⟨p,equal⟩
  · exact ⟨[],equal⟩

private theorem address_bill (ps : List Address) (u : Source) (epoch : Nat) (m : CostModel)
    (tariff : m.address = List.length) :
    cost m (scanTrace u epoch ps) 3 = (ps.map List.length).sum := by
  induction ps with
  | nil => simp [scanTrace, cost]
  | cons p ps ih =>
      cases h : psi (readout p u) <;>
        simp [scanTrace, block, h, NativeActiveParityExecution.bit, cost, eventCost, tariff, ih,
          List.map_append, List.sum_append, List.flatMap_def] at *
      all_goals assumption


def ReadOnly {C : Type} (δ : C → Op C Bool) : Prop :=
  ∀ c, match δ c with | .read _ _ | .stop _ => True | _ => False

private theorem stationary_reaches {C : Type} (δ : C → Op C Bool)
    (quiet : ReadOnly δ)
    (initial final : Config C)
    (reach : StateTransition.Reaches (nativeStep δ) initial final) :
    final.2.1 = initial.2.1 ∧ final.2.2.1 = initial.2.2.1 := by
  have step : ∀ x y, nativeStep δ x = some y →
      y.2.1 = x.2.1 ∧ y.2.2.1 = x.2.2.1 := by
    rintro ⟨c,e,u,log⟩ y hop
    have rows := quiet c
    cases h : δ c with
    | localStep v => simp only [h] at rows
    | applyRho v => simp only [h] at rows
    | stop a => simp only [nativeStep,h] at hop; cases hop
    | read p k =>
      simp only [nativeStep,h,Option.some.injEq] at hop
      cases hop
      exact ⟨rfl,rfl⟩
  change Relation.ReflTransGen (fun x y => nativeStep δ x = some y) initial final at reach
  induction reach with
  | refl => exact ⟨rfl,rfl⟩
  | @tail mid last _ edge ih =>
    have eq := step mid last edge
    exact ⟨eq.1.trans ih.1,eq.2.trans ih.2⟩

private theorem quiet (ps : List Address) :
    ReadOnly (program ps) := by
  intro c
  have rows := all_rows ps c
  cases h : program ps c <;> simp_all only [AllRows, h]

private theorem encoded_quiet (ps : List Address) :
    ReadOnly (encodedProgram ps) := by
  intro w
  have q := quiet ps ((encodingEquiv ps.length).symm w)
  unfold encodedProgram reindex
  cases h : program ps ((encodingEquiv ps.length).symm w) <;> simp_all only [mapOp]

/-- Actual finite-prefix supports, with no nonemptiness requirement. -/
def Support (ps : List Address) (E : Type) (initial : E → Source) (target : E → Bool)
    (c : Control ps.length) : Set (Bool × Source) :=
  {z | ∃ e n epoch log, target e = z.1 ∧
    (advance (program ps))^[n] (some (start ps.length,0,initial e,[])) = some (c,epoch,z.2,log)}
def EncodedSupport (ps : List Address) (E : Type) (initial : E → Source) (target : E → Bool)
    (w : Installed ps.length) : Set (Bool × Source) :=
  {z | ∃ e n epoch log, target e = z.1 ∧ (advance (encodedProgram ps))^[n]
    (some (encodingEquiv ps.length (start ps.length),0,initial e,[])) = some (w,epoch,z.2,log)}

structure TableFacts (ps : List Address) : Prop where
  capacity : ps.length+1 ≤ Nat.fib (NativeFibonacciActiveTable.dimension ps.length+2)
  minimal : ∀ d, d < NativeFibonacciActiveTable.dimension ps.length → Nat.fib (d+2) < ps.length+1
  injective : Function.Injective (@encode ps.length)
  admissible : ∀ c : Control ps.length, Adm (NativeFibonacciActiveTable.dimension ps.length+7) (encode c)
  cardinal : Nat.card (Installed ps.length) = 8*ps.length+2
  rows : AllRows ps
  conjugacy : Certificate (encodingEquiv ps.length) (program ps)
  supports : ∀ (E : Type) (initial : E → Source) (target : E → Bool) (c : Control ps.length),
    EncodedSupport ps E initial target (encodingEquiv ps.length c) = Support ps E initial target c
  first : ∀ c epoch u n a, FirstHalt (encodedProgram ps) (encodingEquiv ps.length c) epoch u n a ↔
    FirstHalt (program ps) c epoch u n a
  stationary : ∀ c epoch u old v k z log,
    StateTransition.Reaches (nativeStep (program ps)) (c,epoch,u,old) (v,k,z,log) →
      k = epoch ∧ z = u
  descent : ∀ c epoch u n a, Remaining (program ps) c epoch u (n+1) a →
    ∃ v event, nativeStep (program ps) (c,epoch,u,[]) = some (v,epoch,u,[event]) ∧
      FirstHalt (program ps) v epoch u n a ∧ hammingDist (encode c) (encode v) = 1

private theorem table_facts (ps : List Address) : TableFacts ps := by
  obtain ⟨cap,mini,inj,adm,_⟩ := NativeFibonacciActiveTable.native_fibonacci_active_table ps.length (fun _ => []) 0
  have cert := certificate (encodingEquiv ps.length) (program ps)
  refine ⟨cap,mini,encode_injective _,fun c => adm (embed c),?_,all_rows ps,cert,?_,?_,?_,?_⟩
  · rw [← Nat.card_congr (encodingEquiv ps.length), Nat.card_eq_fintype_card,
      Fintype.card_congr (controlEquiv ps.length)]
    simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_bool, Fintype.card_fin]
    omega
  · intro E initial target c
    ext z
    simp only [EncodedSupport, Support, Set.mem_setOf_eq]
    have prefixes : ∀ e n epoch log, (advance (encodedProgram ps))^[n]
          (some (encodingEquiv ps.length (start ps.length),0,initial e,[])) =
            some (encodingEquiv ps.length c,epoch,z.2,log) ↔
        (advance (program ps))^[n] (some (start ps.length,0,initial e,[])) = some (c,epoch,z.2,log) := by
      intro e n epoch log
      exact cert.prefixes (start ps.length,0,initial e,[]) (c,epoch,z.2,log) n
    simp only [prefixes]
  · intro c epoch u n a
    simp only [FirstHalt, NativeFibonacciActiveTable.FirstHalt, encodedProgram, cert.remaining]
  · intro c epoch u old v k z log reach
    exact stationary_reaches (program ps) (quiet ps) _ _ reach
  · rintro c epoch u n a ⟨trace,run,size⟩
    cases run with
    | stop hop => simp at size
    | localStep hop _ => have rows := all_rows ps c; rw [hop] at rows; exact rows.elim
    | update hop _ => have rows := all_rows ps c; rw [hop] at rows; exact rows.elim
    | @read c epoch u p k y trace a hop reply suffix =>
        have len : trace.length = n := by simp only [List.length_cons] at size; omega
        have rows := all_rows ps c
        rw [hop] at rows
        refine ⟨k y,.read epoch p y,?_,?_,rows y⟩
        · simp only [nativeStep,hop,reply,List.nil_append]; rfl
        · simpa only [len] using NativeFibonacciActiveTable.first_of_run _ suffix


open NativeActiveParityExecution (Chart chartOf source labels bit parity cone_read shifted_parity)
open DelayedOriginalReadout (rights rightClock right_clock_iterate right_clock_readout)
open scoped BigOperators

/-- Immutable cone-major literals in the original leaf order. -/
def coneList {h : Nat} (C : Chart h) (K : Nat) (i : Fin h) : List Address :=
  (List.range (K+1)).map (fun s => C.address i ++ rights s)
def dataList {h : Nat} (C : Chart h) (K : Nat) : List Address :=
  (List.finRange h).flatMap (coneList C K)
def contributions {h : Nat} (x : Fin h → Bool) (t : Nat) : Nat :=
  ∑ i, (t + bit (x i)) % 2
def addressMass {h : Nat} (C : Chart h) : Nat := ∑ i, (C.address i).length
def depth {h : Nat} (C : Chart h) : Nat :=
  Finset.univ.sup (fun i => (C.address i).length)

private theorem cone_law {h : Nat} (C : Chart h) (x : Fin h → Bool)
    (t s : Nat) (i : Fin h) :
    let r := readout (C.address i ++ rights s) (substitution^[t] (source C x))
    let n := t + bit (x i)
    (r = .absent ↔ n < 2*s) ∧ (r = .alpha ↔ n = 2*s) ∧
      (r = .beta ↔ n = 2*s+1) ∧ (r = .branch ↔ 2*s+2 ≤ n) := by
  have loc := cone_read C x t 0 i (rights s)
  simp only [NativeActiveParityExecution.observations, NativePollingAlignment.observations,
    Function.iterate_zero_apply, Nat.add_zero] at loc
  dsimp
  rw [loc]
  have clock : rightClock (NativeActiveParityExecution.atom (t+bit (x i))) = t+bit (x i) := by
    simpa [NativeActiveParityExecution.atom, rightClock] using
      right_clock_iterate (t+bit (x i)) (.of true)
  simpa only [clock] using right_clock_readout s (NativeActiveParityExecution.atom (t+bit (x i)))

private theorem psi_cone {h : Nat} (C : Chart h) (x : Fin h → Bool)
    (t s : Nat) (i : Fin h) :
    psi (readout (C.address i ++ rights s) (substitution^[t] (source C x))) =
      if s = (t+bit (x i))/2 then decide ((t+bit (x i))%2 = 1) else false := by
  have law := (cone_law C x t s i).2.2.1
  have arith : t+bit (x i) = 2*s+1 ↔
      s = (t+bit (x i))/2 ∧ (t+bit (x i))%2 = 1 := by omega
  rw [arith] at law
  have generic (r : Reply) : psi r = decide (r = .beta) := by cases r <;> rfl
  rw [generic]
  simp only [law]
  by_cases hs : s = (t+bit (x i))/2 <;> simp only [hs, true_and, false_and, ↓reduceIte, decide_false]

private theorem cone_count {h : Nat} (C : Chart h) (x : Fin h → Bool)
    (t K : Nat) (bound : t ≤ 2*K) (i : Fin h) :
    ((coneList C K i).map (fun p => bit (psi (readout p (substitution^[t] (source C x)))))).sum =
      (t+bit (x i))%2 := by
  have small : (t+bit (x i))/2 < K+1 := by
    have bits : bit (x i) ≤ 1 := by cases x i <;> simp [bit]
    omega
  simp only [coneList, List.map_map, Function.comp_def, psi_cone]
  rw [← List.sum_toFinset _ List.nodup_range]
  simp only [List.toFinset_range]
  have bd : bit (decide ((t+bit (x i))%2=1)) = (t+bit (x i))%2 := by
    rcases (show (t+bit (x i))%2=0 ∨ (t+bit (x i))%2=1 by omega) with hm | hm
    all_goals rw [hm]; rfl
  have single : ∀ s, bit (if s = (t+bit (x i))/2 then decide ((t+bit (x i))%2 = 1) else false) =
      if s = (t+bit (x i))/2 then (t+bit (x i))%2 else 0 := by
    intro s
    by_cases hs : s = (t+bit (x i))/2
    · rw [if_pos hs, if_pos hs, bd]
    · rw [if_neg hs, if_neg hs]; rfl
  simp_rw [single]
  simp [Finset.sum_ite_eq, small]

private theorem data_count {h : Nat} (C : Chart h) (x : Fin h → Bool)
    (t K : Nat) (bound : t ≤ 2*K) :
    ((dataList C K).map (fun p => bit (psi (readout p (substitution^[t] (source C x)))))).sum =
      contributions x t := by
  simp only [dataList, List.map_flatMap, List.flatMap_def, List.map_flatten, List.sum_flatten, List.map_map, Function.comp_def, cone_count C x t K bound]
  rw [← List.sum_toFinset _ (List.nodup_finRange h)]
  simp [contributions]

private theorem xor_sum (bs : List Bool) (a : Bool) :
    bs.foldl xor a = xor a (decide ((bs.map bit).sum % 2 = 1)) := by
  induction bs generalizing a with
  | nil => simp
  | cons b bs ih =>
      rw [List.foldl_cons, ih]
      rcases (show (bs.map bit).sum%2=0 ∨ (bs.map bit).sum%2=1 by omega) with hm | hm
      all_goals cases a <;> cases b <;> simp [bit, Nat.add_mod, hm]

theorem parity_sum (x : Nat → Bool) (n : Nat) :
    parity x n = decide (((List.range n).map (fun i => bit (x i))).sum%2 = 1) := by
  have fold : ∀ n, ((List.range n).map x).foldl xor false = parity x n := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => simp only [List.range_succ,List.map_append,List.foldl_append,
        List.map_singleton,List.foldl_cons,List.foldl_nil,ih,parity]
  rw [← fold, xor_sum]
  simp only [Bool.false_xor,List.map_map,Function.comp_def]

private theorem original_parity {h : Nat} (C : Chart h) (x : Fin h → Bool)
    (t K : Nat) (bound : t ≤ 2*K) (regime : h%2=0 ∨ t=0) :
    accumulate (substitution^[t] (source C x)) false (dataList C K) = parity (labels x) h := by
  let shifted : Nat → Bool := fun i => xor (decide (t%2=1)) (labels x i)
  have bitlaw : ∀ i : Fin h, bit (shifted i.val) = (t+bit (x i))%2 := by
    intro i
    rcases (show t%2=0 ∨ t%2=1 by omega) with ht | ht
    all_goals cases hx : x i <;> simp [shifted, labels, i.isLt, hx, bit, Nat.add_mod, ht]
  have sumlaw : (((List.range h).map (fun i => bit (shifted i))).sum) = contributions x t := by
    rw [← List.sum_toFinset _ List.nodup_range, List.toFinset_range, ← Fin.sum_univ_eq_sum_range]
    simp only [bitlaw, contributions]
  have xs := xor_sum ((dataList C K).map
    (fun p => psi (readout p (substitution^[t] (source C x))))) false
  simp only [List.foldl_map, List.map_map, Function.comp_def, Bool.false_xor] at xs
  change accumulate _ false _ = _ at xs
  rw [data_count C x t K bound] at xs
  rw [xs, ← sumlaw, ← parity_sum]
  change parity (fun i => xor (decide (t%2=1)) (labels x i)) h = _
  rw [shifted_parity]
  rcases regime with even | zero
  · simp [even]
  · simp [zero]

private theorem data_length {h : Nat} (C : Chart h) (K : Nat) :
    (dataList C K).length = h*(K+1) := by
  simp [dataList, coneList, List.length_flatMap, List.map_const']

private theorem data_address {h : Nat} (C : Chart h) (K : Nat) :
    ((dataList C K).map List.length).sum =
      (K+1)*addressMass C + h*K*(K+1)/2 := by
  have inner : ∀ i : Fin h, ((coneList C K i).map List.length).sum =
      (K+1)*(C.address i).length + K*(K+1)/2 := by
    intro i
    simp only [coneList, List.map_map, Function.comp_def, List.length_append, rights, List.length_replicate]
    rw [← List.sum_toFinset _ List.nodup_range]
    simp only [List.toFinset_range]
    rw [Finset.sum_add_distrib]
    simp only [Finset.sum_const,
      Finset.card_range, smul_eq_mul, Finset.sum_range_id, Nat.add_sub_cancel]
    congr 1
    rw [Nat.mul_comm]
  simp only [dataList, List.map_flatMap, List.flatMap_def, List.map_flatten, List.sum_flatten, List.map_map, Function.comp_def, inner]
  rw [← List.sum_toFinset _ (List.nodup_finRange h)]
  simp only [List.toFinset_finRange, Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, addressMass]
  rw [← Nat.mul_div_assoc h (Nat.two_dvd_mul_add_one K)]
  congr 1
  ring

private theorem data_maximum {h : Nat} (C : Chart h) (K : Nat) (positive : 0 < h) :
    (∀ p ∈ dataList C K, p.length ≤ depth C+K) ∧
      ∃ p ∈ dataList C K, p.length = depth C+K := by
  constructor
  · intro p hp
    obtain ⟨i,_,hp⟩ := List.mem_flatMap.mp hp
    obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hp
    have small := List.mem_range.mp hr
    have dep : (C.address i).length ≤ depth C := by
      exact Finset.le_sup (f := fun j : Fin h => (C.address j).length) (Finset.mem_univ i)
    simp only [List.length_append, rights, List.length_replicate]
    omega
  · have nonempty : (Finset.univ : Finset (Fin h)).Nonempty := ⟨⟨0,positive⟩,Finset.mem_univ _⟩
    obtain ⟨i,hi,eq⟩ := Finset.exists_mem_eq_sup Finset.univ nonempty
      (fun i : Fin h => (C.address i).length)
    refine ⟨C.address i ++ rights K, ?_, ?_⟩
    · apply List.mem_flatMap.mpr
      refine ⟨i,by simp,?_⟩
      exact List.mem_map.mpr ⟨K,by simp,rfl⟩
    · simpa only [List.length_append, rights, List.length_replicate, depth] using congrArg (· + K) eq.symm

/-- A bound on every submitted literal, with an actual attaining Read occurrence. -/
def SubmittedMaximum (trace : Trace) (L : Nat) : Prop :=
  (∀ epoch p y, Event.read epoch p y ∈ trace → p.length ≤ L) ∧
    ∃ p y, Event.read 0 p y ∈ trace ∧ p.length = L

private theorem scan_maximum (ps : List Address) (u : Source) (L : Nat)
    (upper : ∀ p ∈ ps, p.length ≤ L) (attained : ∃ p ∈ ps, p.length = L) :
    SubmittedMaximum (scanTrace u 0 ps) L := by
  constructor
  · intro epoch p y mem
    obtain ⟨q,hq,hm⟩ := List.mem_flatMap.mp mem
    simp only [block,List.mem_cons,List.mem_replicate] at hm
    rcases hm with same | ⟨_,same⟩
    · cases same; exact upper p hq
    · cases same; exact Nat.zero_le L
  · obtain ⟨p,hp,len⟩ := attained
    refine ⟨p,readout p u,?_,len⟩
    exact List.mem_flatMap.mpr ⟨p,hp,by simp only [block,List.mem_cons,true_or]⟩

set_option backward.isDefEq.respectTransparency false in
private theorem prefix_suffix {C : Type} (δ : C → Op C Bool) (quiet : ReadOnly δ)
    {c : C} {epoch : Nat} {u : Source} {trace : Trace} {a : Bool}
    (run : Run δ c epoch u trace a) (n : Nat) (old : Trace) (final : Config C)
    (reach : (advance δ)^[n] (some (c,epoch,u,old)) = some final) :
    n ≤ trace.length ∧ final.2.1 = epoch ∧ final.2.2.1 = u ∧
      final.2.2.2 = old ++ trace.take n ∧
      Run δ final.1 epoch u (trace.drop n) a := by
  have dead : ∀ m, (advance δ)^[m] none = none := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih => simp only [Function.iterate_succ_apply', ih, advance, Option.bind_none]
  induction n generalizing c epoch u trace old with
  | zero =>
      simp only [Function.iterate_zero_apply,Option.some.injEq] at reach
      subst final
      exact ⟨Nat.zero_le _,rfl,rfl,by simp,by simpa using run⟩
  | succ n ih =>
      cases run with
      | stop hop =>
          rw [Function.iterate_succ_apply] at reach
          simp only [advance,Option.bind_some,nativeStep,Config,hop] at reach
          rw [dead] at reach
          cases reach
      | localStep hop suffix => have q := quiet c; rw [hop] at q; exact q.elim
      | update hop suffix => have q := quiet c; rw [hop] at q; exact q.elim
      | @read c epoch u p k y tail a hop reply suffix =>
          have rest : (advance δ)^[n]
              (some (k y,epoch,u,old ++ [.read epoch p y])) = some final := by
            simpa only [Function.iterate_succ_apply,advance,Option.bind_some,nativeStep,Config,hop,reply] using reach
          obtain ⟨len,je,ue,log,remaining⟩ := ih suffix (old ++ [.read epoch p y]) rest
          refine ⟨by simpa only [List.length_cons] using Nat.succ_le_succ len,je,ue,?_,?_⟩
          · simpa only [List.take_succ_cons,List.append_assoc,List.singleton_append] using log
          · simpa only [List.drop_succ_cons] using remaining

/-- The native Run and its full event bill on one fixed actual entry. -/
structure ExecutionFacts (ps : List Address) (u : Source) (target : Bool)
    (trace : Trace) : Prop where
  native : Run (program ps) (start ps.length) 0 u trace target
  encoded : Run (encodedProgram ps) (encodingEquiv ps.length (start ps.length)) 0 u trace target
  chronology : trace = scanTrace u 0 ps
  first : FirstHalt (program ps) (start ps.length) 0 u trace.length target
  firstEncoded : FirstHalt (encodedProgram ps) (encodingEquiv ps.length (start ps.length))
    0 u trace.length target
  events : ∀ ev ∈ trace, ∃ p, ev = .read 0 p (readout p u)
  coordinates : ∀ m : CostModel, cost m trace 0 = trace.length ∧
    cost m trace 1 = trace.length ∧ cost m trace 2 = 0
  addresses : ∀ m : CostModel, m.address = List.length →
    cost m trace 3 = (ps.map List.length).sum
  responses : ∀ m : CostModel, cost m trace 4 =
    (ps.map (fun p => m.response (readout p u) +
      (2+bit (psi (readout p u)))*m.response (readout [] u))).sum
  actual : ∃ w, StateTransition.Reaches (nativeStep (encodedProgram ps))
      (encodingEquiv ps.length (start ps.length),0,u,[]) (w,0,u,trace) ∧
    encodedProgram ps w = .stop target ∧
    ∀ n p y, Event.read n p y ∈ trace → readout p (substitution^[n] u) = y
  prefixes : ∀ n c epoch v log,
    (advance (program ps))^[n] (some (start ps.length,0,u,[])) = some (c,epoch,v,log) →
    n ≤ trace.length ∧ epoch = 0 ∧ v = u ∧ log = trace.take n ∧
      Run (program ps) c 0 u (trace.drop n) target ∧
      FirstHalt (program ps) c 0 u (trace.length-n) target ∧
      FirstHalt (encodedProgram ps) (encodingEquiv ps.length c) 0 u (trace.length-n) target

private theorem scan_cost (ps : List Address) (u : Source) (epoch : Nat) (m : CostModel) :
    cost m (scanTrace u epoch ps) 0 = (scanTrace u epoch ps).length ∧
    cost m (scanTrace u epoch ps) 1 = (scanTrace u epoch ps).length ∧
    cost m (scanTrace u epoch ps) 2 = 0 ∧
    cost m (scanTrace u epoch ps) 4 =
      (ps.map (fun p => m.response (readout p u) +
        (2+bit (psi (readout p u)))*m.response (readout [] u))).sum := by
  have base : ∀ (log : Trace), (∀ ev ∈ log, ∃ p, ev = .read epoch p (readout p u)) →
      cost m log 0 = log.length ∧ cost m log 1 = log.length ∧ cost m log 2 = 0 := by
    intro log
    induction log with
    | nil => intro _; simp [cost]
    | cons ev log ih =>
      intro reads
      obtain ⟨p,rfl⟩ := reads ev (by simp)
      have tail := ih (fun e he => reads e (List.mem_cons_of_mem _ he))
      rcases tail with ⟨hp,hr,hu⟩
      change (1+cost m log 0 = log.length+1) ∧
        (1+cost m log 1 = log.length+1) ∧ (0+cost m log 2 = 0)
      omega
  obtain ⟨hp,hr,hu⟩ := base (scanTrace u epoch ps) (trace_reads ps u epoch)
  refine ⟨hp,hr,hu,?_⟩
  have add : ∀ s t i, cost m (s++t) i = cost m s i + cost m t i := by
    intro s t i; simp only [cost,List.map_append,List.sum_append]
  have bc : ∀ p, cost m (block u epoch p) 4 =
      m.response (readout p u)+(2+bit (psi (readout p u)))*m.response (readout [] u) := by
    intro p
    cases h : psi (readout p u) <;> simp [block,cost,eventCost,h,bit] <;> omega
  clear hp hr hu
  induction ps with
  | nil => simp [scanTrace,cost]
  | cons p ps ih =>
    have split : scanTrace u epoch (p::ps) = block u epoch p ++ scanTrace u epoch ps := by
      simp only [scanTrace,List.flatMap_cons,List.append_eq]
    rw [split,add,bc]
    simpa only [List.map_cons,List.sum_cons] using congrArg
      (fun n => m.response (readout p u)+(2+bit (psi (readout p u)))*m.response (readout [] u)+n) ih

private theorem execution_facts (ps : List Address) (u : Source) :
    ExecutionFacts ps u (accumulate u false ps) (scanTrace u 0 ps) := by
  have native := execute ps u 0
  have table := table_facts ps
  have encoded := table.conjugacy.runs _ 0 u _ _ |>.mpr native
  have first := NativeFibonacciActiveTable.first_of_run _ native
  have actual := NativeSerialMachine.actual_register_execution (encodedProgram ps) encoded u rfl []
  refine ⟨native,encoded,rfl,first,(table.first _ _ _ _ _).mpr first,
    trace_reads ps u 0,?_,address_bill ps u 0,?_,?_,?_⟩
  · intro m
    obtain ⟨hp,hr,hu,_⟩ := scan_cost ps u 0 m
    exact ⟨hp,hr,hu⟩
  · intro m
    exact (scan_cost ps u 0 m).2.2.2
  · obtain ⟨w,epoch,_,reach,halt,truth⟩ := actual
    have stationary := stationary_reaches (encodedProgram ps) (encoded_quiet ps) _ _ reach
    have zero : epoch = 0 := stationary.1
    subst epoch
    exact ⟨w,by simpa only [List.nil_append,Function.iterate_zero_apply] using reach,halt,truth⟩
  · intro n c epoch v log reach
    obtain ⟨len,ep,src,logeq,suffix⟩ := prefix_suffix (program ps) (quiet ps)
      native n [] (c,epoch,v,log) reach
    have firstSuffix := NativeFibonacciActiveTable.first_of_run (program ps) suffix
    rw [List.length_drop] at firstSuffix
    exact ⟨len,ep,src,by simpa only [List.nil_append] using logeq,suffix,firstSuffix,
      (table.first _ _ _ _ _).mpr firstSuffix⟩

/-- The complete installation also applies to the empty structural schedule. -/
theorem native_static_complete_scan (ps : List Address) (u : Source) :
    TableFacts ps ∧ ExecutionFacts ps u (accumulate u false ps) (scanTrace u 0 ps) ∧
      (scanTrace u 0 ps).length = 3*ps.length +
        (ps.map (fun p => bit (psi (readout p u)))).sum :=
  ⟨table_facts ps,execution_facts ps u,trace_length ps u 0⟩

/-- The full static upper construction uses the original independently labelled skeleton. -/
theorem original_static_parity_scan (S : Source) (x : Fin S.length → Bool)
    (t K : Nat) (bound : t ≤ 2*K) (regime : S.length%2=0 ∨ t=0) :
    let C := chartOf S
    let ps := dataList C K
    let u := substitution^[t] (source C x)
    TableFacts ps ∧ ps.length = S.length*(K+1) ∧
      ExecutionFacts ps u (parity (labels x) S.length) (scanTrace u 0 ps) ∧
      (scanTrace u 0 ps).length = 3*(S.length*(K+1)) + contributions x t ∧
      (ps.map List.length).sum = (K+1)*addressMass C + S.length*K*(K+1)/2 ∧
      (∀ p ∈ ps, p.length ≤ depth C+K) ∧ (∃ p ∈ ps, p.length = depth C+K) ∧
      SubmittedMaximum (scanTrace u 0 ps) (depth C+K) ∧
      (∀ i : Fin S.length, ∀ s : Nat,
        let n := t+bit (x i)
        let r := readout (C.address i ++ rights s) u
        n/2 ≤ K ∧
        (r = .absent ↔ n < 2*s) ∧ (r = .alpha ↔ n = 2*s) ∧
        (r = .beta ↔ n = 2*s+1) ∧ (r = .branch ↔ 2*s+2 ≤ n)) := by
  dsimp
  have exec := execution_facts (dataList (chartOf S) K) (substitution^[t] (source (chartOf S) x))
  rw [original_parity (chartOf S) x t K bound regime] at exec
  obtain ⟨upper,attained⟩ := data_maximum (chartOf S) K S.length_pos
  refine ⟨table_facts _, data_length _ _,exec,?_,data_address _ _,upper,attained,scan_maximum _ _ _ upper attained,?_⟩
  · rw [trace_length,data_length,data_count _ _ _ _ bound]
  · intro i s
    refine ⟨?_,cone_law (chartOf S) x t s i⟩
    have bits : bit (x i) ≤ 1 := by cases x i <;> simp [bit]
    omega

#print axioms native_static_complete_scan
#print axioms original_static_parity_scan
end D5.S3.Arith.FibonacciAtomic.Observer.NativeFibonacciStaticScan
