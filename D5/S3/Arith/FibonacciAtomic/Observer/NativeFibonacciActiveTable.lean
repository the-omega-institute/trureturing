/- GID: D5/S3/Arith/FibonacciAtomic/Observer/NativeFibonacciActiveTable
   generality: G
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/Observer/NativeFibonacciActiveTable
   mirror-E: none(waiver:unbounded-installed-table)
   anchors: []
   utility: none
   digest: The full active table has an injective Fibonacci-width word realization and same-source native execution. -/

import D5.S1.Words.AdmissibleWords.FibonacciGrayPath
import D5.S3.Quantum.FockSpace.ForbiddenNeighbourDeterminant
import D5.S3.Arith.FibonacciAtomic.Observer.NativeActiveParityExecution
import D5.S3.Arith.FibonacciAtomic.Observer.NativeControlConjugacy
import Mathlib.Data.Fintype.EquivFin

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 3000

namespace D5.S3.Arith.FibonacciAtomic.Observer.NativeFibonacciActiveTable

open GenealogicalFiberTransport (Source substitution)
open ActualTreeReadoutAcquisition (Address Reply readout)
open DelayedOriginalReadout (rights)
open NativeActiveParityExecution (Control Phase Chart start endpoint dispatch next chi)
open D5.S1.Words.AdmissibleWords.AdmissibleCount
open D5.S1.Words.AdmissibleWords.FibonacciGrayPath
open D5.S3.Quantum.FockSpace.ForbiddenNeighbourDeterminant (adm_iff_no_adjacent_true)
open NativeSerialMachine (Op Event Trace Config nativeStep)
open NativeControlConjugacy

private def phaseEquiv : Phase ≃ Fin 3 where
  toFun p := match p with | .first => 0 | .second => 1 | .route => 2
  invFun i := if i = 0 then .first else if i = 1 then .second else .route
  left_inv := by intro p; cases p <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

private def controlEquiv (h : Nat) : Control h ≃
    ((Fin (h+1) × Bool) ⊕ ((Fin h × Bool × Bool) ⊕ ((Fin h × Bool) ⊕ (Bool × Fin 3)))) where
  toFun c := match c with
    | .q i a => .inl (i,a)
    | .b i a b => .inr (.inl (i,a,b))
    | .c i b => .inr (.inr (.inl (i,b)))
    | .v a p => .inr (.inr (.inr (a,phaseEquiv p)))
  invFun c := match c with
    | .inl (i,a) => .q i a
    | .inr (.inl (i,a,b)) => .b i a b
    | .inr (.inr (.inl (i,b))) => .c i b
    | .inr (.inr (.inr (a,p))) => .v a (phaseEquiv.symm p)
  left_inv := by intro c; cases c <;> simp
  right_inv := by rintro (⟨i,a⟩ | (⟨i,a,b⟩ | (⟨i,b⟩ | ⟨a,p⟩))) <;> simp

instance controlFintype (h : Nat) : Fintype (Control h) :=
  Fintype.ofEquiv _ (controlEquiv h).symm

private theorem capacity_exists (h : Nat) : ∃ d, h+1 ≤ Nat.fib (d+2) :=
  ⟨h+3, le_trans (by omega) (Nat.le_fib_self (by omega))⟩

/-- The inverse Fibonacci capacity for h+1 immutable stages. -/
noncomputable def dimension (h : Nat) : Nat := Nat.find (capacity_exists h)

noncomputable def path (h : Nat) : StagePath (dimension h) h :=
  let result := exists_stage_path (dimension h) h (Nat.find_spec (capacity_exists h))
  { word := Classical.choose result
    admissible := (Classical.choose_spec result).1
    injective := (Classical.choose_spec result).2.1
    consecutive := (Classical.choose_spec result).2.2 }

def stage {h : Nat} : Control h → Fin (h+1)
  | .q i _ => i
  | .b i _ _ => i.castSucc
  | .c i _ => i.succ
  | .v _ _ => ⟨0, by omega⟩

def accumulator {h : Nat} : Control h → Bool
  | .q _ a | .b _ a _ | .v a _ => a
  | .c _ b => b

/-- Latch coordinates are L00, L01, L10, L11, in this order. -/
def hot (b r : Bool) : Fin 4 → Bool := ![!b && !r, !b && r, b && !r, b && r]

def latch {h : Nat} : Control h → Fin 4 → Bool
  | .q _ _ => ![false,false,false,false]
  | .b i _ b | .c i b => hot b (decide (i.val % 2 = 1))
  | .v _ .first => ![false,true,false,false]
  | .v _ .second => ![false,true,false,true]
  | .v _ .route => ![false,false,false,true]

def suffix {h : Nat} (c : Control h) : Fin 7 → Bool :=
  Fin.cons false (Fin.cons (accumulator c) (Fin.cons false (latch c)))

/-- One complete physical word; there is no separate phase or accumulator register. -/
def encode {d h : Nat} (p : StagePath d h) (c : Control h) : Fin (d+7) → Bool :=
  Fin.append (p.word (stage c)) (suffix c)

private theorem coordinates_injective {h : Nat} :
    Function.Injective (fun c : Control h => (stage c, accumulator c, latch c)) := by
  intro c v same
  have si := congrArg (fun x : Fin (h+1) × Bool × (Fin 4 → Bool) => x.1.val) same
  have ac := congrArg (fun x : Fin (h+1) × Bool × (Fin 4 → Bool) => x.2.1) same
  have l0 := congrArg (fun x : Fin (h+1) × Bool × (Fin 4 → Bool) => x.2.2 0) same
  have l1 := congrArg (fun x : Fin (h+1) × Bool × (Fin 4 → Bool) => x.2.2 1) same
  have l2 := congrArg (fun x : Fin (h+1) × Bool × (Fin 4 → Bool) => x.2.2 2) same
  have l3 := congrArg (fun x : Fin (h+1) × Bool × (Fin 4 → Bool) => x.2.2 3) same
  clear same
  cases c <;> cases v <;> (try casesm* Bool) <;> (try casesm* Phase) <;>
    simp [stage, accumulator, latch, hot] at si ac l0 l1 l2 l3
  all_goals try omega
  all_goals simp_all only [Control.q.injEq, Control.b.injEq, Control.c.injEq, Control.v.injEq, Fin.ext_iff]
  all_goals try omega
  all_goals simp

private theorem encode_injective {d h : Nat} (p : StagePath d h) :
    Function.Injective (encode p) := by
  intro c v same
  have sw : p.word (stage c) = p.word (stage v) := by
    funext i
    have := congrFun same (i.castAdd 7)
    simpa [encode] using this
  have tail : suffix c = suffix v := by
    funext i
    have := congrFun same (i.natAdd d)
    simpa [encode] using this
  apply coordinates_injective
  apply Prod.ext (p.injective sw)
  apply Prod.ext
  · simpa [suffix] using congrFun tail 1
  · funext i
    simpa [suffix] using congrFun tail i.succ.succ.succ

private theorem suffix_admissible {h : Nat} (c : Control h) : Adm 7 (suffix c) := by
  cases c <;> (try casesm* Bool) <;> (try casesm* Phase) <;>
    simp only [suffix, accumulator, latch]
  all_goals try decide
  all_goals rename_i i
  all_goals rcases (show i.val % 2 = 0 ∨ i.val % 2 = 1 by omega) with hi | hi
  all_goals simp [hot, hi, Adm, Fin.tail, Fin.cons_succ, Fin.succ_zero_eq_one]

private theorem encode_admissible {d h : Nat} (p : StagePath d h) (c : Control h) :
    Adm (d+7) (encode p c) := by
  rw [adm_iff_no_adjacent_true]
  intro i j adjacent
  have left := (adm_iff_no_adjacent_true d (p.word (stage c))).mp (p.admissible _)
  have right := (adm_iff_no_adjacent_true 7 (suffix c)).mp (suffix_admissible c)
  revert j adjacent
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · intro j
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · intro adjacent
      simpa [encode] using left i j adjacent
    · intro adjacent
      have zero : j = 0 := by apply Fin.ext; simp only [Fin.val_castAdd, Fin.val_natAdd] at adjacent; omega
      right
      simp [encode, zero, suffix]
  · intro j
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · intro adjacent
      simp only [Fin.val_castAdd, Fin.val_natAdd] at adjacent
      have := j.isLt
      omega
    · intro adjacent
      have near : i.val + 1 = j.val := by
        simp only [Fin.val_natAdd] at adjacent; omega
      simpa [encode] using right i j near

private theorem hamming_append {d n : Nat} (x y : Fin d → Bool) (a b : Fin n → Bool) :
    hammingDist (Fin.append x a) (Fin.append y b) = hammingDist x y + hammingDist a b := by
  simp only [hammingDist, Finset.card_eq_sum_ones, Finset.sum_filter, Fin.sum_univ_add,
    Fin.append_left, Fin.append_right]

/-- The faithful native Op presentation includes h=0 without an impossible Chart binder. -/
def nativeProgram {h : Nat} (address : Fin h → Address) (K : Nat) : Control h → Op (Control h) Bool
  | .q i a => if hi : i.val < h then
      .read (address ⟨i.val, hi⟩ ++ rights K) (dispatch ⟨i.val, hi⟩ a)
    else .stop a
  | .b i a b => .read [] (fun _ => if a = b then .c i b else .b i b b)
  | .c i b => .read [] (fun _ => next i b)
  | .v a .first => .applyRho (.v a .second)
  | .v a .second => .applyRho (.v a .route)
  | .v a .route => .read [] (fun _ => .q ⟨0, by omega⟩ a)

def IsPilot {h : Nat} : Control h → Bool
  | .q i _ => decide (i.val = 0)
  | _ => false

/-- Every declared raw reply and acknowledgement is retained, with exactly the
pilot branch holds. Stop payloads and the absence of internal actions are included. -/
def AllRows {d h : Nat} (p : StagePath d h) (address : Fin h → Address) (K : Nat) : Prop :=
  ∀ c, match nativeProgram address K c with
    | .localStep _ => False
    | .stop a => c = endpoint h a
    | .applyRho v => hammingDist (encode p c) (encode p v) = 1
    | .read _ k => ∀ y, hammingDist (encode p c) (encode p (k y)) =
        if IsPilot c ∧ y = .branch then 0 else 1

private theorem all_rows {d h : Nat} (p : StagePath d h)
    (address : Fin h → Address) (K : Nat) : AllRows p address K := by
  intro c
  cases c with
  | q i a =>
      by_cases hi : i.val < h
      · simp only [nativeProgram, hi, ↓reduceDIte]
        intro y
        by_cases hz : i.val = 0
        · have iz : i = (0 : Fin (h+1)) := Fin.ext hz
          subst i
          cases a <;> cases y <;>
            simp [dispatch, chi, IsPilot, encode, hamming_append, stage, suffix,
              accumulator, latch, hot] <;> decide
        · have mod : i.val % 2 = 0 ∨ i.val % 2 = 1 := by omega
          rcases mod with hm | hm
          all_goals cases a <;> cases y <;>
            simp [dispatch, hz, hm, chi, IsPilot, encode, hamming_append, stage,
              suffix, accumulator, latch, hot] <;> decide
      · have endval : i.val = h := by have := i.isLt; omega
        simp only [nativeProgram, hi, ↓reduceDIte]
        exact congrArg (fun j => Control.q j a) (Fin.ext endval)
  | b i a b =>
      simp only [nativeProgram]
      intro y
      have mod : i.val % 2 = 0 ∨ i.val % 2 = 1 := by omega
      rcases mod with hm | hm
      all_goals cases a <;> cases b <;>
        simp [IsPilot, encode, hamming_append, stage, suffix, accumulator, latch,
          hot, hm, p.consecutive] <;> decide
  | c i b =>
      have idx : (⟨i.val+1, by omega⟩ : Fin (h+1)) = i.succ := Fin.ext rfl
      simp only [nativeProgram]
      intro y
      have mod : i.val % 2 = 0 ∨ i.val % 2 = 1 := by omega
      rcases mod with hm | hm
      all_goals cases b <;>
        simp [IsPilot, encode, hamming_append, stage, suffix, accumulator, latch,
          hot, hm, next, idx] <;> decide
  | v a phase =>
      cases phase <;> cases a <;>
        simp [nativeProgram, IsPilot, encode, hamming_append, stage, suffix,
          accumulator, latch, hot] <;> decide

/-- Exact full installed image; even unsupported controls retain their physical words. -/
def Installed {d h : Nat} (p : StagePath d h) := Set.range (encode p)

noncomputable def encodingEquiv {d h : Nat} (p : StagePath d h) : Control h ≃ Installed p :=
  Equiv.ofInjective (encode p) (encode_injective p)

noncomputable def encodedProgram {d h : Nat} (p : StagePath d h)
    (address : Fin h → Address) (K : Nat) : Installed p → Op (Installed p) Bool :=
  reindex (encodingEquiv p) (nativeProgram address K)

private theorem read_agreement {h : Nat} (C : Chart h) (K : Nat) (c : Control h)
    (p : Address) (k : Reply → Control h)
    (hop : NativeActiveParityExecution.program C K c = .read p k) :
    nativeProgram C.address K c = .read p k := by
  cases c with
  | q i a =>
      by_cases hi : i.val < h
      · simpa only [NativeActiveParityExecution.program, nativeProgram, hi,
          ↓reduceDIte, D5.S3.ObserverMemory.Algorithms.GuardedPhaseExecution.Instruction.read.injEq,
          Op.read.injEq] using hop
      · simp [NativeActiveParityExecution.program, hi] at hop
  | b i a b =>
      simpa only [NativeActiveParityExecution.program, nativeProgram,
        D5.S3.ObserverMemory.Algorithms.GuardedPhaseExecution.Instruction.read.injEq,
        Op.read.injEq] using hop
  | c i b =>
      simpa only [NativeActiveParityExecution.program, nativeProgram,
        D5.S3.ObserverMemory.Algorithms.GuardedPhaseExecution.Instruction.read.injEq,
        Op.read.injEq] using hop
  | v a phase =>
      cases phase <;> simp [NativeActiveParityExecution.program, nativeProgram,
        D5.S3.ObserverMemory.Algorithms.GuardedPhaseExecution.Instruction.read.injEq,
        Op.read.injEq] at hop ⊢ <;> exact hop

private theorem update_agreement {h : Nat} (C : Chart h) (K : Nat) (c v : Control h)
    (hop : NativeActiveParityExecution.program C K c = .update v) :
    nativeProgram C.address K c = .applyRho v := by
  cases c with
  | q i a =>
      by_cases hi : i.val < h <;> simp [NativeActiveParityExecution.program, hi] at hop
  | b i a b => simp [NativeActiveParityExecution.program] at hop
  | c i b => simp [NativeActiveParityExecution.program] at hop
  | v a phase =>
      cases phase <;> simp [NativeActiveParityExecution.program, nativeProgram,
        D5.S3.ObserverMemory.Algorithms.GuardedPhaseExecution.Instruction.update.injEq,
        Op.applyRho.injEq] at hop ⊢ <;> exact hop

def updates : Trace → Nat
  | [] => 0
  | .update _ :: rest => 1 + updates rest
  | _ :: rest => updates rest

private theorem guarded_native {h : Nat} (C : Chart h) (K : Nat) (u : Source)
    {c z : Control h} {j J : Nat} {a : Bool}
    (run : D5.S3.ObserverMemory.Algorithms.GuardedPhaseExecution.Run
      (NativeActiveParityExecution.program C K)
      (fun n p => readout p (substitution^[n] u)) c j z J)
    (halt : nativeProgram C.address K z = .stop a) :
    ∃ trace, NativeSerialMachine.Run (nativeProgram C.address K) c j
      (substitution^[j] u) trace a ∧ updates trace + j = J := by
  induction run with
  | refl => exact ⟨[], .stop halt, by simp [updates]⟩
  | read hop _ ih =>
      obtain ⟨trace, actual, epoch⟩ := ih halt
      exact ⟨.read _ _ _ :: trace, .read (read_agreement C K _ _ _ hop) rfl actual, epoch⟩
  | update hop _ ih =>
      obtain ⟨trace, actual, epoch⟩ := ih halt
      refine ⟨.update _ :: trace, .update (update_agreement C K _ _ hop) ?_, ?_⟩
      · simpa only [Function.iterate_succ_apply'] using actual
      · simp only [updates]; omega

/-- Exact reached target/current-source fibers at a complete word. Epoch and log
are existential proof coordinates, never inputs to the controller. -/
def Support {h : Nat} (address : Fin h → Address) (K : Nat)
    (entry : Type) (initial : entry → Source) (target : entry → Bool)
    (c : Control h) : Set (Bool × Source) :=
  { z | ∃ e n j log, target e = z.1 ∧
    (advance (nativeProgram address K))^[n] (some (start h,0,initial e,[])) =
      some (c,j,z.2,log) }

def EncodedSupport {d h : Nat} (p : StagePath d h) (address : Fin h → Address) (K : Nat)
    (entry : Type) (initial : entry → Source) (target : entry → Bool)
    (w : Installed p) : Set (Bool × Source) :=
  { z | ∃ e n j log, target e = z.1 ∧
    (advance (encodedProgram p address K))^[n]
      (some (encodingEquiv p (start h),0,initial e,[])) = some (w,j,z.2,log) }

/-- First terminating primitive count and fixed payload. -/
def FirstHalt {C : Type} (δ : C → Op C Bool) (c : C) (j : Nat)
    (u : Source) (n : Nat) (a : Bool) : Prop :=
  Remaining δ c j u n a ∧ ∀ k, k < n → ∀ b, ¬ Remaining δ c j u k b

theorem first_of_run {C : Type} (δ : C → Op C Bool)
    {c : C} {j : Nat} {u : Source} {trace : Trace} {a : Bool}
    (run : NativeSerialMachine.Run δ c j u trace a) : FirstHalt δ c j u trace.length a := by
  refine ⟨⟨trace,run,rfl⟩, ?_⟩
  intro k small b other
  obtain ⟨s,second,size⟩ := other
  have same := (certificate (Equiv.refl C) δ).deterministic
    c j u trace s a b run second
  have := congrArg List.length same.1
  omega

/-- A supported remaining-primitive count decreases at the next actual event.
The source, epoch and one appended event are exposed explicitly. -/
def RankDescent {d h : Nat} (p : StagePath d h) (address : Fin h → Address) (K : Nat) : Prop :=
  ∀ c j u n a, Remaining (nativeProgram address K) c j u (n+1) a →
    ∃ v k z event, nativeStep (nativeProgram address K) (c,j,u,[]) = some (v,k,z,[event]) ∧
      FirstHalt (nativeProgram address K) v k z n a ∧
      hammingDist (encode p c) (encode p v) = 1

private theorem rank_descent {d h : Nat} (p : StagePath d h)
    (address : Fin h → Address) (K : Nat) : RankDescent p address K := by
  intro c j u n a remaining
  obtain ⟨trace,run,size⟩ := remaining
  cases run with
  | stop hop => simp at size
  | localStep hop _ =>
      have rows := all_rows p address K c
      rw [hop] at rows
      exact rows.elim
  | @update c v j u trace a hop suffix =>
      have len : trace.length = n := by simp only [List.length_cons] at size; omega
      have rows := all_rows p address K c
      rw [hop] at rows
      refine ⟨v,j+1,substitution u,.update j,?_,?_,rows⟩
      · simp only [nativeStep, hop, List.nil_append]
        rfl
      · simpa only [len] using first_of_run _ suffix
  | @read c j u address' k y trace a hop reply suffix =>
      have len : trace.length = n := by simp only [List.length_cons] at size; omega
      have rows := all_rows p address K c
      rw [hop] at rows
      have edge := rows y
      have distance : hammingDist (encode p c) (encode p (k y)) = 1 := by
        by_cases hold : IsPilot c ∧ y = .branch
        · have zero : hammingDist (encode p c) (encode p (k y)) = 0 := by simpa [hold] using edge
          have equal := encode_injective p (hammingDist_eq_zero.mp zero)
          have same := (certificate (Equiv.refl (Control h))
            (nativeProgram address K)).deterministic c j u
            (.read j address' y :: trace) trace a a (.read hop reply suffix)
            (by simpa only [equal] using suffix)
          have := congrArg List.length same.1
          simp only [List.length_cons] at this
          omega
        · simpa [hold] using edge
      refine ⟨k y,j,u,.read j address' y,?_,?_,distance⟩
      · simp only [nativeStep,hop,reply,List.nil_append]
        rfl
      · simpa only [len] using first_of_run _ suffix

private theorem control_card (h : Nat) : Nat.card (Control h) = 8*h+8 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_congr (controlEquiv h)]
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_bool, Fintype.card_fin]
  omega

/-- Complete installed-table construction. The support family may contain empty
fibers, and need not assert a source-independent replacement device. -/
theorem native_fibonacci_active_table (h : Nat) (address : Fin h → Address) (K : Nat) :
    h+1 ≤ Nat.fib (dimension h+2) ∧
    (∀ d, d < dimension h → Nat.fib (d+2) < h+1) ∧
    Function.Injective (encode (path h)) ∧
    (∀ c, Adm (dimension h+7) (encode (path h) c)) ∧
    Nat.card (Installed (path h)) = 8*h+8 ∧
    AllRows (path h) address K ∧
    Certificate (encodingEquiv (path h)) (nativeProgram address K) ∧
    (∀ (entry : Type) (initial : entry → Source) (target : entry → Bool) (c : Control h),
      EncodedSupport (path h) address K entry initial target (encodingEquiv (path h) c) =
        Support address K entry initial target c) ∧
    (∀ c j u n a, FirstHalt (encodedProgram (path h) address K)
      (encodingEquiv (path h) c) j u n a ↔ FirstHalt (nativeProgram address K) c j u n a) ∧
    RankDescent (path h) address K := by
  have cert := certificate (encodingEquiv (path h)) (nativeProgram address K)
  refine ⟨Nat.find_spec (capacity_exists h), ?_, encode_injective _, encode_admissible _, ?_,
    all_rows _ _ _, cert, ?_, ?_, rank_descent _ _ _⟩
  · intro d small
    exact Nat.lt_of_not_ge (Nat.find_min (capacity_exists h) small)
  · rw [← Nat.card_congr (encodingEquiv (path h)), control_card]
  · intro entry initial target c
    ext z
    simp only [EncodedSupport, Support, Set.mem_setOf_eq]
    have prefixes : ∀ e n j log,
        (advance (encodedProgram (path h) address K))^[n]
          (some (encodingEquiv (path h) (start h),0,initial e,[])) =
            some (encodingEquiv (path h) c,j,z.2,log) ↔
        (advance (nativeProgram address K))^[n] (some (start h,0,initial e,[])) =
            some (c,j,z.2,log) := by
      intro e n j log
      exact cert.prefixes (start h,0,initial e,[]) (c,j,z.2,log) n
    simp only [prefixes]
  · intro c j u n a
    simp only [FirstHalt, encodedProgram, cert.remaining]

private theorem native_no_local {h : Nat} (address : Fin h → Address) (K : Nat)
    (c v : Control h) : nativeProgram address K c ≠ .localStep v := by
  cases c with
  | q i a => by_cases hi : i.val < h <;> simp [nativeProgram, hi]
  | b i a b => simp [nativeProgram]
  | c i b => simp [nativeProgram]
  | v a phase => cases phase <;> simp [nativeProgram]

private theorem active_primitive_cost {h : Nat} {address : Fin h → Address} {K : Nat}
    {c : Control h} {j : Nat} {u : Source} {trace : Trace} {a : Bool}
    (run : NativeSerialMachine.Run (nativeProgram address K) c j u trace a) :
    ∀ m : CostModel, cost m trace 0 = trace.length := by
  intro m
  induction run with
  | stop => rfl
  | localStep hop => exact False.elim (native_no_local _ _ _ _ hop)
  | @update c v j u trace a hop suffix ih =>
      change 1 + cost m trace 0 = trace.length + 1
      omega
  | @read c j u p k y trace a hop reply suffix ih =>
      change 1 + cost m trace 0 = trace.length + 1
      omega

/-- The original actual-source parity theorem supplies a native finite trace.
The same trace, source and payload are used by the Fibonacci-word machine. -/
theorem encoded_active_parity_execution (S : Source) (x : Fin S.length → Bool)
    (t K : Nat) (bound : t ≤ 2*K) (admissible : S.length % 2 = 0 ∨ t = 0) :
    ∃ trace, NativeSerialMachine.Run
        (nativeProgram (NativeActiveParityExecution.chartOf S).address K)
        (start S.length) 0
        (substitution^[t] (NativeActiveParityExecution.source (NativeActiveParityExecution.chartOf S) x))
        trace (NativeActiveParityExecution.parity (NativeActiveParityExecution.labels x) S.length) ∧
      NativeSerialMachine.Run
        (encodedProgram (path S.length) (NativeActiveParityExecution.chartOf S).address K)
        (encodingEquiv (path S.length) (start S.length)) 0
        (substitution^[t] (NativeActiveParityExecution.source (NativeActiveParityExecution.chartOf S) x))
        trace (NativeActiveParityExecution.parity (NativeActiveParityExecution.labels x) S.length) ∧
      FirstHalt (nativeProgram (NativeActiveParityExecution.chartOf S).address K)
        (start S.length) 0
        (substitution^[t] (NativeActiveParityExecution.source (NativeActiveParityExecution.chartOf S) x))
        trace.length (NativeActiveParityExecution.parity (NativeActiveParityExecution.labels x) S.length) ∧
      updates trace = 2*(K-(t+NativeActiveParityExecution.bit (x ⟨0,S.length_pos⟩))/2) ∧
      (∀ m : CostModel, cost m trace 0 = trace.length) ∧
      (∃ w J, StateTransition.Reaches
        (nativeStep (encodedProgram (path S.length) (NativeActiveParityExecution.chartOf S).address K))
        (encodingEquiv (path S.length) (start S.length),0,
          substitution^[t] (NativeActiveParityExecution.source (NativeActiveParityExecution.chartOf S) x),[])
        (w,J,substitution^[J] (substitution^[t]
          (NativeActiveParityExecution.source (NativeActiveParityExecution.chartOf S) x)),trace) ∧
        encodedProgram (path S.length) (NativeActiveParityExecution.chartOf S).address K w =
          .stop (NativeActiveParityExecution.parity (NativeActiveParityExecution.labels x) S.length) ∧
        ∀ n p y, Event.read n p y ∈ trace → readout p (substitution^[n] (substitution^[t]
          (NativeActiveParityExecution.source (NativeActiveParityExecution.chartOf S) x))) = y) := by
  let C := NativeActiveParityExecution.chartOf S
  let a := NativeActiveParityExecution.parity (NativeActiveParityExecution.labels x) S.length
  let J := 2*(K-(t+NativeActiveParityExecution.bit (x ⟨0,S.length_pos⟩))/2)
  have symbolic := (NativeActiveParityExecution.native_active_parity_execution
    S x t K bound admissible a J).mpr ⟨rfl,rfl,by simp [NativeActiveParityExecution.output, endpoint, a]⟩
  have actual := guarded_native (a := a) C K (substitution^[t] (NativeActiveParityExecution.source C x)) symbolic (by simp [nativeProgram, endpoint])
  obtain ⟨trace, run, epoch⟩ := actual
  have encoded := (certificate (encodingEquiv (path S.length))
    (nativeProgram C.address K)).runs (start S.length) 0 _ trace a |>.mpr run
  refine ⟨trace, run, encoded, first_of_run _ run, by simpa using epoch,
    active_primitive_cost run, ?_⟩
  obtain ⟨w,J,_,reaches,halt,truth⟩ := NativeSerialMachine.actual_register_execution
    _ encoded (substitution^[t] (NativeActiveParityExecution.source C x)) rfl []
  exact ⟨w,J,by simpa only [encodedProgram,C,List.nil_append,Function.iterate_zero_apply] using reaches,halt,truth⟩

#print axioms native_fibonacci_active_table
#print axioms encoded_active_parity_execution

end D5.S3.Arith.FibonacciAtomic.Observer.NativeFibonacciActiveTable
