/- GID: D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OriginalExecutionBridge
   generality: I
   mirror-B: D5/B/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OriginalExecutionBridge
   mirror-E: none(waiver:symbolic-proof-no-numeric-artifact)
   anchors: []
   utility: none
   digest: The original scanner and selector preserve the joint native record and exact fee. -/

import D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.NarrowWindowCost
import D5.S3.ObserverMemory.Algorithms.KBonacciIrreversibleAcquisition

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe z

namespace D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OriginalExecutionBridge

open D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition
open D5.S0.Tower.DBonacci.Names
open D5.S0.Tower.DBonacciGeneral.UniformBaseGap
open D5.S0.Automata.TypedPartialDFAOOverBase
open LiteralModel EndpointCells
open D5.S3.ObserverMemory.Algorithms.KBonacciIrreversibleAcquisition
open D5.S3.ObserverMemory.Prediction.ControlledBehaviorUniversality
open scoped BigOperators

local notation "scannedRecord" =>
  (fun (k : ℕ) (hk : 0 < k) (w : List Bool) =>
    Option.map
      (fun tail => LiveRecord.mk (NarrowWindowCost.value k 0 w)
        (List.length w : ZMod (k + 1)) (Fin.val tail))
      (PartialDFA.eval (NarrowWindowCost.scanner k hk) w))

/-- The original selector recursion on the native record, with its own archive and exact fee. -/
def NativeExecute {Y : Type z} {k m : ℕ} (π : NarrowWindowCost.Selector m Y)
    (d : ℕ) : Option (LiveRecord k) → Option (ZMod 2) →
      NarrowWindowCost.Archive m → Option (Y × ℕ) :=
  Nat.rec
    (fun _ y₀ archive => match π y₀ archive with
      | .inl y => some (y,0)
      | .inr _ => none)
    (fun _ next q y₀ archive => match π y₀ archive with
      | .inl y => some (y,0)
      | .inr B =>
        let q' := runBits k B q
        (next q' y₀ (archive++[(B,endpointReading q')])).map
          (fun r => (r.1,r.2+1))) d

private theorem weight_coefficient :
    ∀ (k : ℕ), 2 ≤ k → ∀ n : ℕ,
      originalWeight k n = coefficient k (n : ZMod (k+1)) := by
  intro k hk
  let W := originalWeight k
  have recurrence (n : ℕ) : W (n+k) = ∑ i ∈ Finset.range k, W (n+i) := by
    have h := congrArg (fun a : ℕ => (a : ZMod 2))
      (dbonacci_add_two_of_le k (n+k) (by omega))
    have hfin : W (n+k) = ∑ i : Fin k, W (n+i.val) := by
      simpa only [Nat.add_sub_cancel,Nat.cast_sum,W,originalWeight] using h
    rw [Finset.sum_fin_eq_sum_range] at hfin
    calc
      _ = _ := hfin
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i hi
        simp only [Finset.mem_range.mp hi,dif_pos,Fin.val_mk]
  have period : Function.Periodic W (k+1) := by
    intro n
    have window : (∑ i ∈ Finset.range k, W (n+1+i)) + W n =
        (∑ i ∈ Finset.range k, W (n+i)) + W (n+k) := by
      have left := Finset.sum_range_succ' (fun i => W (n+i)) k
      have right := Finset.sum_range_succ (fun i => W (n+i)) k
      simpa only [Nat.add_zero, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
        using left.symm.trans right
    rw [← recurrence (n+1), ← recurrence n] at window
    have hzero : W (n+k) + W (n+k) = 0 := CharTwo.add_self_eq_zero _
    rw [hzero] at window
    have same := CharTwo.add_eq_zero.mp window
    simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using same
  intro n
  let r := n % (k+1)
  have hr : r < k+1 := Nat.mod_lt n (by omega)
  have seed : W r = if r=0 ∨ r=k then 1 else 0 := by
    by_cases last : r=k
    · rw [if_pos (Or.inr last),last]
      change (dbonacci k (k+2) : ZMod 2)=1
      rw [dbonacci_diagonal_cardinality]
      rw [Nat.cast_sub (Nat.one_le_pow k 2 (by omega))]
      simp [Nat.cast_pow, CharTwo.two_eq_zero, show k ≠ 0 by omega]
    · change (dbonacci k (r+2) : ZMod 2) = _
      rw [dbonacci_add_two_of_lt k r (by omega)]
      by_cases zero : r=0
      · simp [zero]
      · simp [zero,last,Nat.cast_pow,CharTwo.two_eq_zero]
  have hz : (n : ZMod (k+1))=0 ↔ r=0 := by
    rw [← Nat.cast_zero,ZMod.natCast_eq_natCast_iff']
    simp only [Nat.zero_mod,r]
  have ht : (n : ZMod (k+1)) = -1 ↔ r=k := by
    constructor
    · intro h
      simpa only [ZMod.val_natCast,ZMod.val_neg_one,r] using congrArg ZMod.val h
    · intro h
      apply ZMod.val_injective (k+1)
      simpa only [ZMod.val_natCast,ZMod.val_neg_one,r] using h
  change W n = _
  rw [← period.map_mod_nat n,seed]
  simp only [coefficient,hz,ht]

private theorem run_append : ∀ (k : ℕ) (a b : List Bool) (q : Option (LiveRecord k)),
    runWord (bitUpdate k) (a++b) q =
      runWord (bitUpdate k) b (runWord (bitUpdate k) a q) := by
  intro k a
  induction a with
  | nil => intros; rfl
  | cons bit a ih =>
      intro b q
      simpa only [List.cons_append,runWord] using ih b (bitUpdate k bit q)

private theorem run_absorbed : ∀ (k : ℕ) (w : List Bool),
    runWord (bitUpdate k) w none = none := by
  intro k w
  induction w with
  | nil => rfl
  | cons bit w ih => simpa only [runWord,bitUpdate] using ih

private theorem scanner_value_joint :
    ∀ (k : ℕ) (hk : 2 ≤ k) (w : List Bool) (n : ℕ) (a : ZMod 2) (s : Fin k),
      runWord (bitUpdate k) w (some ⟨a,(n : ZMod (k+1)),s.val⟩) =
        ((D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.NarrowWindowCost.scanner k (by omega)).evalFrom s w).map
          (fun tail => ⟨a+D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.NarrowWindowCost.value k n w,((n+w.length : ℕ) : ZMod (k+1)),tail.val⟩) := by
  intro k hk w
  induction w with
  | nil => intro n a s; simp [runWord,PartialDFA.evalFrom,runTransition,D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.NarrowWindowCost.value]
  | cons bit w ih =>
      intro n a s
      cases bit with
      | false =>
          have h := ih (n+1) a ⟨0,by omega⟩
          simpa only [runWord,bitUpdate,Bool.false_eq_true,if_false,
            PartialDFA.evalFrom,runTransition,D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.NarrowWindowCost.scanner,D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.NarrowWindowCost.value,List.length_cons,
            Nat.cast_add,Nat.cast_one,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm,
            zero_add,add_zero] using h
      | true =>
          by_cases safe : s.val+1<k
          · have h := ih (n+1) (a+coefficient k (n : ZMod (k+1))) ⟨s.val+1,safe⟩
            simpa only [runWord,bitUpdate,if_true,safe,if_pos,dite_true,
              PartialDFA.evalFrom,runTransition,D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.NarrowWindowCost.scanner,D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.NarrowWindowCost.value,List.length_cons,
              Nat.cast_add,Nat.cast_one,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm,
              ← weight_coefficient k hk n,originalWeight,add_assoc] using h
          · simp only [runWord,bitUpdate,if_true,safe,if_false,dite_false,run_absorbed,
              PartialDFA.evalFrom,runTransition,D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.NarrowWindowCost.scanner,dif_neg safe,Option.map_none]

private theorem record_run : ∀ (k : ℕ) (hk : 2 ≤ k) (w : List Bool),
    scannedRecord k (by omega) w =
      runWord (bitUpdate k) w (some ⟨0,0,0⟩) := by
  intro k hk w
  have h := scanner_value_joint k hk w 0 0 ⟨0,by omega⟩
  simpa only [PartialDFA.eval,D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.NarrowWindowCost.scanner,Nat.cast_zero,
    Nat.zero_add,zero_add] using h.symm

theorem record_append : ∀ (k : ℕ) (hk : 2 ≤ k) (w b : List Bool),
    scannedRecord k (by omega) (w++b) =
      runWord (bitUpdate k) b (scannedRecord k (by omega) w) := by
  intro k hk w b
  rw [record_run k hk,run_append,record_run k hk]


theorem output_record : ∀ (k : ℕ) (hk : 0<k) (w : List Bool),
    D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.NarrowWindowCost.output k hk w = endpointReading (scannedRecord k hk w) := by
  intro k hk w
  unfold D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.NarrowWindowCost.output
  dsimp only
  cases (D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.NarrowWindowCost.scanner k hk).eval w <;> rfl

theorem execute_same : ∀ {Y : Type z} (k m : ℕ) (hk : 2 ≤ k)
    (π : D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.NarrowWindowCost.Selector m Y) (d : ℕ) (w : List Bool) (y₀ : Option (ZMod 2)) (archive : D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.NarrowWindowCost.Archive m),
    D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.NarrowWindowCost.execute k (by omega) π d w y₀ archive =
      NativeExecute π d (scannedRecord k (by omega) w) y₀ archive := by
  intro Y k m hk π d
  induction d with
  | zero => intros; rfl
  | succ d ih =>
      intro w y₀ archive
      cases selected : π y₀ archive with
      | inl label => simp only [D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.NarrowWindowCost.execute,NativeExecute,selected]
      | inr B =>
          simp only [D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.NarrowWindowCost.execute,NativeExecute,selected]
          rw [ih,output_record,record_append k hk]
          rfl

private theorem history_flatten : ∀ (k m : ℕ) (localAlphabet : Bool)
    (history : List (AllowedBlock k m localAlphabet)) (q : Option (LiveRecord k)),
    historyRecordFrom history q =
      runWord (bitUpdate k) (history.flatMap (fun action => List.ofFn action.val)) q := by
  intro k m localAlphabet history
  induction history with
  | nil => intros; rfl
  | cons action history ih =>
      intro q
      simpa only [historyRecordFrom,List.foldl_cons,List.flatMap_cons,run_append,runBits]
        using ih (runBits k action.val q)

theorem record_history : ∀ (k m : ℕ) (hk : 2 ≤ k) (localAlphabet : Bool)
    (history : List (AllowedBlock k m localAlphabet)),
    scannedRecord k (by omega) (history.flatMap (fun action => List.ofFn action.val)) =
      historyRecord history := by
  intro k m hk localAlphabet history
  rw [record_run k hk,historyRecord,history_flatten]


#print axioms NativeExecute
#print axioms record_append
#print axioms output_record
#print axioms execute_same
#print axioms record_history

end D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OriginalExecutionBridge
