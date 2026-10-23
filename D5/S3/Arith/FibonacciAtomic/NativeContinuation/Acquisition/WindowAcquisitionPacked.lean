/- GID: D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/WindowAcquisitionPacked
   generality: I
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/WindowAcquisitionPacked
   mirror-E: none(waiver:unbounded-operational-correspondence)
   anchors: [mathlib/module/Mathlib.Data.Nat.Fib.Zeckendorf]
   utility: none
   digest: The original positive numeral is acquired by one accepting packed execution. -/

import D5.S3.Arith.FibonacciAtomic.NativeContinuation.Acquisition.WindowAcquisitionTerminal

namespace PhysicalWindowContinuation
namespace Original
open D5.S3.Arith.FibonacciAtomic

def numeral (w : List Window) (e : Bool) : ℕ :=
  (D5.S1.Digit.GoldenBase4IntervalMachine.fibPair
    (NativeContinuation.JointLaw.digits (w.map letter) ++ [if e then 1 else 0])).1

def finalColumns (w : List Window) (e : Bool) : List Bits :=
  Terminal.finished (if e then 1 else 0) (columnsAfter [zeros] w)

theorem final_values (w : List Window) (e : Bool) :
    pair (finalColumns w e) = NativeContinuation.JointLaw.composition (w.map letter) ∧
    valueCount (finalColumns w e) = w.length ∧
    valueN (finalColumns w e) = numeral w e := by
  obtain ⟨h1,h2,hc,hn⟩ := Terminal.finished_values (if e then 1 else 0) (columnsAfter [zeros] w)
  have hpair := original_composition w
  have hcount := columnsAfter_count [zeros] w
  have hnum := physical_numeral_correspondence w e
  have he : (if e then (1 : Fin 5) else 0).val = e.toNat := by cases e <;> rfl
  refine ⟨?_,?_,?_⟩
  · simpa only [finalColumns,pair,h1,h2] using hpair
  · simpa [finalColumns,valueCount,bitValue,zeros] using hc.trans hcount
  · rw [he] at hn
    exact hn.trans hnum.symm



end Original

namespace Original

def maximumColumn (w : List Window) : ℕ :=
  max (value1 (columnsAfter [zeros] w)) (value2 (columnsAfter [zeros] w))

theorem columnsAfter_append (bs : List Bits) (w : List Window) (b : Window) :
    columnsAfter bs (w ++ [b]) = updated (windowCarry b) (columnsAfter bs w) := by
  simp [columnsAfter,List.foldl_append]

theorem maximum_step (w : List Window) (b : Window) :
    maximumColumn (w ++ [b]) ≤ 5*maximumColumn w+2 := by
  obtain ⟨h1,h2,_⟩ := updated_values (windowCarry b) (columnsAfter [zeros] w)
  have hleft := le_max_left (value1 (columnsAfter [zeros] w)) (value2 (columnsAfter [zeros] w))
  have hright := le_max_right (value1 (columnsAfter [zeros] w)) (value2 (columnsAfter [zeros] w))
  have hd : (windowCarry b).first.val ≤ 2 ∧ (windowCarry b).second.val ≤ 1 := by
    cases b <;> decide
  simp only [maximumColumn,columnsAfter_append]
  rw [max_le_iff,h1,h2]
  exact ⟨by omega,by omega⟩

theorem maximum_growth (w : List Window) :
    maximumColumn [] = 0 ∧
    2*maximumColumn w+1 ≤ 5^w.length ∧
    maximumColumn w ≤ (5^w.length-1)/2 := by
  have hzero : maximumColumn [] = 0 := by
    simp [maximumColumn,columnsAfter,value1,value2,bitValue,zeros]
  have hg : 2*maximumColumn w+1 ≤ 5^w.length := by
    induction w using List.reverseRecOn with
    | nil => simp [hzero]
    | append_singleton w b ih =>
      have hs := maximum_step w b
      simp only [List.length_append,List.length_singleton,pow_succ]
      omega
  exact ⟨hzero,hg,by omega⟩


end Original

namespace Original
open D5.S3.Arith.FibonacciAtomic
open D5.S0.Automata.BinaryZeckendorfLanguage
open D5.S1.Digit.ZeckendorfRawWindow

theorem original_capacity (w : List Window) (e : Bool)
    (hg : D5.S3.Arith.ZeckendorfFutureKernel.legal false
      (NativeContinuation.NullReplyFiber.highBits (w.map letter) ++ [e])) :
    numeral w e < Nat.fib (3*w.length+3) := by
  let ds := NativeContinuation.JointLaw.digits (w.map letter) ++ [if e then 1 else 0]
  have chain : ∀ (bs : List Bool) (s : Bool),
      D5.S3.Arith.ZeckendorfFutureKernel.legal s bs →
      ((if s then 1 else 0 : Fin 2) :: bs.map (fun b => if b then 1 else 0)).IsChain
        (fun a b => a = 0 ∨ b = 0) := by
    intro bs
    induction bs with
    | nil => simp
    | cons b bs ih =>
      intro s hs
      cases s <;> cases b <;>
        simp_all [D5.S3.Arith.ZeckendorfFutureKernel.legal,List.isChain_cons_cons]
  have hd : NoAdjacentOnes ds := by
    have hc := (chain _ false hg).tail
    simpa [NoAdjacentOnes,ds,NativeContinuation.JointLaw.digits,List.map_append] using hc
  have hl : ds.length = 3*w.length+1 := by
    have hb : (NativeContinuation.NullReplyFiber.highBits (w.map letter)).length = 3*w.length := by
      clear hg hd ds
      induction w with
      | nil => simp [NativeContinuation.NullReplyFiber.highBits]
      | cons b w ih =>
        cases b <;> simp [NativeContinuation.NullReplyFiber.highBits,List.flatMap_cons,
          letter,LiteralWindowEnd.bits] at ih ⊢ <;> omega
    simp only [ds,NativeContinuation.JointLaw.digits,List.length_append,
      List.length_map,List.length_singleton,hb]
  obtain ⟨hc,hb,hv,_⟩ := source_word_coordinates ds hd
  have hlt : ((support ds).map Nat.fib).sum < Nat.fib (3*w.length+3) := by
    apply hc.sum_fib_lt
    intro k hk
    rcases List.mem_append.mp (List.mem_of_mem_head? hk) with hk | hk
    · have hh := hb k hk
      omega
    · simp only [List.mem_singleton] at hk
      omega
  simpa only [hv,numeral,ds] using hlt

end Original

namespace Original

def matrix : (ℕ × ℕ) →+ (ℕ × ℕ) where
  toFun c := (c.1+2*c.2,2*c.1+3*c.2)
  map_zero' := by rfl
  map_add' := by
    intro a b
    ext <;> simp <;> omega

def digitColumn (b : Window) : ℕ × ℕ :=
  ((displacement b).1.val,(displacement b).2.val)

def columnSum (w : List Window) : ℕ × ℕ :=
  (w.reverse.mapIdx (fun j b => (matrix : (ℕ × ℕ) → (ℕ × ℕ))^[j] (digitColumn b))).sum

theorem columnSum_append (w : List Window) (b : Window) :
    columnSum (w ++ [b]) = matrix (columnSum w) + digitColumn b := by
  have he :
      (w.reverse.mapIdx (fun j b => (matrix : (ℕ × ℕ) → (ℕ × ℕ))^[j+1] (digitColumn b))) =
      (w.reverse.mapIdx (fun j b => (matrix : (ℕ × ℕ) → (ℕ × ℕ))^[j] (digitColumn b))).map matrix := by
    apply List.ext_getElem
    · simp
    · intro j h1 h2
      simp [Function.iterate_succ_apply']
  simp only [columnSum,List.reverse_append,List.reverse_singleton,List.singleton_append,
    List.mapIdx_cons,Function.iterate_zero_apply,List.sum_cons]
  rw [he,← map_list_sum]
  exact add_comm _ _

theorem physical_column_sum (w : List Window) :
    pair (columnsAfter [zeros] w) = columnSum w := by
  induction w using List.reverseRecOn with
  | nil => simp [pair,columnsAfter,value1,value2,bitValue,zeros,columnSum]
  | append_singleton w b ih =>
    obtain ⟨h1,h2,_⟩ := updated_values (windowCarry b) (columnsAfter [zeros] w)
    rw [columnsAfter_append,columnSum_append,← ih]
    apply Prod.ext
    · simpa only [pair,matrix,AddMonoidHom.coe_mk,ZeroHom.coe_mk,Prod.fst_add,
        digitColumn,windowCarry] using h1
    · simpa only [pair,matrix,AddMonoidHom.coe_mk,ZeroHom.coe_mk,Prod.snd_add,
        digitColumn,windowCarry] using h2

end Original

namespace Original
open D5.S3.Arith.FibonacciAtomic

theorem original_accepting_packed_resources :
    Function.Injective (finiteCode (α := Symbol)) ∧
    ∃ A B : ℕ, 0 < A ∧ 0 < B ∧
    ∀ (w : List Window) (e : Bool),
      D5.S3.Arith.ZeckendorfFutureKernel.legal false
        (NativeContinuation.NullReplyFiber.highBits (w.map letter) ++ [e]) →
      0 < numeral w e →
    ∃ T : ℕ, T ≤ A*(w.length+1)^2 ∧
      run (initial w e) T = boundary (inputSource w e) w.length (finalColumns w e) 0 .done ∧
      program (run (initial w e) T).control = .halt ∧
      pair (finalColumns w e) = NativeContinuation.JointLaw.composition (w.map letter) ∧
      valueCount (finalColumns w e) = w.length ∧
      valueN (finalColumns w e) = numeral w e ∧
      pair (finalColumns w e) = columnSum w ∧
      maximumColumn [] = 0 ∧
      (∀ b, maximumColumn (w ++ [b]) ≤ 5*maximumColumn w+2) ∧
      2*maximumColumn w+1 ≤ 5^w.length ∧
      maximumColumn w ≤ (5^w.length-1)/2 ∧
      valueN (finalColumns w e) < Nat.fib (3*w.length+3) ∧
      (finalColumns w e).length ≤ 3*w.length+4 ∧
      (∀ n ≤ T, chargedBits w e n ≤ B*(w.length+1)) ∧
      (∀ n ≤ T, Frame (inputSource w e) w.length (3*w.length+5)
        (run (initial w e) n)) := by
  refine ⟨finiteCode_injective,80,programCode.length+Fintype.card Control+64*(Fintype.card Symbol+1),
    by omega,by omega,?_⟩
  intro w e hg hpos
  obtain ⟨t,ht,he,hpair,hcount,hlen,hf⟩ := source_unit_entry w e hg
  obtain ⟨u,hu,hend,hout,hs⟩ := Terminal.scan_return (inputSource w e) w.length
    (columnsAfter [zeros] w) (if e then 1 else 0) false
  obtain ⟨vp,vc,vn⟩ := final_values w e
  have hp : Terminal.hasN (finalColumns w e) = true :=
    (Terminal.hasN_iff_pos _).mpr (by rw [vn]; exact hpos)
  have hend' : run (boundary (inputSource w e) w.length (columnsAfter [zeros] w) 1
      (.finishScan (if e then 1 else 0) false)) u =
      boundary (inputSource w e) w.length (finalColumns w e) 0 .done := by
    have hp' : Terminal.hasN (Terminal.finished (if e then 1 else 0) (columnsAfter [zeros] w)) = true := hp
    simpa only [finalColumns,Bool.false_or,hp',↓reduceIte] using hend
  have hall : ∀ n ≤ u+t, Frame (inputSource w e) w.length (3*w.length+5)
      (run (initial w e) n) := by
    apply frame_join (inputSource w e) w.length (3*w.length+5) t u _ _ he hf
    intro n hn
    exact safe_frame (inputSource w e) w.length ((columnsAfter [zeros] w).length+3)
      w.length (3*w.length+5) _ (by omega) (by omega) (by omega) (hs n hn)
  have hrun : run (initial w e) (u+t) =
      boundary (inputSource w e) w.length (finalColumns w e) 0 .done := by
    rw [run,Function.iterate_add_apply]
    change run (run _ t) u = _
    rw [he]
    exact hend'
  obtain ⟨mz,mp,mg⟩ := maximum_growth w
  have vsum : pair (finalColumns w e) = columnSum w :=
    vp.trans ((original_composition w).symm.trans (physical_column_sum w))
  exact ⟨u+t,by nlinarith,hrun,by rw [hrun]; rfl,vp,vc,vn,vsum,mz,
    maximum_step w,mp,mg,by rw [vn]; exact original_capacity w e hg,
    by dsimp [finalColumns]; omega,prefix_charged_bound w e (u+t) hall,hall⟩


end Original

end PhysicalWindowContinuation
