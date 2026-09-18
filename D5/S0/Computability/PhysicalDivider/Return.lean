/- GID: D5/S0/Computability/PhysicalDivider/Return
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Executed copy-out, scratch erasure, fourteen-head parking and reusable return. -/

import D5.S0.Computability.PhysicalDivider.Preparation
import D5.S0.Computability.PhysicalDivider.Parking
import Mathlib.Tactic.Ring
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace D5.S0.Computability.PhysicalDivider
open Turing Lax51Proofs.RamToTM

/-- The terminal call boundary has exactly the same layout as the entry buffers. -/
def callReturned (a d capacity q r : List Bool) : PhysicalCfg :=
  ⟨.returned, entryTapes a d capacity q r⟩

set_option maxHeartbeats 2400000 in
/-- Copy-out and erasure reach the machine's own return state. Re-entry preserves
all tape and head data and executes the paid boundary read. -/
theorem return_execution (a d capacity divisor quotient remainder : List Bool) :
    ((fun o : Option LocatedCfg => o.bind locatedStep)^[
      37 * (quotient.length + remainder.length) + 10 * divisor.length +
        3 * (a.length + d.length + capacity.length) + 45])
      (some (locatedSourceCfg (divDoneCfg true divisor remainder quotient)
        (preparedFrame a d capacity) (preparedHeads a d capacity))) =
      some (callReturned a d capacity quotient remainder, fun _ => 0) ∧
    callAgain (callReturned a d capacity quotient remainder) =
      some (callEntry a d capacity quotient remainder) := by
  let run := fun o : Option LocatedCfg => o.bind locatedStep
  have chain {i j : ℕ} {a b c : LocatedCfg}
      (h₁ : (run^[i]) (some a) = some b) (h₂ : (run^[j]) (some b) = some c) :
      (run^[j + i]) (some a) = some c := by rw [Function.iterate_add_apply, h₁, h₂]
  have topWithin (bs : List Bool) : Within (stackAtTop bs) (topExtent bs) := by
    have lengthBelow (bs : List Bool) : (cellsBelow bs).length = 2 * bs.length + 2 := by
      induction bs with
      | nil => rfl
      | cons b bs ih => simp [cellsBelow, ih]; omega
    have getBound (bs : List Bool) (i : ℕ) (h : bs.getI i = true) : i < bs.length := by
      by_contra hn
      rw [List.getI_eq_default _ (by omega)] at h
      cases h
    cases bs with
    | nil =>
      refine ⟨by simp [topExtent], by simp [topExtent], ?_⟩
      intro i hi
      cases i with
      | ofNat n =>
        change (Tape.mk₂ [] [false, true]).nth (n : ℤ) = true at hi
        rw [Tape.mk₂, Tape.mk'_nth_nat, ListBlank.nth_mk] at hi
        have hn := getBound [false, true] n hi
        simp only [List.length_cons, List.length_nil] at hn
        dsimp [topExtent]; constructor <;> omega
      | negSucc n =>
        change ([] : List Bool).getI n = true at hi
        have hn := getBound [] n hi
        simp at hn
    | cons b bs =>
      refine ⟨by simp [topExtent]; omega, by simp [topExtent], ?_⟩
      intro i hi
      cases i with
      | ofNat n =>
        change (Tape.mk₂ (cellsBelow bs) [true, b]).nth (n : ℤ) = true at hi
        rw [Tape.mk₂, Tape.mk'_nth_nat, ListBlank.nth_mk] at hi
        have hn := getBound [true, b] n hi
        simp only [List.length_cons, List.length_nil] at hn
        dsimp [topExtent]; try simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
        constructor <;> omega
      | negSucc n =>
        change (cellsBelow bs).getI n = true at hi
        have hn := getBound (cellsBelow bs) n hi
        rw [lengthBelow] at hn
        dsimp [topExtent]; try simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
        constructor <;> omega
  have park (label next : FrameLabel) (k : ActiveTape)
      (tapes : ActiveTape → Tape Bool) (heads : ActiveTape → ℤ) (bs : List Bool)
      (htape : tapes k = stackAtTop bs) (hhead : heads k = 2 * bs.length)
      (hcode : frameInstruction label none = startBlock k .parkMarker (.frame next none false)) :
      (run^[3 * bs.length + 2]) (some ((⟨.frame label none, tapes⟩ : PhysicalCfg), heads)) =
        some ((⟨.frame next none, Function.update tapes k (stackAtOrigin bs)⟩ : PhysicalCfg),
          Function.update heads k 0) := by
    let cont := Continuation.frame next none false
    let embed := fun c : BlockCfg × Extent =>
      (liftBlockCfg k cont tapes c.1, Function.update heads k c.2.head)
    have lift (n : ℕ) (c c' : BlockCfg × Extent)
        (h : ((fun o : Option (BlockCfg × Extent) => o.bind accountedBlockStep)^[n])
          (some c) = some c') : (run^[n]) (some (embed c)) = some (embed c') := by
      have one (c c' : BlockCfg × Extent) (hs : accountedBlockStep c = some c') :
          locatedStep (embed c) = some (embed c') := by
        rcases c with ⟨⟨pc, tape⟩, e⟩
        cases pc <;>
          simp only [accountedBlockStep, blockStep, blockAction] at hs <;>
          cases hs <;>
          simp [embed, liftBlockCfg, locatedStep, instruction, blockAction, liftBlockAction,
            executeInstruction, advanceHeads, accountAction, Function.update_idem]
      induction n generalizing c' with
      | zero =>
        simp only [Function.iterate_zero_apply, Option.some.injEq] at h
        subst c'; rfl
      | succ n ih =>
        rw [Function.iterate_succ_apply'] at h ⊢
        cases he : ((fun o : Option (BlockCfg × Extent) => o.bind accountedBlockStep)^[n])
            (some c) with
        | none => simp [he] at h
        | some mid => rw [he] at h; rw [ih mid he]; exact one mid c' h
    have htop : stackWithAbove bs [] = stackAtTop bs := by cases bs <;> rfl
    have hw : Within (stackWithAbove bs []) ⟨2 * (bs.length : ℤ), 0, 2 * bs.length + 1⟩ := by
      rw [htop]; exact topWithin bs
    have hp := (park_preserves_extent k cont tapes bs [] (2 * bs.length + 1) (by omega) hw).1
    have hlift := lift (3 * bs.length + 1) _ _ hp
    have hup : Function.update tapes k (stackAtTop bs) = tapes := by
      rw [← htape]; exact Function.update_eq_self _ _
    have hhu : Function.update heads k (2 * bs.length) = heads := by
      rw [← hhead]; exact Function.update_eq_self _ _
    simp only [embed, liftBlockCfg, htop, hup, hhu] at hlift
    have heq : locatedStep ((⟨.frame label none, tapes⟩ : PhysicalCfg), heads) =
        locatedStep ((⟨.block k .parkMarker cont, tapes⟩ : PhysicalCfg), heads) := by
      simp [locatedStep, instruction, hcode, startBlock, blockAction, cont]
    -- The first counted action is identical at the frame and block entry controls.
    have hstart : (run^[3 * bs.length + 2])
        (some ((⟨.frame label none, tapes⟩ : PhysicalCfg), heads)) =
        (run^[3 * bs.length + 2])
          (some ((⟨.block k .parkMarker cont, tapes⟩ : PhysicalCfg), heads)) := by
      rw [show 3 * bs.length + 2 = (3 * bs.length + 1) + 1 by omega,
        Function.iterate_succ_apply]
      change (run^[3 * bs.length + 1]) (locatedStep _) =
        (run^[3 * bs.length + 1]) (locatedStep _)
      rw [heq]
    rw [hstart]
    rw [show 3 * bs.length + 2 = (3 * bs.length + 1) + 1 by omega,
      Function.iterate_succ_apply', hlift]
    simp [run, locatedStep, instruction, controlRead, executeInstruction, advanceHeads,
      continueBlock, cont, stackAtOrigin, List.append_nil]
  let initial : ActiveTape → List Bool := fun k => match k with
    | .inl j => (divDoneCfg true divisor remainder quotient).stk j
    | .inr j => boundaryWords a d capacity [] [] (.inr j)
  have hstart : (run^[1]) (some (locatedSourceCfg
      (divDoneCfg true divisor remainder quotient)
      (preparedFrame a d capacity) (preparedHeads a d capacity))) =
      some (topFrameCfg .copyQ none initial) := by
    simp only [run, Function.iterate_one, Option.bind_some, locatedStep,
      locatedSourceCfg, sourceCfg, divDoneCfg, divCfg, instruction, controlRead,
      Option.map_some, executeInstruction, advanceHeads, topFrameCfg, Option.some.injEq,
      Prod.mk.injEq, PhysicalCfg.mk.injEq, and_true, true_and]
    constructor <;> funext k <;> cases k <;> rfl
  have h1 := frame_loop_execution .copyQ none initial
  let words1 := FrameLoop.result .copyQ initial
  have h2 := frame_loop_execution .emitQ none words1
  let words2 := FrameLoop.result .emitQ words1
  have h3 := frame_loop_execution .copyR none words2
  let words3 := FrameLoop.result .copyR words2
  have h4 := frame_loop_execution .emitR none words3
  let words4 := FrameLoop.result .emitR words3
  have h5 := frame_loop_execution .clearDivisor none words4
  let words5 := FrameLoop.result .clearDivisor words4
  have hclean := (chain (chain (chain (chain (chain hstart h1) h2) h3) h4) h5)
  have hw : words5 = boundaryWords a d capacity quotient remainder := by
    funext k
    cases k <;> rename_i k <;> cases k <;>
      simp [initial, words1, words2, words3, words4, words5, FrameLoop.result, FrameLoop.outputs, FrameLoop.source,
        boundaryWords, divMachine, divDoneCfg, divCfg, divStacks]
  change _ = some (topFrameCfg .parkDividend none words5) at hclean
  rw [hw] at hclean
  let tapes₀ : ActiveTape → Tape Bool := fun k =>
    stackAtTop (boundaryWords a d capacity quotient remainder k)
  let heads₀ : ActiveTape → ℤ := fun k =>
    2 * (boundaryWords a d capacity quotient remainder k).length
  have park1 := park .parkDividend .parkDivisor (.inl .dividend) tapes₀ heads₀ []
    (by simp [tapes₀, heads₀, boundaryWords]) (by simp [tapes₀, heads₀, boundaryWords]) rfl
  let tapes1 := Function.update tapes₀ (.inl .dividend) (stackAtOrigin [])
  let heads1 := Function.update heads₀ (.inl .dividend) 0
  have park2 := park .parkDivisor .parkRemainder (.inl .divisor) tapes1 heads1 []
    (by simp [tapes₀, heads₀, boundaryWords, tapes1, heads1]) (by simp [tapes₀, heads₀, boundaryWords, tapes1, heads1]) rfl
  let tapes2 := Function.update tapes1 (.inl .divisor) (stackAtOrigin [])
  let heads2 := Function.update heads1 (.inl .divisor) 0
  have park3 := park .parkRemainder .parkQuotient (.inl .remainder) tapes2 heads2 []
    (by simp [tapes₀, heads₀, boundaryWords, tapes1, heads1, tapes2, heads2]) (by simp [tapes₀, heads₀, boundaryWords, tapes1, heads1, tapes2, heads2]) rfl
  let tapes3 := Function.update tapes2 (.inl .remainder) (stackAtOrigin [])
  let heads3 := Function.update heads2 (.inl .remainder) 0
  have park4 := park .parkQuotient .parkDivisorBackup (.inl .quotient) tapes3 heads3 []
    (by simp [tapes₀, heads₀, boundaryWords, tapes1, heads1, tapes2, heads2, tapes3, heads3]) (by simp [tapes₀, heads₀, boundaryWords, tapes1, heads1, tapes2, heads2, tapes3, heads3]) rfl
  let tapes4 := Function.update tapes3 (.inl .quotient) (stackAtOrigin [])
  let heads4 := Function.update heads3 (.inl .quotient) 0
  have park5 := park .parkDivisorBackup .parkRemainderBackup (.inl .divisorBackup) tapes4 heads4 []
    (by simp [tapes₀, heads₀, boundaryWords, tapes1, heads1, tapes2, heads2, tapes3, heads3, tapes4, heads4]) (by simp [tapes₀, heads₀, boundaryWords, tapes1, heads1, tapes2, heads2, tapes3, heads3, tapes4, heads4]) rfl
  let tapes5 := Function.update tapes4 (.inl .divisorBackup) (stackAtOrigin [])
  let heads5 := Function.update heads4 (.inl .divisorBackup) 0
  have park6 := park .parkRemainderBackup .parkDifference (.inl .remainderBackup) tapes5 heads5 []
    (by simp [tapes₀, heads₀, boundaryWords, tapes1, heads1, tapes2, heads2, tapes3, heads3, tapes4, heads4, tapes5, heads5]) (by simp [tapes₀, heads₀, boundaryWords, tapes1, heads1, tapes2, heads2, tapes3, heads3, tapes4, heads4, tapes5, heads5]) rfl
  let tapes6 := Function.update tapes5 (.inl .remainderBackup) (stackAtOrigin [])
  let heads6 := Function.update heads5 (.inl .remainderBackup) 0
  have park7 := park .parkDifference .parkShift (.inl .differenceReverse) tapes6 heads6 []
    (by simp [tapes₀, heads₀, boundaryWords, tapes1, heads1, tapes2, heads2, tapes3, heads3, tapes4, heads4, tapes5, heads5, tapes6, heads6]) (by simp [tapes₀, heads₀, boundaryWords, tapes1, heads1, tapes2, heads2, tapes3, heads3, tapes4, heads4, tapes5, heads5, tapes6, heads6]) rfl
  let tapes7 := Function.update tapes6 (.inl .differenceReverse) (stackAtOrigin [])
  let heads7 := Function.update heads6 (.inl .differenceReverse) 0
  have park8 := park .parkShift .parkA (.inl .shiftTemp) tapes7 heads7 []
    (by simp [tapes₀, heads₀, boundaryWords, tapes1, heads1, tapes2, heads2, tapes3, heads3, tapes4, heads4, tapes5, heads5, tapes6, heads6, tapes7, heads7]) (by simp [tapes₀, heads₀, boundaryWords, tapes1, heads1, tapes2, heads2, tapes3, heads3, tapes4, heads4, tapes5, heads5, tapes6, heads6, tapes7, heads7]) rfl
  let tapes8 := Function.update tapes7 (.inl .shiftTemp) (stackAtOrigin [])
  let heads8 := Function.update heads7 (.inl .shiftTemp) 0
  have park9 := park .parkA .parkD (.inr .operandA) tapes8 heads8 a
    (by simp [tapes₀, heads₀, boundaryWords, tapes1, heads1, tapes2, heads2, tapes3, heads3, tapes4, heads4, tapes5, heads5, tapes6, heads6, tapes7, heads7, tapes8, heads8]) (by simp [tapes₀, heads₀, boundaryWords, tapes1, heads1, tapes2, heads2, tapes3, heads3, tapes4, heads4, tapes5, heads5, tapes6, heads6, tapes7, heads7, tapes8, heads8]) rfl
  let tapes9 := Function.update tapes8 (.inr .operandA) (stackAtOrigin a)
  let heads9 := Function.update heads8 (.inr .operandA) 0
  have park10 := park .parkD .parkCapacity (.inr .operandD) tapes9 heads9 d
    (by simp [tapes₀, heads₀, boundaryWords, tapes1, heads1, tapes2, heads2, tapes3, heads3, tapes4, heads4, tapes5, heads5, tapes6, heads6, tapes7, heads7, tapes8, heads8, tapes9, heads9]) (by simp [tapes₀, heads₀, boundaryWords, tapes1, heads1, tapes2, heads2, tapes3, heads3, tapes4, heads4, tapes5, heads5, tapes6, heads6, tapes7, heads7, tapes8, heads8, tapes9, heads9]) rfl
  let tapes10 := Function.update tapes9 (.inr .operandD) (stackAtOrigin d)
  let heads10 := Function.update heads9 (.inr .operandD) 0
  have park11 := park .parkCapacity .parkCapacityBackup (.inr .capacity) tapes10 heads10 capacity
    (by simp [tapes₀, heads₀, boundaryWords, tapes1, heads1, tapes2, heads2, tapes3, heads3, tapes4, heads4, tapes5, heads5, tapes6, heads6, tapes7, heads7, tapes8, heads8, tapes9, heads9, tapes10, heads10]) (by simp [tapes₀, heads₀, boundaryWords, tapes1, heads1, tapes2, heads2, tapes3, heads3, tapes4, heads4, tapes5, heads5, tapes6, heads6, tapes7, heads7, tapes8, heads8, tapes9, heads9, tapes10, heads10]) rfl
  let tapes11 := Function.update tapes10 (.inr .capacity) (stackAtOrigin capacity)
  let heads11 := Function.update heads10 (.inr .capacity) 0
  have park12 := park .parkCapacityBackup .parkQ (.inr .capacityBackup) tapes11 heads11 []
    (by simp [tapes₀, heads₀, boundaryWords, tapes1, heads1, tapes2, heads2, tapes3, heads3, tapes4, heads4, tapes5, heads5, tapes6, heads6, tapes7, heads7, tapes8, heads8, tapes9, heads9, tapes10, heads10, tapes11, heads11]) (by simp [tapes₀, heads₀, boundaryWords, tapes1, heads1, tapes2, heads2, tapes3, heads3, tapes4, heads4, tapes5, heads5, tapes6, heads6, tapes7, heads7, tapes8, heads8, tapes9, heads9, tapes10, heads10, tapes11, heads11]) rfl
  let tapes12 := Function.update tapes11 (.inr .capacityBackup) (stackAtOrigin [])
  let heads12 := Function.update heads11 (.inr .capacityBackup) 0
  have park13 := park .parkQ .parkR (.inr .quotientOut) tapes12 heads12 quotient
    (by simp [tapes₀, heads₀, boundaryWords, tapes1, heads1, tapes2, heads2, tapes3, heads3, tapes4, heads4, tapes5, heads5, tapes6, heads6, tapes7, heads7, tapes8, heads8, tapes9, heads9, tapes10, heads10, tapes11, heads11, tapes12, heads12]) (by simp [tapes₀, heads₀, boundaryWords, tapes1, heads1, tapes2, heads2, tapes3, heads3, tapes4, heads4, tapes5, heads5, tapes6, heads6, tapes7, heads7, tapes8, heads8, tapes9, heads9, tapes10, heads10, tapes11, heads11, tapes12, heads12]) rfl
  let tapes13 := Function.update tapes12 (.inr .quotientOut) (stackAtOrigin quotient)
  let heads13 := Function.update heads12 (.inr .quotientOut) 0
  have park14 := park .parkR .signalReturn (.inr .remainderOut) tapes13 heads13 remainder
    (by simp [tapes₀, heads₀, boundaryWords, tapes1, heads1, tapes2, heads2, tapes3, heads3, tapes4, heads4, tapes5, heads5, tapes6, heads6, tapes7, heads7, tapes8, heads8, tapes9, heads9, tapes10, heads10, tapes11, heads11, tapes12, heads12, tapes13, heads13]) (by simp [tapes₀, heads₀, boundaryWords, tapes1, heads1, tapes2, heads2, tapes3, heads3, tapes4, heads4, tapes5, heads5, tapes6, heads6, tapes7, heads7, tapes8, heads8, tapes9, heads9, tapes10, heads10, tapes11, heads11, tapes12, heads12, tapes13, heads13]) rfl
  let tapes14 := Function.update tapes13 (.inr .remainderOut) (stackAtOrigin remainder)
  let heads14 := Function.update heads13 (.inr .remainderOut) 0
  have hsignal : (run^[1])
      (some ((⟨.frame .signalReturn none, tapes14⟩ : PhysicalCfg), heads14)) =
      some ((⟨.returned, tapes14⟩ : PhysicalCfg), heads14) := by rfl
  have hall := chain (chain (chain (chain (chain (chain (chain (chain (chain (chain (chain (chain (chain (chain (chain hclean park1) park2) park3) park4) park5) park6) park7) park8) park9) park10) park11) park12) park13) park14) hsignal
  have ht : tapes14 = entryTapes a d capacity quotient remainder := by
    funext k
    cases k <;> rename_i k <;> cases k <;>
      simp [tapes₀, heads₀, boundaryWords, tapes1, heads1, tapes2, heads2, tapes3, heads3, tapes4, heads4, tapes5, heads5, tapes6, heads6, tapes7, heads7, tapes8, heads8, tapes9, heads9, tapes10, heads10, tapes11, heads11, tapes12, heads12, tapes13, heads13, tapes14, heads14, entryTapes, stackAtOrigin, stackAtTop]
  have hh : heads14 = fun _ => 0 := by
    funext k
    cases k <;> rename_i k <;> cases k <;>
      simp [tapes₀, heads₀, boundaryWords, tapes1, heads1, tapes2, heads2, tapes3, heads3, tapes4, heads4, tapes5, heads5, tapes6, heads6, tapes7, heads7, tapes8, heads8, tapes9, heads9, tapes10, heads10, tapes11, heads11, tapes12, heads12, tapes13, heads13, tapes14, heads14]
  rw [ht, hh] at hall
  have htime : (1 + ((3 * remainder.length + 2) + ((3 * quotient.length + 2) + ((3 * ([] : List Bool).length + 2) + ((3 * capacity.length + 2) + ((3 * d.length + 2) + ((3 * a.length + 2) + ((3 * ([] : List Bool).length + 2) + ((3 * ([] : List Bool).length + 2) + ((3 * ([] : List Bool).length + 2) + ((3 * ([] : List Bool).length + 2) + ((3 * ([] : List Bool).length + 2) + ((3 * ([] : List Bool).length + 2) + ((3 * ([] : List Bool).length + 2) + ((3 * ([] : List Bool).length + 2) + ((10 + 7 * FrameLoop.clearDivisor.outputs.length) * (words4 FrameLoop.clearDivisor.source).length + 3 + ((10 + 7 * FrameLoop.emitR.outputs.length) * (words3 FrameLoop.emitR.source).length + 3 + ((10 + 7 * FrameLoop.copyR.outputs.length) * (words2 FrameLoop.copyR.source).length + 3 + ((10 + 7 * FrameLoop.emitQ.outputs.length) * (words1 FrameLoop.emitQ.source).length + 3 + ((10 + 7 * FrameLoop.copyQ.outputs.length) * (initial FrameLoop.copyQ.source).length + 3 + 1)))))))))))))))))))) =
      37 * (quotient.length + remainder.length) + 10 * divisor.length +
        3 * (a.length + d.length + capacity.length) + 45 := by
    simp [initial, words1, words2, words3, words4, FrameLoop.result, FrameLoop.outputs,
      FrameLoop.source, divMachine, divDoneCfg, divCfg, divStacks, boundaryWords,
      Nat.mul_add, Nat.add_mul]
    ring
  rw [htime] at hall
  exact ⟨hall, rfl⟩

end D5.S0.Computability.PhysicalDivider
