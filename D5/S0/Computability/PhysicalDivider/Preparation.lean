/- GID: D5/S0/Computability/PhysicalDivider/Preparation
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Executed framed operand preparation with exact physical action accounting. -/

import D5.S0.Computability.PhysicalDivider.FrameLoops
import D5.S0.Computability.PhysicalDivider.Seeking
import Mathlib.Tactic.Ring
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace D5.S0.Computability.PhysicalDivider
open Turing Lax51Proofs.RamToTM

/-- The entry words include old output, which is cleared by the machine. -/
def boundaryWords (a d capacity q r : List Bool) : ActiveTape → List Bool
  | .inl _ => []
  | .inr .operandA => a
  | .inr .operandD => d
  | .inr .capacity => capacity
  | .inr .capacityBackup => []
  | .inr .quotientOut => q
  | .inr .remainderOut => r

/-- During arithmetic, the preserved operand and capacity copies are at their tops. -/
def preparedFrame (a d capacity : List Bool) : FrameTape → Tape Bool :=
  fun k => stackAtTop (boundaryWords a d capacity [] [] (.inr k))

def preparedHeads (a d capacity : List Bool) : FrameTape → ℤ :=
  fun k => 2 * (boundaryWords a d capacity [] [] (.inr k)).length

set_option maxHeartbeats 2400000 in
/-- All loads, reversals, copies, padding, clearing and head motion are executed.
The resulting source configuration is the exact padded input to the divider. -/
theorem preparation_execution (a d capacity oldQ oldR : List Bool) :
    ((fun o : Option LocatedCfg => o.bind locatedStep)^[
      44 * (a.length + d.length + capacity.length) +
        13 * (oldQ.length + oldR.length) + 69])
      (some (callEntry a d capacity oldQ oldR, fun _ => 0)) =
      some (locatedSourceCfg
        (divInitialCfg a.reverse (d ++ [false]) (List.replicate (capacity.length + 1) false))
        (preparedFrame a d capacity) (preparedHeads a d capacity)) := by
  let run := fun o : Option LocatedCfg => o.bind locatedStep
  have chain {i j : ℕ} {a b c : LocatedCfg}
      (h₁ : (run^[i]) (some a) = some b) (h₂ : (run^[j]) (some b) = some c) :
      (run^[j + i]) (some a) = some c := by rw [Function.iterate_add_apply, h₁, h₂]
  have seek (label next : FrameLabel) (held : Option Bool) (k : ActiveTape)
      (tapes : ActiveTape → Tape Bool) (heads : ActiveTape → ℤ) (bs : List Bool)
      (htape : tapes k = stackAtOrigin bs) (hhead : heads k = 0)
      (hcode : frameInstruction label held = startBlock k .seekFirst (.frame next held false)) :
      (run^[3 * bs.length + 6]) (some (⟨.frame label held, tapes⟩, heads)) =
        some (⟨.frame next held, Function.update tapes k (stackAtTop bs)⟩,
          Function.update heads k (2 * bs.length)) := by
    have h := seek_stack_execution k (.frame next held false) tapes heads [] bs.reverse
    have ht : Function.update tapes k (stackWithAbove []
        (bs.reverse.flatMap fun b => [true, b])) = tapes := by
      change Function.update tapes k (stackAtOrigin bs) = tapes
      rw [← htape]
      exact Function.update_eq_self _ _
    have hh : Function.update heads k 0 = heads := by rw [← hhead]; exact Function.update_eq_self _ _
    simp only [List.length_reverse, List.reverse_reverse, List.append_nil,
      List.length_nil, Nat.cast_zero, add_zero, seekingCfg, mul_zero, ht, hh,
      continueBlock, Bool.false_eq_true, ↓reduceIte] at h
    rw [show 3 * bs.length + 6 = (3 * bs.length + 5) + 1 by omega,
      Function.iterate_succ_apply] at h ⊢
    have hs : locatedStep (⟨.frame label held, tapes⟩, heads) =
        locatedStep (⟨.block k .seekFirst (.frame next held false), tapes⟩, heads) := by
      simp [locatedStep, instruction, hcode, startBlock, blockAction]
    change (run^[3 * bs.length + 5]) (locatedStep _) = _
    rw [hs]
    exact h
  have push (label next : FrameLabel) (held saved : Option Bool) (k : ActiveTape) (b : Bool)
      (words : ActiveTape → List Bool)
      (hcode : frameInstruction label held =
        startBlock k (.pushFirst b) (.frame next saved false)) :
      (run^[7]) (some (topFrameCfg label held words)) =
        some (topFrameCfg next saved (Function.update words k (b :: words k))) := by
    cases hs : words k <;>
      simp [run, topFrameCfg, locatedStep, advanceHeads, instruction, hcode,
        startBlock, liftBlockAction, blockAction, executeInstruction, continueBlock,
        controlRead, stackAtTop, hs, cellsBelow, Tape.mk₂, Tape.mk', Tape.move,
        Tape.write, Function.update_idem, Function.iterate_succ_apply] <;>
      constructor <;> funext j <;> by_cases hj : j = k
    all_goals
      first
      | subst j
        simp [hs, stackAtTop, cellsBelow, Tape.mk₂, Tape.mk'] <;> omega
      | simp [Function.update, hj]
  let initial := boundaryWords a d capacity oldQ oldR
  let tapes₀ := entryTapes a d capacity oldQ oldR
  let heads₀ : ActiveTape → ℤ := fun _ => 0
  have seek₁ := seek .seekA .seekD none (.inr .operandA) tapes₀ heads₀ a
    (by simp [tapes₀, heads₀, entryTapes]) (by simp [tapes₀, heads₀, entryTapes]) rfl
  let tapes₁ := Function.update tapes₀ (.inr .operandA) (stackAtTop a)
  let heads₁ := Function.update heads₀ (.inr .operandA) (2 * (a.length : ℤ))
  have seek₂ := seek .seekD .seekCapacity none (.inr .operandD) tapes₁ heads₁ d
    (by simp [tapes₀, heads₀, entryTapes, tapes₁, heads₁]) (by simp [tapes₀, heads₀, entryTapes, tapes₁, heads₁]) rfl
  let tapes₂ := Function.update tapes₁ (.inr .operandD) (stackAtTop d)
  let heads₂ := Function.update heads₁ (.inr .operandD) (2 * (d.length : ℤ))
  have seek₃ := seek .seekCapacity .seekQ none (.inr .capacity) tapes₂ heads₂ capacity
    (by simp [tapes₀, heads₀, entryTapes, tapes₁, heads₁, tapes₂, heads₂]) (by simp [tapes₀, heads₀, entryTapes, tapes₁, heads₁, tapes₂, heads₂]) rfl
  let tapes₃ := Function.update tapes₂ (.inr .capacity) (stackAtTop capacity)
  let heads₃ := Function.update heads₂ (.inr .capacity) (2 * (capacity.length : ℤ))
  have seek₄ := seek .seekQ .seekR none (.inr .quotientOut) tapes₃ heads₃ oldQ
    (by simp [tapes₀, heads₀, entryTapes, tapes₁, heads₁, tapes₂, heads₂, tapes₃, heads₃]) (by simp [tapes₀, heads₀, entryTapes, tapes₁, heads₁, tapes₂, heads₂, tapes₃, heads₃]) rfl
  let tapes₄ := Function.update tapes₃ (.inr .quotientOut) (stackAtTop oldQ)
  let heads₄ := Function.update heads₃ (.inr .quotientOut) (2 * (oldQ.length : ℤ))
  have seek₅ := seek .seekR .clearQ none (.inr .remainderOut) tapes₄ heads₄ oldR
    (by simp [tapes₀, heads₀, entryTapes, tapes₁, heads₁, tapes₂, heads₂, tapes₃, heads₃, tapes₄, heads₄]) (by simp [tapes₀, heads₀, entryTapes, tapes₁, heads₁, tapes₂, heads₂, tapes₃, heads₃, tapes₄, heads₄]) rfl
  let tapes₅ := Function.update tapes₄ (.inr .remainderOut) (stackAtTop oldR)
  let heads₅ := Function.update heads₄ (.inr .remainderOut) (2 * (oldR.length : ℤ))
  have hs := chain (chain (chain (chain seek₁ seek₂) seek₃) seek₄) seek₅
  have he : (⟨.frame .clearQ none, tapes₅⟩, heads₅) = topFrameCfg .clearQ none initial := by
    apply Prod.ext
    · apply congrArg (fun tapes => (⟨.frame .clearQ none, tapes⟩ : PhysicalCfg))
      funext k
      cases k <;> rename_i k <;> cases k <;>
        simp [tapes₀, heads₀, entryTapes, tapes₁, heads₁, tapes₂, heads₂, tapes₃, heads₃, tapes₄, heads₄, tapes₅, heads₅, topFrameCfg, initial, boundaryWords, stackAtOrigin, stackAtTop]
    · funext k
      cases k <;> rename_i k <;> cases k <;>
        simp [tapes₀, heads₀, entryTapes, tapes₁, heads₁, tapes₂, heads₂, tapes₃, heads₃, tapes₄, heads₄, tapes₅, heads₅, topFrameCfg, initial, boundaryWords]
  change _ = some ((⟨.frame .clearQ none, tapes₅⟩ : PhysicalCfg), heads₅) at hs
  rw [he] at hs
  have h1 := frame_loop_execution .clearQ none initial
  let words1 := FrameLoop.result .clearQ initial
  have h2 := frame_loop_execution .clearR none words1
  let words2 := FrameLoop.result .clearR words1
  have h3 := frame_loop_execution .loadA none words2
  let words3 := FrameLoop.result .loadA words2
  have h4 := frame_loop_execution .restoreA none words3
  let words4 := FrameLoop.result .restoreA words3
  have h5 := push .padD .loadD none none (.inl .divisor) false words4 rfl
  let words5 := Function.update words4 (.inl .divisor) (false :: words4 (.inl .divisor))
  have h6 := frame_loop_execution .loadD none words5
  let words6 := FrameLoop.result .loadD words5
  have h7 := frame_loop_execution .restoreD none words6
  let words7 := FrameLoop.result .restoreD words6
  have h8 := push .padR .loadCapacity none none (.inl .remainder) false words7 rfl
  let words8 := Function.update words7 (.inl .remainder) (false :: words7 (.inl .remainder))
  have h9 := frame_loop_execution .loadCapacity none words8
  let words9 := FrameLoop.result .loadCapacity words8
  have h10 := frame_loop_execution .restoreCapacity none words9
  let words10 := FrameLoop.result .restoreCapacity words9
  have henter : (run^[1]) (some (topFrameCfg .enterSource none words10)) =
      some ((⟨.sourceLabel .inspectDivisor default, fun k => stackAtTop (words10 k)⟩ : PhysicalCfg),
        fun k => 2 * ((words10 k).length : ℤ)) := by rfl
  have hall := chain (chain (chain (chain (chain (chain (chain (chain (chain (chain (chain hs h1) h2) h3) h4) h5) h6) h7) h8) h9) h10) henter
  have hwords : words10 = fun k => match k with
      | .inl j => (divInitialCfg a.reverse (d ++ [false])
          (List.replicate (capacity.length + 1) false)).stk j
      | .inr j => boundaryWords a d capacity [] [] (.inr j) := by
    funext k
    cases k <;> rename_i k <;> cases k <;>
      simp [initial, words1, words2, words3, words4, words5, words6, words7, words8, words9, words10, FrameLoop.result, FrameLoop.outputs, FrameLoop.source,
        boundaryWords, divInitialCfg, divCfg, divStacks, List.reverse_append,
        List.replicate_add, List.replicate_succ, List.append_assoc] <;>
      simpa only [List.replicate_succ] using
        (List.replicate_succ' (n := capacity.length) (a := false)).symm
  have hend : ((⟨.sourceLabel .inspectDivisor default,
      fun k => stackAtTop (words10 k)⟩ : PhysicalCfg),
      fun k => 2 * ((words10 k).length : ℤ)) = locatedSourceCfg
        (divInitialCfg a.reverse (d ++ [false]) (List.replicate (capacity.length + 1) false))
        (preparedFrame a d capacity) (preparedHeads a d capacity) := by
    rw [hwords]
    apply Prod.ext
    · apply congrArg (fun tapes =>
        (⟨.sourceLabel .inspectDivisor default, tapes⟩ : PhysicalCfg))
      funext k
      cases k <;> rfl
    · funext k
      cases k <;> rfl
  rw [hend] at hall
  have htime : (1 + (((10 + 7 * FrameLoop.restoreCapacity.outputs.length) * (words9 FrameLoop.restoreCapacity.source).length + 3) + (((10 + 7 * FrameLoop.loadCapacity.outputs.length) * (words8 FrameLoop.loadCapacity.source).length + 3) + (7 + (((10 + 7 * FrameLoop.restoreD.outputs.length) * (words6 FrameLoop.restoreD.source).length + 3) + (((10 + 7 * FrameLoop.loadD.outputs.length) * (words5 FrameLoop.loadD.source).length + 3) + (7 + (((10 + 7 * FrameLoop.restoreA.outputs.length) * (words3 FrameLoop.restoreA.source).length + 3) + (((10 + 7 * FrameLoop.loadA.outputs.length) * (words2 FrameLoop.loadA.source).length + 3) + (((10 + 7 * FrameLoop.clearR.outputs.length) * (words1 FrameLoop.clearR.source).length + 3) + (((10 + 7 * FrameLoop.clearQ.outputs.length) * (initial FrameLoop.clearQ.source).length + 3) + (3 * oldR.length + 6 + (3 * oldQ.length + 6 + (3 * capacity.length + 6 + (3 * d.length + 6 + (3 * a.length + 6)))))))))))))))) =
      44 * (a.length + d.length + capacity.length) +
        13 * (oldQ.length + oldR.length) + 69 := by
    simp [initial, words1, words2, words3, words4, words5, words6, words7, words8,
      words9, FrameLoop.outputs, FrameLoop.source, FrameLoop.result, boundaryWords,
      Nat.mul_add, Nat.add_mul]
    ring
  rw [htime] at hall
  exact hall

end D5.S0.Computability.PhysicalDivider
