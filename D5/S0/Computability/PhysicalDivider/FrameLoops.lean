/- GID: D5/S0/Computability/PhysicalDivider/FrameLoops
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Executed erasure, transfer and double-copy loops of the fixed frame program. -/

import D5.S0.Computability.PhysicalDivider.ExecutionBounds
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace D5.S0.Computability.PhysicalDivider
open Turing

/-- All active words with their heads on their top blocks. -/
def topFrameCfg (label : FrameLabel) (held : Option Bool)
    (words : ActiveTape → List Bool) : LocatedCfg :=
  (⟨.frame label held, fun k => stackAtTop (words k)⟩,
    fun k => 2 * (words k).length)

/-- The loop descriptions refer only to phases already in the fixed physical program. -/
inductive FrameLoop
  | clearQ | clearR | loadA | restoreA | loadD | restoreD
  | loadCapacity | restoreCapacity | copyQ | emitQ | copyR | emitR | clearDivisor
  deriving DecidableEq, Fintype

def FrameLoop.start : FrameLoop → FrameLabel
  | .clearQ => .clearQ | .clearR => .clearR | .loadA => .loadA | .restoreA => .restoreA
  | .loadD => .loadD | .restoreD => .restoreD | .loadCapacity => .loadCapacity
  | .restoreCapacity => .restoreCapacity | .copyQ => .copyQ | .emitQ => .emitQ
  | .copyR => .copyR | .emitR => .emitR | .clearDivisor => .clearDivisor

def FrameLoop.read : FrameLoop → FrameLabel
  | .clearQ => .clearQRead | .clearR => .clearRRead | .loadA => .loadARead
  | .restoreA => .restoreARead | .loadD => .loadDRead | .restoreD => .restoreDRead
  | .loadCapacity => .loadCapacityRead | .restoreCapacity => .restoreCapacityRead
  | .copyQ => .copyQRead | .emitQ => .emitQRead | .copyR => .copyRRead
  | .emitR => .emitRRead | .clearDivisor => .clearDivisorRead

def FrameLoop.after : FrameLoop → FrameLabel
  | .clearQ => .clearR | .clearR => .loadA | .loadA => .restoreA | .restoreA => .padD
  | .loadD => .restoreD | .restoreD => .padR | .loadCapacity => .restoreCapacity
  | .restoreCapacity => .enterSource | .copyQ => .emitQ | .emitQ => .copyR
  | .copyR => .emitR | .emitR => .clearDivisor | .clearDivisor => .parkDividend

def FrameLoop.source : FrameLoop → ActiveTape
  | .clearQ => .inr .quotientOut | .clearR => .inr .remainderOut
  | .loadA => .inr .operandA | .restoreA => .inr .capacityBackup
  | .loadD => .inr .operandD | .restoreD => .inl .shiftTemp
  | .loadCapacity => .inr .capacity | .restoreCapacity => .inr .capacityBackup
  | .copyQ => .inl .quotient | .emitQ => .inl .shiftTemp
  | .copyR => .inl .remainder | .emitR => .inl .shiftTemp
  | .clearDivisor => .inl .divisor

def FrameLoop.outputs : FrameLoop → List (ActiveTape × (Bool → Bool))
  | .clearQ | .clearR | .clearDivisor => []
  | .loadA => [(.inl .dividend, id), (.inr .capacityBackup, id)]
  | .restoreA => [(.inr .operandA, id)]
  | .loadD => [(.inl .shiftTemp, id)]
  | .restoreD => [(.inl .divisor, id), (.inr .operandD, id)]
  | .loadCapacity => [(.inr .capacityBackup, id), (.inl .remainder, fun _ => false)]
  | .restoreCapacity => [(.inr .capacity, id)]
  | .copyQ | .copyR => [(.inl .shiftTemp, id)]
  | .emitQ => [(.inr .quotientOut, id)]
  | .emitR => [(.inr .remainderOut, id)]

/-- A mathematical description of the finished words, not a machine transition. -/
def FrameLoop.result (loop : FrameLoop) (words : ActiveTape → List Bool) :
    ActiveTape → List Bool :=
  loop.outputs.foldl (fun ws out =>
    Function.update ws out.1 ((words loop.source).reverse.map out.2 ++ words out.1))
    (Function.update words loop.source [])

set_option maxHeartbeats 1600000 in
/-- Each iteration executes a pop, the branch read, and the listed pushes.
The empty-stack exit also pays its two reads and the branch read. -/
theorem frame_loop_execution (loop : FrameLoop) (held : Option Bool)
    (words : ActiveTape → List Bool) :
    ((fun o : Option LocatedCfg => o.bind locatedStep)^[
      (10 + 7 * loop.outputs.length) * (words loop.source).length + 3])
      (some (topFrameCfg loop.start held words)) =
      some (topFrameCfg loop.after none (loop.result words)) := by
  let run := fun o : Option LocatedCfg => o.bind locatedStep
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
  have pop (label next : FrameLabel) (held : Option Bool) (k : ActiveTape)
      (words : ActiveTape → List Bool)
      (hcode : frameInstruction label held = startBlock k .popMarker (.frame next held true)) :
      (run^[if (words k).isEmpty then 2 else 9]) (some (topFrameCfg label held words)) =
        some (topFrameCfg next (words k).head? (Function.update words k (words k).tail)) := by
    cases hs : words k with
    | nil =>
      simp [run, topFrameCfg, locatedStep, advanceHeads, instruction, hcode,
        startBlock, liftBlockAction, blockAction, executeInstruction, continueBlock,
        controlRead, stackAtTop, hs, Tape.mk₂, Tape.mk', Function.iterate_succ_apply]
      constructor <;> funext j <;> by_cases hj : j = k <;> simp [hj, hs]
    | cons b bs =>
      cases bs <;>
        simp [run, topFrameCfg, locatedStep, advanceHeads, instruction, hcode,
          startBlock, liftBlockAction, blockAction, executeInstruction, continueBlock,
          controlRead, stackAtTop, hs, cellsBelow, Tape.mk₂, Tape.mk', Tape.move,
          Tape.write, Function.update_idem, Function.iterate_succ_apply] <;>
        constructor <;> funext j <;> by_cases hj : j = k
      all_goals
        first
        | subst j
          simp [stackAtTop, hs, cellsBelow, Tape.mk₂, Tape.mk'] <;>
            first | omega | (apply Quotient.sound; exact Or.inr ⟨2, rfl⟩)
        | simp [Function.update, hj]
  have read (label next : FrameLabel) (held saved : Option Bool)
      (words : ActiveTape → List Bool)
      (hcode : frameInstruction label held = controlRead (.frame next saved)) :
      (run^[1]) (some (topFrameCfg label held words)) =
        some (topFrameCfg next saved words) := by
    simp [run, topFrameCfg, locatedStep, instruction, hcode,
      controlRead, executeInstruction, advanceHeads]
  have finish (loop : FrameLoop) (held : Option Bool) (words : ActiveTape → List Bool)
      (hempty : words loop.source = []) :
      (run^[3]) (some (topFrameCfg loop.start held words)) =
        some (topFrameCfg loop.after none words) := by
    have hp := pop loop.start loop.read held loop.source words (by cases loop <;> rfl)
    simp only [hempty, List.isEmpty_nil, ↓reduceIte, List.head?_nil, List.tail_nil] at hp
    have hup : Function.update words loop.source [] = words := by
      rw [← hempty]; exact Function.update_eq_self _ _
    rw [hup] at hp
    rw [show 3 = 1 + 2 from rfl, Function.iterate_add_apply, hp]
    exact read loop.read loop.after none none words (by cases loop <;> rfl)
  have body (loop : FrameLoop) (held : Option Bool) (words : ActiveTape → List Bool)
      (b : Bool) (bs : List Bool) (hsource : words loop.source = b :: bs) :
      (run^[10 + 7 * loop.outputs.length]) (some (topFrameCfg loop.start held words)) =
        some (topFrameCfg loop.start (some b)
          (loop.outputs.foldl (fun ws out => Function.update ws out.1 (out.2 b :: ws out.1))
            (Function.update words loop.source bs))) := by
    have hp := pop loop.start loop.read held loop.source words (by cases loop <;> rfl)
    simp only [hsource, List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte,
      List.head?_cons, List.tail_cons] at hp
    cases loop with
    | clearQ =>
      dsimp only [FrameLoop.start, FrameLoop.read, FrameLoop.source] at hp ⊢
      dsimp only [FrameLoop.outputs, List.length, List.foldl]
      have ht : 10 + 7 * (FrameLoop.outputs .clearQ).length = 1 + 9 := rfl
      change (run^[1 + 9]) _ = _
      rw [Function.iterate_add_apply, hp]
      rw [read .clearQRead .clearQ (some b) (some b) _ rfl]
    | clearR =>
      dsimp only [FrameLoop.start, FrameLoop.read, FrameLoop.source] at hp ⊢
      dsimp only [FrameLoop.outputs, List.length, List.foldl]
      have ht : 10 + 7 * (FrameLoop.outputs .clearR).length = 1 + 9 := rfl
      change (run^[1 + 9]) _ = _
      rw [Function.iterate_add_apply, hp]
      rw [read .clearRRead .clearR (some b) (some b) _ rfl]
    | clearDivisor =>
      dsimp only [FrameLoop.start, FrameLoop.read, FrameLoop.source] at hp ⊢
      dsimp only [FrameLoop.outputs, List.length, List.foldl]
      have ht : 10 + 7 * (FrameLoop.outputs .clearDivisor).length = 1 + 9 := rfl
      change (run^[1 + 9]) _ = _
      rw [Function.iterate_add_apply, hp]
      rw [read .clearDivisorRead .clearDivisor (some b) (some b) _ rfl]
    | loadA =>
      dsimp only [FrameLoop.start, FrameLoop.read, FrameLoop.source] at hp ⊢
      dsimp only [FrameLoop.outputs, List.length, List.foldl]
      have ht : 10 + 7 * (FrameLoop.outputs .loadA).length = 7 + (7 + (1 + 9)) := rfl
      change (run^[7 + (7 + (1 + 9))]) _ = _
      rw [Function.iterate_add_apply, Function.iterate_add_apply, Function.iterate_add_apply, hp]
      rw [read .loadARead .loadAPush (some b) (some b) _ rfl]
      rw [ push .loadAPush .loadABackup (some b) (some b) (.inl .dividend) b _ rfl]
      exact push .loadABackup .loadA (some b) (some b) (.inr .capacityBackup) b _ rfl
    | restoreA =>
      dsimp only [FrameLoop.start, FrameLoop.read, FrameLoop.source] at hp ⊢
      dsimp only [FrameLoop.outputs, List.length, List.foldl]
      have ht : 10 + 7 * (FrameLoop.outputs .restoreA).length = 7 + (1 + 9) := rfl
      change (run^[7 + (1 + 9)]) _ = _
      rw [Function.iterate_add_apply, Function.iterate_add_apply, hp]
      rw [read .restoreARead .restoreAPush (some b) (some b) _ rfl]
      exact push .restoreAPush .restoreA (some b) (some b) (.inr .operandA) b _ rfl
    | loadD =>
      dsimp only [FrameLoop.start, FrameLoop.read, FrameLoop.source] at hp ⊢
      dsimp only [FrameLoop.outputs, List.length, List.foldl]
      have ht : 10 + 7 * (FrameLoop.outputs .loadD).length = 7 + (1 + 9) := rfl
      change (run^[7 + (1 + 9)]) _ = _
      rw [Function.iterate_add_apply, Function.iterate_add_apply, hp]
      rw [read .loadDRead .loadDPush (some b) (some b) _ rfl]
      exact push .loadDPush .loadD (some b) (some b) (.inl .shiftTemp) b _ rfl
    | restoreD =>
      dsimp only [FrameLoop.start, FrameLoop.read, FrameLoop.source] at hp ⊢
      dsimp only [FrameLoop.outputs, List.length, List.foldl]
      have ht : 10 + 7 * (FrameLoop.outputs .restoreD).length = 7 + (7 + (1 + 9)) := rfl
      change (run^[7 + (7 + (1 + 9))]) _ = _
      rw [Function.iterate_add_apply, Function.iterate_add_apply, Function.iterate_add_apply, hp]
      rw [read .restoreDRead .restoreDPush (some b) (some b) _ rfl]
      rw [ push .restoreDPush .restoreDCopy (some b) (some b) (.inl .divisor) b _ rfl]
      exact push .restoreDCopy .restoreD (some b) (some b) (.inr .operandD) b _ rfl
    | loadCapacity =>
      dsimp only [FrameLoop.start, FrameLoop.read, FrameLoop.source] at hp ⊢
      dsimp only [FrameLoop.outputs, List.length, List.foldl]
      have ht : 10 + 7 * (FrameLoop.outputs .loadCapacity).length = 7 + (7 + (1 + 9)) := rfl
      change (run^[7 + (7 + (1 + 9))]) _ = _
      rw [Function.iterate_add_apply, Function.iterate_add_apply, Function.iterate_add_apply, hp]
      rw [read .loadCapacityRead .loadCapacityPush (some b) (some b) _ rfl]
      rw [ push .loadCapacityPush .loadCapacityZero (some b) (some b) (.inr .capacityBackup) b _ rfl]
      exact push .loadCapacityZero .loadCapacity (some b) (some b) (.inl .remainder) false _ rfl
    | restoreCapacity =>
      dsimp only [FrameLoop.start, FrameLoop.read, FrameLoop.source] at hp ⊢
      dsimp only [FrameLoop.outputs, List.length, List.foldl]
      have ht : 10 + 7 * (FrameLoop.outputs .restoreCapacity).length = 7 + (1 + 9) := rfl
      change (run^[7 + (1 + 9)]) _ = _
      rw [Function.iterate_add_apply, Function.iterate_add_apply, hp]
      rw [read .restoreCapacityRead .restoreCapacityPush (some b) (some b) _ rfl]
      exact push .restoreCapacityPush .restoreCapacity (some b) (some b) (.inr .capacity) b _ rfl
    | copyQ =>
      dsimp only [FrameLoop.start, FrameLoop.read, FrameLoop.source] at hp ⊢
      dsimp only [FrameLoop.outputs, List.length, List.foldl]
      have ht : 10 + 7 * (FrameLoop.outputs .copyQ).length = 7 + (1 + 9) := rfl
      change (run^[7 + (1 + 9)]) _ = _
      rw [Function.iterate_add_apply, Function.iterate_add_apply, hp]
      rw [read .copyQRead .copyQReverse (some b) (some b) _ rfl]
      exact push .copyQReverse .copyQ (some b) (some b) (.inl .shiftTemp) b _ rfl
    | emitQ =>
      dsimp only [FrameLoop.start, FrameLoop.read, FrameLoop.source] at hp ⊢
      dsimp only [FrameLoop.outputs, List.length, List.foldl]
      have ht : 10 + 7 * (FrameLoop.outputs .emitQ).length = 7 + (1 + 9) := rfl
      change (run^[7 + (1 + 9)]) _ = _
      rw [Function.iterate_add_apply, Function.iterate_add_apply, hp]
      rw [read .emitQRead .emitQPush (some b) (some b) _ rfl]
      exact push .emitQPush .emitQ (some b) (some b) (.inr .quotientOut) b _ rfl
    | copyR =>
      dsimp only [FrameLoop.start, FrameLoop.read, FrameLoop.source] at hp ⊢
      dsimp only [FrameLoop.outputs, List.length, List.foldl]
      have ht : 10 + 7 * (FrameLoop.outputs .copyR).length = 7 + (1 + 9) := rfl
      change (run^[7 + (1 + 9)]) _ = _
      rw [Function.iterate_add_apply, Function.iterate_add_apply, hp]
      rw [read .copyRRead .copyRReverse (some b) (some b) _ rfl]
      exact push .copyRReverse .copyR (some b) (some b) (.inl .shiftTemp) b _ rfl
    | emitR =>
      dsimp only [FrameLoop.start, FrameLoop.read, FrameLoop.source] at hp ⊢
      dsimp only [FrameLoop.outputs, List.length, List.foldl]
      have ht : 10 + 7 * (FrameLoop.outputs .emitR).length = 7 + (1 + 9) := rfl
      change (run^[7 + (1 + 9)]) _ = _
      rw [Function.iterate_add_apply, Function.iterate_add_apply, hp]
      rw [read .emitRRead .emitRPush (some b) (some b) _ rfl]
      exact push .emitRPush .emitR (some b) (some b) (.inr .remainderOut) b _ rfl
  have allWords (xs : List Bool) : ∀ held words, words loop.source = xs →
      (run^[(10 + 7 * loop.outputs.length) * xs.length + 3])
        (some (topFrameCfg loop.start held words)) =
        some (topFrameCfg loop.after none (loop.result words)) := by
    induction xs with
    | nil =>
      intro held words hs
      have hr := finish loop held words hs
      have he : loop.result words = words := by
        cases loop <;> funext k <;> cases k <;> rename_i k <;> cases k <;>
          simp only [FrameLoop.source] at hs <;>
          simp [FrameLoop.result, FrameLoop.outputs, FrameLoop.source, Function.update, hs]
      simpa [he] using hr
    | cons b bs ih =>
      intro held words hs
      let ws : ActiveTape → List Bool := loop.outputs.foldl
        (fun ws out => Function.update ws out.1 (out.2 b :: ws out.1))
        (Function.update words loop.source bs)
      have hws : ws loop.source = bs := by
        cases loop <;> simp [ws, FrameLoop.outputs, FrameLoop.source]
      have he : loop.result ws = loop.result words := by
        cases loop <;> funext k <;> cases k <;> rename_i k <;> cases k <;>
          simp only [FrameLoop.source] at hs <;>
          simp [FrameLoop.result, FrameLoop.outputs, FrameLoop.source, ws,
            List.reverse_cons, List.map_append, Function.update, hs, List.append_assoc]
      have hi := ih (some b) ws hws
      rw [he] at hi
      rw [show (10 + 7 * loop.outputs.length) * (b :: bs).length + 3 =
          ((10 + 7 * loop.outputs.length) * bs.length + 3) +
            (10 + 7 * loop.outputs.length) by simp [Nat.mul_add]; omega,
        Function.iterate_add_apply, body loop held words b bs hs]
      exact hi
  exact allWords (words loop.source) held words rfl

end D5.S0.Computability.PhysicalDivider
