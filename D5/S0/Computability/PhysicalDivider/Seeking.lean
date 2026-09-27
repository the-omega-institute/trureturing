/- GID: D5/S0/Computability/PhysicalDivider/Seeking
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Counted physical traversal from a parked block to a word's top. -/

import D5.S0.Computability.PhysicalDivider.ExecutionBounds
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace D5.S0.Computability.PhysicalDivider
open Turing

/-- A partially traversed stack, used only as a representation relation. -/
def seekingCfg (k : ActiveTape) (next : Continuation)
    (tapes : ActiveTape → Tape Bool) (heads : ActiveTape → ℤ)
    (below above : List Bool) : LocatedCfg :=
  (⟨.block k .seekFirst next,
      Function.update tapes k (stackWithAbove below (above.flatMap (fun b => [true, b])))⟩,
    Function.update heads k (2 * below.length))

/-- Seeking visits each data block and the first blank block, then steps back.
The continuation read is included in the exact action count. -/
theorem seek_stack_execution (k : ActiveTape) (next : Continuation)
    (tapes : ActiveTape → Tape Bool) (heads : ActiveTape → ℤ)
    (below above : List Bool) :
    ((fun o : Option LocatedCfg => o.bind locatedStep)^[3 * above.length + 6])
      (some (seekingCfg k next tapes heads below above)) =
      some (⟨continueBlock next none,
        Function.update tapes k (stackAtTop (above.reverse ++ below))⟩,
        Function.update heads k (2 * (above.length + below.length))) := by
  let run := fun o : Option LocatedCfg => o.bind locatedStep
  induction above generalizing below with
  | nil =>
    cases below <;>
      simp [seekingCfg, locatedStep, instruction, executeInstruction, advanceHeads,
        blockAction, liftBlockAction, controlRead, Function.iterate_succ_apply,
        stackWithAbove, stackAtTop, Tape.mk₂, Tape.mk', Tape.move, cellsBelow,
        Function.update_idem] <;>
      congr 2 <;> apply Quotient.sound <;> exact Or.inr ⟨1, rfl⟩
  | cons b above ih =>
    have hthree : (run^[3]) (some (seekingCfg k next tapes heads below (b :: above))) =
        some (seekingCfg k next tapes heads (b :: below) above) := by
      cases below <;>
        simp [run, seekingCfg, locatedStep, instruction, executeInstruction, advanceHeads,
          blockAction, liftBlockAction, controlRead, Function.iterate_succ_apply,
          stackWithAbove, stackAtTop, Tape.mk₂, Tape.mk', Tape.move, cellsBelow,
          Function.update_idem] <;>
        congr 2 <;> omega
    rw [show 3 * (b :: above).length + 6 = (3 * above.length + 6) + 3 by simp; omega,
      Function.iterate_add_apply]
    change (run^[3 * above.length + 6]) ((run^[3]) _) = _
    rw [hthree, ih]
    simp [List.reverse_cons, List.append_assoc, add_assoc, add_left_comm, add_comm]

end D5.S0.Computability.PhysicalDivider
