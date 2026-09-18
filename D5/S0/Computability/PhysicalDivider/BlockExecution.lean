/- GID: D5/S0/Computability/PhysicalDivider/BlockExecution
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact microstep lifting from the concrete block table into the divider program. -/

import D5.S0.Computability.PhysicalDivider.CallProgram
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace D5.S0.Computability.PhysicalDivider
open Turing

def liftBlockCfg (k : ActiveTape) (next : Continuation)
    (tapes : ActiveTape → Tape Bool) (c : BlockCfg) : PhysicalCfg :=
  ⟨.block k c.control next, Function.update tapes k c.tape⟩

theorem block_lift_run (k : ActiveTape) (next : Continuation)
    (tapes : ActiveTape → Tape Bool) (n : ℕ) (c c' : BlockCfg)
    (h : ((fun o : Option BlockCfg => o.bind blockStep)^[n]) (some c) = some c') :
    ((fun o : Option PhysicalCfg => o.bind physicalStep)^[n])
      (some (liftBlockCfg k next tapes c)) = some (liftBlockCfg k next tapes c') := by
  have one (k : ActiveTape) (next : Continuation) (tapes : ActiveTape → Tape Bool)
      (c c' : BlockCfg) (h : blockStep c = some c') :
      physicalStep (liftBlockCfg k next tapes c) = some (liftBlockCfg k next tapes c') := by
    cases c with
    | mk pc tape =>
      cases pc <;>
        simp only [blockStep, blockAction] at h <;>
        cases h <;>
        simp [physicalStep, liftBlockCfg, instruction, blockAction, liftBlockAction,
          executeInstruction, Function.update_idem]
  induction n generalizing c' with
  | zero =>
      simp only [Function.iterate_zero, id_eq, Option.some.injEq] at h
      subst c'
      rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply'] at h ⊢
      cases he : ((fun o : Option BlockCfg => o.bind blockStep)^[n]) (some c) with
      | none => simp [he] at h
      | some middle =>
          rw [he] at h
          rw [ih middle he]
          exact one k next tapes middle c' h
end D5.S0.Computability.PhysicalDivider
