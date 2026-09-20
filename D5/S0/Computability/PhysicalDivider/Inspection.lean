/- GID: D5/S0/Computability/PhysicalDivider/Inspection
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Executed inspection and restoration of the divisor. -/

/-
Source: szymtor/RAM-TM, commit 6fe5a3d94f6c2da46cc2c5ab98cd36997b130737.
Authors: Szymon Toruńczyk and Codex 5.6 (upstream manifest).
Apache-2.0; full license, source mapping and retirement condition:
Library/Computability/ramtm2026divider.md.
Original declaration names and proof derivations are retained. Import routing,
definitional unfolding and local inlining adapt the source to the current pin.
These symbolic program and word laws contain no certified finite instance,
bounded enumeration, certificate checker or conditional numerical reduction.
-/

import D5.S0.Computability.PhysicalDivider.Machine

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Lax51Proofs.RamToTM

open Turing TM2

-- Source: proofs/Lax51Proofs/RamToTM/DivideMacro.lean:190-192.
def containsTrue : List Bool → Bool
  | [] => false
  | b :: bs => b || containsTrue bs

-- Source: proofs/Lax51Proofs/RamToTM/DivideMacro.lean:207-213.
theorem containsTrue_false_bitsValue_zero {bits : List Bool}
    (h : containsTrue bits = false) : bitsValue bits = 0 := by
  induction bits with
  | nil => rfl
  | cons b bits ih =>
      simp [containsTrue] at h
      simp [bitsValue, h.1, ih h.2]

-- Source: proofs/Lax51Proofs/RamToTM/DivideMacro.lean:237-249.
theorem div_inspect_iterate (nz : Bool)
    (dividend divisor remainder backup : List Bool) :
    ((fun o : Option divMachine.Cfg => o.bind divMachine.step)^[divisor.length])
        (some (divCleanCfg .inspectDivisor nz dividend divisor remainder [] backup)) =
      some (divCleanCfg .inspectDivisor (nz || containsTrue divisor) dividend []
        remainder [] (divisor.reverse ++ backup)) := by
  -- Original proof: proofs/Lax51Proofs/RamToTM/DivideMacro.lean:215.
  have div_step_inspect_cons (nz b : Bool)
      (dividend divisor remainder backup : List Bool) :
      divMachine.step
          (divCleanCfg .inspectDivisor nz dividend (b :: divisor) remainder [] backup) =
        some (divCleanCfg .inspectDivisor (nz || b) dividend divisor remainder []
          (b :: backup)) := by
    simp [default, FinTM2.inhabitedσ, instInhabitedDivControl, instInhabitedDivControl.default, instInhabitedBool.default, divMachine, divCleanCfg, divCfg, divStacks, DivControl.clearHeld,
      Function.update]
    all_goals (congr 2 <;> first | rfl | (funext k; cases k <;> rfl))
  induction divisor generalizing nz backup with
  | nil => simp [containsTrue]
  | cons b divisor ih =>
      rw [List.length_cons, Function.iterate_succ_apply]
      simp only [Option.bind_some, div_step_inspect_cons]
      rw [ih]
      simp [containsTrue, List.reverse_cons, List.append_assoc, Bool.or_assoc]

-- Source: proofs/Lax51Proofs/RamToTM/DivideMacro.lean:274-287.
theorem div_restore_inspected_iterate (nz : Bool)
    (dividend divisor remainder quotient backup : List Bool) :
    ((fun o : Option divMachine.Cfg => o.bind divMachine.step)^[backup.length])
        (some (divCleanCfg .restoreInspectedDivisor nz dividend divisor remainder
          quotient backup)) =
      some (divCleanCfg .restoreInspectedDivisor nz dividend
        (backup.reverse ++ divisor) remainder quotient []) := by
  -- Original proof: proofs/Lax51Proofs/RamToTM/DivideMacro.lean:251.
  have div_step_restore_inspected_cons (nz b : Bool)
      (dividend divisor remainder quotient backup : List Bool) :
      divMachine.step (divCleanCfg .restoreInspectedDivisor nz dividend divisor remainder
          quotient (b :: backup)) =
        some (divCleanCfg .restoreInspectedDivisor nz dividend (b :: divisor) remainder
          quotient backup) := by
    simp [default, FinTM2.inhabitedσ, instInhabitedDivControl, instInhabitedDivControl.default, instInhabitedBool.default, divMachine, divMoveIteration, divCleanCfg, divCfg, divStacks,
      DivControl.clearHeld, Function.update]
    all_goals (congr 2 <;> first | rfl | (funext k; cases k <;> rfl))
  induction backup generalizing divisor with
  | nil => rfl
  | cons b backup ih =>
      rw [List.length_cons, Function.iterate_succ_apply]
      simp only [Option.bind_some, div_step_restore_inspected_cons]
      rw [ih]
      simp [List.reverse_cons, List.append_assoc]

end Lax51Proofs.RamToTM
