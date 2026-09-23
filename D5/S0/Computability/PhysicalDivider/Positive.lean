/- GID: D5/S0/Computability/PhysicalDivider/Positive
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact positive-divisor quotient, remainder and source-step runtime. -/

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

import D5.S0.Computability.PhysicalDivider.Inspection
import D5.S0.Computability.PhysicalDivider.Rounds

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Lax51Proofs.RamToTM

open Turing TM2

-- Source: proofs/Lax51Proofs/RamToTM/DivideMacro.lean:1106-1107.
def divPositiveRunTime (w : ℕ) : ℕ :=
  2 * (w + 1) + 3 + w * (6 * (w + 1) + 10) + 1

-- Source: proofs/Lax51Proofs/RamToTM/DivideMacro.lean:1182-1260.
theorem divMachine_positive_correct (w a d : ℕ)
    (ha : a < 2 ^ w) (hd0 : 0 < d) (hd : d < 2 ^ w) :
    ((fun o : Option divMachine.Cfg => o.bind divMachine.step)^[
      divPositiveRunTime w])
      (some (divInitialCfg (fixedBits w a).reverse (fixedBits (w + 1) d)
        (fixedBits (w + 1) 0))) =
      some (divDoneCfg true (fixedBits (w + 1) d) (fixedBits (w + 1) (a % d))
        (fixedBits w (a / d))) := by
  -- Original proof: proofs/Lax51Proofs/RamToTM/FixedWord.lean:49.
  have bitsValue_fixedBits_of_lt {w n : ℕ} (h : n < 2 ^ w) :
      bitsValue (fixedBits w n) = n := by
    simp [bitsValue_fixedBits, Nat.mod_eq_of_lt h]
  -- Original proof: proofs/Lax51Proofs/RamToTM/FixedWord.lean:665.
  have divisionScan_fixed_correct (w n d : ℕ)
      (hn : n < 2 ^ w) (hd : 0 < d) :
      let s := divisionScan d ⟨[], 0⟩ (fixedBits w n).reverse
      bitsValue s.quotient = n / d ∧ s.remainder = n % d := by
    -- Original proof: proofs/Lax51Proofs/RamToTM/FixedWord.lean:49.
    have bitsValue_fixedBits_of_lt {w n : ℕ} (h : n < 2 ^ w) :
        bitsValue (fixedBits w n) = n := by
      simp [bitsValue_fixedBits, Nat.mod_eq_of_lt h]
    -- Original proof: proofs/Lax51Proofs/RamToTM/FixedWord.lean:641.
    have divisionScan_zero_correct {d : ℕ} (hd : 0 < d) (bits : List Bool) :
        let s := divisionScan d ⟨[], 0⟩ bits
        bitsValue s.quotient = msbValue bits / d ∧
          s.remainder = msbValue bits % d := by
      have hi :
          bitsValue (divisionScan d ⟨[], 0⟩ bits).quotient * d +
              (divisionScan d ⟨[], 0⟩ bits).remainder = msbValue bits ∧
            (divisionScan d ⟨[], 0⟩ bits).remainder < d := by
        simpa [msbValue, bitsValue] using
          (divisionScan_invariant hd bits (⟨[], 0⟩ : DivisionScan) hd)
      let s := divisionScan d ⟨[], 0⟩ bits
      have hdiv : msbValue bits / d = bitsValue s.quotient := by
        apply Nat.div_eq_of_lt_le
        · dsimp [s] at hi ⊢
          nlinarith [hi.1, hi.2]
        · dsimp [s] at hi ⊢
          nlinarith [hi.1, hi.2]
      have hmod : s.remainder = msbValue bits % d := by
        have hcanonical := Nat.div_add_mod (msbValue bits) d
        dsimp [s] at hi ⊢
        rw [hdiv] at hcanonical
        nlinarith [hi.1, hcanonical]
      exact ⟨hdiv.symm, hmod⟩
    simpa [bitsValue_fixedBits_of_lt hn] using
      divisionScan_zero_correct hd (fixedBits w n).reverse
  -- Original proof: proofs/Lax51Proofs/RamToTM/DivideMacro.lean:227.
  have div_step_inspect_nil (nz : Bool)
      (dividend remainder backup : List Bool) :
      divMachine.step
          (divCleanCfg .inspectDivisor nz dividend [] remainder [] backup) =
        some (divCleanCfg .restoreInspectedDivisor nz dividend [] remainder [] backup) := by
    simp [default, FinTM2.inhabitedσ, instInhabitedDivControl, instInhabitedDivControl.default, instInhabitedBool.default, divMachine, divCleanCfg, divCfg, divStacks, DivControl.clearHeld]
    all_goals (congr 2 <;> first | rfl | (funext k; cases k <;> rfl))
  -- Original proof: proofs/Lax51Proofs/RamToTM/DivideMacro.lean:263.
  have div_step_restore_inspected_nil (nz : Bool)
      (dividend divisor remainder quotient : List Bool) :
      divMachine.step (divCleanCfg .restoreInspectedDivisor nz dividend divisor remainder
          quotient []) =
        some (divCleanCfg .dispatch nz dividend divisor remainder quotient []) := by
    simp [default, FinTM2.inhabitedσ, instInhabitedDivControl, instInhabitedDivControl.default, instInhabitedBool.default, divMachine, divMoveIteration, divCleanCfg, divCfg, divStacks,
      DivControl.clearHeld]
    all_goals (congr 2 <;> first | rfl | (funext k; cases k <;> rfl))
  -- Original proof: proofs/Lax51Proofs/RamToTM/DivideMacro.lean:295.
  have div_step_dispatch_true
      (dividend divisor remainder quotient : List Bool) :
      divMachine.step (divCleanCfg .dispatch true dividend divisor remainder quotient []) =
        some (divCleanCfg .outer true dividend divisor remainder quotient []) := by
    rfl
  -- Original proof: proofs/Lax51Proofs/RamToTM/DivideMacro.lean:301.
  have div_step_outer_nil
      (divisor remainder quotient : List Bool) :
      divMachine.step (divCleanCfg .outer true [] divisor remainder quotient []) =
        some (divDoneCfg true divisor remainder quotient) := by
    simp [default, FinTM2.inhabitedσ, instInhabitedDivControl, instInhabitedDivControl.default, instInhabitedBool.default, divMachine, divCleanCfg, divDoneCfg, divCfg, divStacks,
      DivControl.clearHeld]
    all_goals (congr 2 <;> first | rfl | (funext k; cases k <;> rfl))
  let stepO := fun o : Option divMachine.Cfg => o.bind divMachine.step
  have chain {m n : ℕ} {x y z : Option divMachine.Cfg}
      (h₁ : (stepO^[m]) x = y) (h₂ : (stepO^[n]) y = z) :
      (stepO^[n + m]) x = z := by
    rw [Function.iterate_add_apply, h₁, h₂]
  let dividend := (fixedBits w a).reverse
  let divisor := fixedBits (w + 1) d
  let remainder := fixedBits (w + 1) 0
  let initialScan : DivisionScan := ⟨[], 0⟩
  let finalScan := divisionScan d initialScan dividend
  have hdextra : d < 2 ^ (w + 1) := by
    rw [pow_succ]
    omega
  have htrue : containsTrue divisor = true := by
    cases hc : containsTrue divisor with
    | false =>
        have hz := containsTrue_false_bitsValue_zero hc
        rw [bitsValue_fixedBits_of_lt hdextra] at hz
        omega
    | true => rfl
  have hi := div_inspect_iterate false dividend divisor remainder []
  simp only [Bool.false_or, htrue, List.append_nil] at hi
  have hi0 : (stepO^[1])
      (some (divCleanCfg .inspectDivisor true dividend [] remainder [] divisor.reverse)) =
      some (divCleanCfg .restoreInspectedDivisor true dividend [] remainder []
        divisor.reverse) := by
    simpa [stepO] using div_step_inspect_nil true dividend remainder divisor.reverse
  have hr := div_restore_inspected_iterate true dividend [] remainder [] divisor.reverse
  simp only [List.length_reverse, List.reverse_reverse, List.append_nil] at hr
  have hr0 : (stepO^[1])
      (some (divCleanCfg .restoreInspectedDivisor true dividend divisor remainder [] [])) =
      some (divCleanCfg .dispatch true dividend divisor remainder [] []) := by
    simpa [stepO] using
      div_step_restore_inspected_nil true dividend divisor remainder ([] : List Bool)
  have hdsp : (stepO^[1])
      (some (divCleanCfg .dispatch true dividend divisor remainder [] [])) =
      some (divCleanCfg .outer true dividend divisor remainder [] []) := by
    simpa [stepO] using div_step_dispatch_true dividend divisor remainder []
  have hlo := div_rounds_fixed w d dividend initialScan hd0 hd hd0
  change (stepO^[dividend.length * (6 * (w + 1) + 10)])
      (some (divCleanCfg .outer true dividend divisor remainder [] [])) =
      some (divCleanCfg .outer true [] divisor
        (fixedBits (w + 1) finalScan.remainder) finalScan.quotient []) at hlo
  have hdone : (stepO^[1])
      (some (divCleanCfg .outer true [] divisor
        (fixedBits (w + 1) finalScan.remainder) finalScan.quotient [])) =
      some (divDoneCfg true divisor (fixedBits (w + 1) finalScan.remainder)
        finalScan.quotient) := by
    simpa [stepO] using div_step_outer_nil divisor
      (fixedBits (w + 1) finalScan.remainder) finalScan.quotient
  have h := chain (chain (chain (chain (chain (chain hi hi0) hr) hr0) hdsp) hlo) hdone
  have htime :
      1 + (dividend.length * (6 * (w + 1) + 10) +
        (1 + (1 + (divisor.length + (1 + divisor.length))))) =
        divPositiveRunTime w := by
    simp [dividend, divisor, divPositiveRunTime]
    omega
  rw [htime] at h
  have hscan := divisionScan_fixed_correct w a d ha hd0
  change bitsValue finalScan.quotient = a / d ∧ finalScan.remainder = a % d at hscan
  have hlen : finalScan.quotient.length = w := by
    dsimp [finalScan, initialScan, dividend]
    rw [divisionScan_quotient_length]
    simp
  have hquot : finalScan.quotient = fixedBits w (a / d) := by
    calc
      finalScan.quotient = fixedBits finalScan.quotient.length
          (bitsValue finalScan.quotient) := (fixedBits_bitsValue _).symm
      _ = fixedBits w (a / d) := by rw [hlen, hscan.1]
  rw [hscan.2, hquot] at h
  simpa [default, FinTM2.inhabitedσ, instInhabitedDivControl, instInhabitedDivControl.default, instInhabitedBool.default, stepO, divInitialCfg, divCleanCfg, dividend, divisor, remainder] using h

end Lax51Proofs.RamToTM
