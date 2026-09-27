/- GID: D5/S0/Computability/PhysicalDivider/Rounds
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact fixed-width restoring-divider round and iteration equations. -/

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

import D5.S0.Computability.PhysicalDivider.Finalize
import D5.S0.Computability.PhysicalDivider.Shift

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Lax51Proofs.RamToTM

open Turing TM2

-- Source: proofs/Lax51Proofs/RamToTM/DivideMacro.lean:992-1026.
theorem div_round (b x : Bool)
    (dividend divisor remainder quotient : List Bool)
    (hlen : (x :: remainder).length = divisor.length) :
    let candidate := shiftInBit b (x :: remainder)
    let borrow := subBorrowOut candidate divisor false
    let nextRemainder := if borrow then candidate else subBits candidate divisor false
    ((fun o : Option divMachine.Cfg => o.bind divMachine.step)^[
      6 * (x :: remainder).length + 10])
      (some (divCleanCfg .outer true (b :: dividend) divisor (x :: remainder)
        quotient [])) =
      some (divCleanCfg .outer true dividend divisor nextRemainder
        ((!borrow) :: quotient) []) := by
  -- Original proof: proofs/Lax51Proofs/RamToTM/FixedWord.lean:443.
  have shiftInBit_length (bit : Bool) (bits : List Bool) :
      (shiftInBit bit bits).length = bits.length := by
    cases bits <;> simp [shiftInBit]
  let stepO := fun o : Option divMachine.Cfg => o.bind divMachine.step
  let candidate := shiftInBit b (x :: remainder)
  let borrow := subBorrowOut candidate divisor false
  have hs := div_shift_pipeline b x dividend divisor remainder quotient
  change (stepO^[2 * (x :: remainder).length + 4]) _ = _ at hs
  change _ = some (divPhaseCfg .subtract b false dividend divisor candidate quotient
    [] [] [] []) at hs
  have hcandidate : candidate.length = divisor.length := by
    simp [shiftInBit_length, candidate, hlen]
  have hd := div_subtract_pipeline b dividend divisor candidate quotient hcandidate
  change (stepO^[4 * candidate.length + 6]) _ = _ at hd
  have chain {m n : ℕ} {a c d : Option divMachine.Cfg}
      (h₁ : (stepO^[m]) a = c) (h₂ : (stepO^[n]) c = d) :
      (stepO^[n + m]) a = d := by
    rw [Function.iterate_add_apply, h₁, h₂]
  have h := chain hs hd
  have htime :
      4 * candidate.length + 6 + (2 * (x :: remainder).length + 4) =
        6 * (x :: remainder).length + 10 := by
    simp [shiftInBit_length, candidate]
    omega
  rw [htime] at h
  simpa [stepO, candidate, borrow] using h

-- Source: proofs/Lax51Proofs/RamToTM/DivideMacro.lean:1028-1069.
theorem div_round_fixed (w d : ℕ) (s : DivisionScan) (b : Bool)
    (bits : List Bool)
    (hd : d < 2 ^ w) (hr : s.remainder < d) :
    let s' := divisionScanStep d s b
    ((fun o : Option divMachine.Cfg => o.bind divMachine.step)^[
      6 * (w + 1) + 10])
      (some (divCleanCfg .outer true (b :: bits) (fixedBits (w + 1) d)
        (fixedBits (w + 1) s.remainder) s.quotient [])) =
      some (divCleanCfg .outer true bits (fixedBits (w + 1) d)
        (fixedBits (w + 1) s'.remainder) s'.quotient []) := by
  -- Original proof: proofs/Lax51Proofs/RamToTM/FixedWord.lean:313.
  have fixedBits_sub_of_le (w : ℕ) {a b : ℕ} (h : b ≤ a) :
      fixedBits w (a - b) = subBits (fixedBits w a) (fixedBits w b) false := by
    simpa using fixedBits_sub_borrow w a b false (by simpa using h)
  -- Original proof: proofs/Lax51Proofs/RamToTM/FixedWord.lean:349.
  have subBorrowOut_fixed_eq_decide_lt (w a b : ℕ)
      (ha : a < 2 ^ w) (hb : b < 2 ^ w) :
      subBorrowOut (fixedBits w a) (fixedBits w b) false = decide (a < b) := by
    -- Original proof: proofs/Lax51Proofs/RamToTM/FixedWord.lean:49.
    have bitsValue_fixedBits_of_lt {w n : ℕ} (h : n < 2 ^ w) :
        bitsValue (fixedBits w n) = n := by
      simp [bitsValue_fixedBits, Nat.mod_eq_of_lt h]
    -- Original proof: proofs/Lax51Proofs/RamToTM/FixedWord.lean:344.
    have subBorrowOut_fixed_false_of_le (w : ℕ) {a b : ℕ}
        (ha : a < 2 ^ w) (hb : b < 2 ^ w) (hba : b ≤ a) :
        subBorrowOut (fixedBits w a) (fixedBits w b) false = false := by
      exact subBorrowOut_fixed_false w false ha hb (by simpa using hba)
    by_cases hlt : a < b
    · have hi := subBits_value_identity false
        (show (fixedBits w a).length = (fixedBits w b).length by simp)
      rw [bitsValue_fixedBits_of_lt ha, bitsValue_fixedBits_of_lt hb] at hi
      cases hout : subBorrowOut (fixedBits w a) (fixedBits w b) false
      · simp [hout] at hi
        omega
      · simp [hlt]
    · have hout := subBorrowOut_fixed_false_of_le w ha hb (Nat.le_of_not_gt hlt)
      simp [hlt, hout]
  -- Original proof: proofs/Lax51Proofs/RamToTM/FixedWord.lean:465.
  have shiftInBit_fixed (w r : ℕ) (bit : Bool) :
      shiftInBit bit (fixedBits (w + 1) r) =
        fixedBits (w + 1) (2 * r + bit.toNat) := by
    simp only [fixedBits, shiftInBit, fixedBits_length]
    rw [show r.bodd :: fixedBits w r.div2 = fixedBits (w + 1) r by rfl,
      fixedBits_take]
    cases bit <;> simp [Nat.div2_val]
  -- Original proof: proofs/Lax51Proofs/RamToTM/FixedWord.lean:598.
  have divisionScan_candidate_lt_extra_bit {w d r : ℕ} (b : Bool)
      (hd : d < 2 ^ w) (hr : r < d) :
      2 * r + b.toNat < 2 ^ (w + 1) := by
    have hb : b.toNat ≤ 1 := by cases b <;> simp
    rw [pow_succ]
    omega
  let candidate := 2 * s.remainder + b.toNat
  have hc : candidate < 2 ^ (w + 1) :=
    divisionScan_candidate_lt_extra_bit b hd hr
  have hdextra : d < 2 ^ (w + 1) := by
    rw [pow_succ]
    omega
  have hround := div_round b s.remainder.bodd bits (fixedBits (w + 1) d)
    (fixedBits w s.remainder.div2) s.quotient (by simp)
  dsimp only at hround
  simp only [fixedBits_length, List.length_cons] at hround
  change ((fun o : Option divMachine.Cfg => o.bind divMachine.step)^[
      6 * (w + 1) + 10])
      (some (divCleanCfg .outer true (b :: bits) (fixedBits (w + 1) d)
        (fixedBits (w + 1) s.remainder) s.quotient [])) = _ at hround
  rw [show s.remainder.bodd :: fixedBits w s.remainder.div2 =
    fixedBits (w + 1) s.remainder by rfl] at hround
  rw [shiftInBit_fixed] at hround
  change _ = some (divCleanCfg .outer true bits (fixedBits (w + 1) d)
    (if subBorrowOut (fixedBits (w + 1) candidate) (fixedBits (w + 1) d) false
      then fixedBits (w + 1) candidate
      else subBits (fixedBits (w + 1) candidate) (fixedBits (w + 1) d) false)
    ((!subBorrowOut (fixedBits (w + 1) candidate) (fixedBits (w + 1) d) false) ::
      s.quotient) []) at hround
  rw [subBorrowOut_fixed_eq_decide_lt (w + 1) candidate d hc hdextra] at hround
  by_cases hle : d ≤ candidate
  · have hnlt : ¬ candidate < d := by omega
    have hsub := fixedBits_sub_of_le (w + 1) hle
    simp [divisionScanStep, candidate, hle, hnlt, hsub] at hround ⊢
    exact hround
  · have hlt : candidate < d := by omega
    simp [divisionScanStep, candidate, hle, hlt] at hround ⊢
    exact hround

-- Source: proofs/Lax51Proofs/RamToTM/DivideMacro.lean:1071-1098.
theorem div_rounds_fixed (w d : ℕ) (bits : List Bool) (s : DivisionScan)
    (hd0 : 0 < d) (hd : d < 2 ^ w) (hr : s.remainder < d) :
    ((fun o : Option divMachine.Cfg => o.bind divMachine.step)^[
      bits.length * (6 * (w + 1) + 10)])
      (some (divCleanCfg .outer true bits (fixedBits (w + 1) d)
        (fixedBits (w + 1) s.remainder) s.quotient [])) =
      some (divCleanCfg .outer true [] (fixedBits (w + 1) d)
        (fixedBits (w + 1) (divisionScan d s bits).remainder)
        (divisionScan d s bits).quotient []) := by
  -- Original proof: proofs/Lax51Proofs/RamToTM/FixedWord.lean:576.
  have divisionScanStep_invariant {d : ℕ} (hd : 0 < d)
      (s : DivisionScan) (b : Bool) (hr : s.remainder < d) :
      let s' := divisionScanStep d s b
      bitsValue s'.quotient * d + s'.remainder =
        2 * (bitsValue s.quotient * d + s.remainder) + b.toNat ∧
      s'.remainder < d := by
    simp only [divisionScanStep]
    have hb : b.toNat ≤ 1 := by cases b <;> simp
    have hcand : 2 * s.remainder + b.toNat < 2 * d := by omega
    by_cases hle : d ≤ 2 * s.remainder + b.toNat
    · simp [hle, bitsValue, Nat.bit_val]
      constructor
      · have hsub := Nat.sub_add_cancel hle
        ring_nf at hsub ⊢
        omega
      · omega
    · simp [hle, bitsValue, Nat.bit_val]
      constructor
      · ring
      · omega
  induction bits generalizing s with
  | nil => simp [divisionScan]
  | cons b bits ih =>
      let s' := divisionScanStep d s b
      have hr' : s'.remainder < d :=
        (divisionScanStep_invariant hd0 s b hr).2
      have hround := div_round_fixed w d s b bits hd hr
      have htail := ih s' hr'
      have hchain :
          ((fun o : Option divMachine.Cfg => o.bind divMachine.step)^[
            bits.length * (6 * (w + 1) + 10) + (6 * (w + 1) + 10)])
            (some (divCleanCfg .outer true (b :: bits) (fixedBits (w + 1) d)
              (fixedBits (w + 1) s.remainder) s.quotient [])) =
            some (divCleanCfg .outer true [] (fixedBits (w + 1) d)
              (fixedBits (w + 1) (divisionScan d s' bits).remainder)
              (divisionScan d s' bits).quotient []) := by
        rw [Function.iterate_add_apply, hround, htail]
      simpa [divisionScan, s', List.length_cons, Nat.add_mul, Nat.add_comm,
        Nat.add_left_comm, Nat.add_assoc] using hchain

end Lax51Proofs.RamToTM
