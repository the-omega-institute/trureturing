/- GID: D5/S0/Computability/PhysicalDivider/WordArithmetic
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Fixed-width Boolean words and the restoring-division scan invariant. -/

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

import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Lax51Proofs.RamToTM

-- Source: proofs/Lax51Proofs/RamToTM/FixedWord.lean:10-12.
def bitsValue : List Bool → ℕ
  | [] => 0
  | b :: bs => Nat.bit b (bitsValue bs)

-- Source: proofs/Lax51Proofs/RamToTM/FixedWord.lean:15-17.
def fixedBits : ℕ → ℕ → List Bool
  | 0, _ => []
  | w + 1, n => n.bodd :: fixedBits w n.div2

-- Source: proofs/Lax51Proofs/RamToTM/FixedWord.lean:19-20.
@[simp] theorem fixedBits_length (w n : ℕ) : (fixedBits w n).length = w := by
  induction w generalizing n <;> simp [fixedBits, *]

-- Source: proofs/Lax51Proofs/RamToTM/FixedWord.lean:41-47.
@[simp] theorem bitsValue_fixedBits (w n : ℕ) :
    bitsValue (fixedBits w n) = n % 2 ^ w := by
  -- Original proof: proofs/Lax51Proofs/RamToTM/FixedWord.lean:28.
  have bit_mod_two_pow (b : Bool) (n w : ℕ) :
      Nat.bit b (n % 2 ^ w) = Nat.bit b n % 2 ^ (w + 1) := by
    simp only [Nat.bit_val, pow_succ]
    let M := 2 ^ w
    have hM : 0 < M := by simp [M]
    have hn : n % M < M := Nat.mod_lt _ hM
    have hb : b.toNat ≤ 1 := by cases b <;> simp
    have hsmall : 2 * (n % M) + b.toNat < M * 2 := by omega
    rw [← Nat.mod_eq_of_lt hsmall]
    simpa [Nat.ModEq, M, Nat.mul_comm] using
      (Nat.ModEq.mul_left' 2 (Nat.mod_modEq n M)).add
        (Nat.ModEq.rfl : b.toNat ≡ b.toNat [MOD 2 * M])
  induction w generalizing n with
  | zero => simp [fixedBits, bitsValue, Nat.mod_one]
  | succ w ih =>
      simp only [fixedBits, bitsValue, ih]
      rw [bit_mod_two_pow, Nat.bit_bodd_div2]

-- Source: proofs/Lax51Proofs/RamToTM/FixedWord.lean:215-217.
def fullSubtractor (a b borrow : Bool) : Bool × Bool :=
  (xor (xor a b) borrow,
    ((!a) && (b || borrow)) || (b && borrow))

-- Source: proofs/Lax51Proofs/RamToTM/FixedWord.lean:224-228.
def subBits : List Bool → List Bool → Bool → List Bool
  | a :: as, b :: bs, borrow =>
      let q := fullSubtractor a b borrow
      q.1 :: subBits as bs q.2
  | _, _, _ => []

-- Source: proofs/Lax51Proofs/RamToTM/FixedWord.lean:230-233.
def subBorrowOut : List Bool → List Bool → Bool → Bool
  | a :: as, b :: bs, borrow =>
      subBorrowOut as bs (fullSubtractor a b borrow).2
  | _, _, borrow => borrow

-- Source: proofs/Lax51Proofs/RamToTM/FixedWord.lean:235-245.
theorem subBits_length_of_eq {as bs : List Bool} (borrow : Bool)
    (h : as.length = bs.length) : (subBits as bs borrow).length = as.length := by
  induction as generalizing bs borrow with
  | nil =>
      cases bs <;> simp [subBits] at h ⊢
  | cons a as ih =>
      cases bs with
      | nil => simp at h
      | cons b bs =>
          simp at h
          simp [subBits, ih _ h]

-- Source: proofs/Lax51Proofs/RamToTM/FixedWord.lean:247-266.
theorem subBits_value_identity {as bs : List Bool} (borrow : Bool)
    (h : as.length = bs.length) :
    bitsValue as + 2 ^ as.length * (subBorrowOut as bs borrow).toNat =
      bitsValue bs + borrow.toNat + bitsValue (subBits as bs borrow) := by
  -- Original proof: proofs/Lax51Proofs/RamToTM/FixedWord.lean:219.
  have fullSubtractor_value (a b borrow : Bool) :
      a.toNat + 2 * (fullSubtractor a b borrow).2.toNat =
        b.toNat + borrow.toNat + (fullSubtractor a b borrow).1.toNat := by
    cases a <;> cases b <;> cases borrow <;> decide
  induction as generalizing bs borrow with
  | nil =>
      cases bs with
      | nil => simp [bitsValue, subBits, subBorrowOut]
      | cons _ _ => simp at h
  | cons a as ih =>
      cases bs with
      | nil => simp at h
      | cons b bs =>
          simp at h
          have ht := ih (borrow := (fullSubtractor a b borrow).2)
            (bs := bs) h
          have hf := fullSubtractor_value a b borrow
          simp only [bitsValue, subBits, subBorrowOut, List.length_cons, pow_succ]
          simp only [bitsValue, Nat.bit_val] at ht ⊢
          nlinarith

-- Source: proofs/Lax51Proofs/RamToTM/FixedWord.lean:300-311.
theorem fixedBits_sub_borrow (w a b : ℕ) (borrow : Bool)
    (h : b + borrow.toNat ≤ a) :
    fixedBits w (a - (b + borrow.toNat)) =
      subBits (fixedBits w a) (fixedBits w b) borrow := by
  -- Original proof: proofs/Lax51Proofs/RamToTM/FixedWord.lean:272.
  have sub_borrow_head_tail (a b : ℕ) (borrow : Bool)
      (h : b + borrow.toNat ≤ a) :
      let d := a - (b + borrow.toNat)
      d.bodd = (fullSubtractor a.bodd b.bodd borrow).1 ∧
        d.div2 = a.div2 -
          (b.div2 + (fullSubtractor a.bodd b.bodd borrow).2.toNat) ∧
        b.div2 + (fullSubtractor a.bodd b.bodd borrow).2.toNat ≤ a.div2 := by
    -- Original proof: proofs/Lax51Proofs/RamToTM/FixedWord.lean:219.
    have fullSubtractor_value (a b borrow : Bool) :
        a.toNat + 2 * (fullSubtractor a b borrow).2.toNat =
          b.toNat + borrow.toNat + (fullSubtractor a b borrow).1.toNat := by
      cases a <;> cases b <;> cases borrow <;> decide
    let d := a - (b + borrow.toNat)
    have hd : b + borrow.toNat + d = a := by
      dsimp [d]
      omega
    have ha := Nat.bodd_add_div2 a
    have hb := Nat.bodd_add_div2 b
    have hd' := Nat.bodd_add_div2 d
    have hf := fullSubtractor_value a.bodd b.bodd borrow
    have hhead : d.bodd = (fullSubtractor a.bodd b.bodd borrow).1 := by
      cases hba : a.bodd <;> cases hbb : b.bodd <;> cases hbd : d.bodd <;>
        cases borrow <;> simp_all [fullSubtractor] <;> omega
    have hquot :
        a.div2 = b.div2 +
          (fullSubtractor a.bodd b.bodd borrow).2.toNat + d.div2 := by
      cases hba : a.bodd <;> cases hbb : b.bodd <;> cases hbd : d.bodd <;>
        cases borrow <;> simp_all [fullSubtractor] <;> omega
    refine ⟨hhead, ?_, ?_⟩
    · rw [hquot, Nat.add_sub_cancel_left]
    · rw [hquot]
      omega
  induction w generalizing a b borrow with
  | zero => rfl
  | succ w ih =>
      obtain ⟨hhead, htail, hnext⟩ := sub_borrow_head_tail a b borrow h
      simp only [fixedBits, subBits]
      rw [hhead, htail]
      apply congrArg ((fullSubtractor a.bodd b.bodd borrow).1 :: ·)
      exact ih _ _ _ hnext

-- Source: proofs/Lax51Proofs/RamToTM/FixedWord.lean:322-342.
theorem subBorrowOut_fixed_false (w : ℕ) {a b : ℕ} (borrow : Bool)
    (ha : a < 2 ^ w) (hb : b < 2 ^ w) (hba : b + borrow.toNat ≤ a) :
    subBorrowOut (fixedBits w a) (fixedBits w b) borrow = false := by
  -- Original proof: proofs/Lax51Proofs/RamToTM/FixedWord.lean:272.
  have sub_borrow_head_tail (a b : ℕ) (borrow : Bool)
      (h : b + borrow.toNat ≤ a) :
      let d := a - (b + borrow.toNat)
      d.bodd = (fullSubtractor a.bodd b.bodd borrow).1 ∧
        d.div2 = a.div2 -
          (b.div2 + (fullSubtractor a.bodd b.bodd borrow).2.toNat) ∧
        b.div2 + (fullSubtractor a.bodd b.bodd borrow).2.toNat ≤ a.div2 := by
    -- Original proof: proofs/Lax51Proofs/RamToTM/FixedWord.lean:219.
    have fullSubtractor_value (a b borrow : Bool) :
        a.toNat + 2 * (fullSubtractor a b borrow).2.toNat =
          b.toNat + borrow.toNat + (fullSubtractor a b borrow).1.toNat := by
      cases a <;> cases b <;> cases borrow <;> decide
    let d := a - (b + borrow.toNat)
    have hd : b + borrow.toNat + d = a := by
      dsimp [d]
      omega
    have ha := Nat.bodd_add_div2 a
    have hb := Nat.bodd_add_div2 b
    have hd' := Nat.bodd_add_div2 d
    have hf := fullSubtractor_value a.bodd b.bodd borrow
    have hhead : d.bodd = (fullSubtractor a.bodd b.bodd borrow).1 := by
      cases hba : a.bodd <;> cases hbb : b.bodd <;> cases hbd : d.bodd <;>
        cases borrow <;> simp_all [fullSubtractor] <;> omega
    have hquot :
        a.div2 = b.div2 +
          (fullSubtractor a.bodd b.bodd borrow).2.toNat + d.div2 := by
      cases hba : a.bodd <;> cases hbb : b.bodd <;> cases hbd : d.bodd <;>
        cases borrow <;> simp_all [fullSubtractor] <;> omega
    refine ⟨hhead, ?_, ?_⟩
    · rw [hquot, Nat.add_sub_cancel_left]
    · rw [hquot]
      omega
  induction w generalizing a b borrow with
  | zero =>
      simp at ha hb
      subst a
      subst b
      cases borrow <;> simp_all [subBorrowOut, fixedBits]
  | succ w ih =>
      obtain ⟨_, _, hnext⟩ := sub_borrow_head_tail a b borrow hba
      have ha' : a.div2 < 2 ^ w := by
        change a / 2 < 2 ^ w
        rw [pow_succ] at ha
        omega
      have hb' : b.div2 < 2 ^ w := by
        change b / 2 < 2 ^ w
        rw [pow_succ] at hb
        omega
      simp only [fixedBits, subBorrowOut]
      exact ih _ ha' hb' hnext

-- Source: proofs/Lax51Proofs/RamToTM/FixedWord.lean:416-421.
theorem fixedBits_bitsValue (xs : List Bool) :
    fixedBits xs.length (bitsValue xs) = xs := by
  induction xs with
  | nil => rfl
  | cons b bs ih =>
      simp [fixedBits, bitsValue, ih]

-- Source: proofs/Lax51Proofs/RamToTM/FixedWord.lean:423-430.
theorem fixedBits_take (k w n : ℕ) :
    (fixedBits w n).take k = fixedBits (min k w) n := by
  induction k generalizing w n with
  | zero => simp [fixedBits]
  | succ k ih =>
      cases w with
      | zero => simp [fixedBits]
      | succ w => simp [fixedBits, ih, Nat.succ_min_succ]

-- Source: proofs/Lax51Proofs/RamToTM/FixedWord.lean:439-441.
def shiftInBit (bit : Bool) : List Bool → List Bool
  | [] => []
  | x :: xs => bit :: (x :: xs).take xs.length

-- Source: proofs/Lax51Proofs/RamToTM/FixedWord.lean:473-475.
@[simp] theorem fixedBits_zero (w : ℕ) :
    fixedBits w 0 = List.replicate w false := by
  induction w <;> simp [fixedBits, List.replicate_succ, *]

-- Source: proofs/Lax51Proofs/RamToTM/FixedWord.lean:542-544.
def msbValueFrom : ℕ → List Bool → ℕ
  | acc, [] => acc
  | acc, b :: bs => msbValueFrom (2 * acc + b.toNat) bs

-- Source: proofs/Lax51Proofs/RamToTM/FixedWord.lean:546-546.
def msbValue (bits : List Bool) : ℕ := msbValueFrom 0 bits

-- Source: proofs/Lax51Proofs/RamToTM/FixedWord.lean:548-550.
theorem msbValueFrom_append (acc : ℕ) (xs ys : List Bool) :
    msbValueFrom acc (xs ++ ys) = msbValueFrom (msbValueFrom acc xs) ys := by
  induction xs generalizing acc <;> simp [msbValueFrom, *]

-- Source: proofs/Lax51Proofs/RamToTM/FixedWord.lean:552-559.
@[simp] theorem msbValue_reverse (xs : List Bool) :
    msbValue xs.reverse = bitsValue xs := by
  induction xs with
  | nil => rfl
  | cons b bs ih =>
      change msbValueFrom 0 bs.reverse = bitsValue bs at ih
      simp [msbValue, msbValueFrom_append, msbValueFrom, bitsValue, ih,
        Nat.bit_val]

-- Source: proofs/Lax51Proofs/RamToTM/FixedWord.lean:561-563.
structure DivisionScan where
  quotient : List Bool
  remainder : ℕ

-- Source: proofs/Lax51Proofs/RamToTM/FixedWord.lean:565-570.
def divisionScanStep (divisor : ℕ) (s : DivisionScan) (bit : Bool) :
    DivisionScan :=
  let candidate := 2 * s.remainder + bit.toNat
  let quotientBit := decide (divisor ≤ candidate)
  { quotient := quotientBit :: s.quotient,
    remainder := if quotientBit then candidate - divisor else candidate }

-- Source: proofs/Lax51Proofs/RamToTM/FixedWord.lean:572-574.
def divisionScan (divisor : ℕ) : DivisionScan → List Bool → DivisionScan
  | s, [] => s
  | s, b :: bs => divisionScan divisor (divisionScanStep divisor s b) bs

-- Source: proofs/Lax51Proofs/RamToTM/FixedWord.lean:626-639.
theorem divisionScan_invariant {d : ℕ} (hd : 0 < d)
    (bits : List Bool) (s : DivisionScan) (hr : s.remainder < d) :
    let s' := divisionScan d s bits
    bitsValue s'.quotient * d + s'.remainder =
      msbValueFrom (bitsValue s.quotient * d + s.remainder) bits ∧
    s'.remainder < d := by
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
  | nil => simp [divisionScan, msbValueFrom, hr]
  | cons b bits ih =>
      obtain ⟨hstep, hr'⟩ := divisionScanStep_invariant hd s b hr
      obtain ⟨htail, hr''⟩ := ih (divisionScanStep d s b) hr'
      simp only [divisionScan, msbValueFrom]
      rw [hstep] at htail
      exact ⟨htail, hr''⟩

-- Source: proofs/Lax51Proofs/RamToTM/WordOperations.lean:82-91.
theorem divisionScan_quotient_length (d : ℕ) (s : DivisionScan)
    (bits : List Bool) :
    (divisionScan d s bits).quotient.length = s.quotient.length + bits.length := by
  induction bits generalizing s with
  | nil => simp [divisionScan]
  | cons b bits ih =>
      simp only [divisionScan]
      rw [ih]
      simp [divisionScanStep]
      omega

end Lax51Proofs.RamToTM
