/- GID: D5/S3/ObserverMemory/ContextUpdates/TwoSenderFeedbackClassification
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/ContextUpdates/TwoSenderFeedbackClassification
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Binary feedback and two simultaneous binary replies have a shared affine classification. -/

import D5.S3.ObserverMemory.ContextUpdates.ExactSnapshotCollisionClassification
import Mathlib.Data.Bool.Basic
import Mathlib.Tactic.FinCases

namespace D5.S3.ObserverMemory.ContextUpdates.TwoSenderFeedbackClassification

open scoped BigOperators
open D5.S3.ObserverMemory.ContextUpdates.ExactSnapshotPeriodClassification
open D5.S3.ObserverMemory.ContextUpdates.ExactSnapshotCollisionClassification

local notation "Z4" => ZMod 4
local notation "Z2" => ZMod 2
local notation "χ" => (ZMod.castHom (by decide : 2 ∣ 4) Z2).toAddMonoidHom
local notation "S" => Source (I := Fin 2) χ
local notation "PType" => Protocol Z4 (Fin 2) Bool (fun _ => Bool)
local notation "bit" b => (Bool.toNat b : Z4)

/-- Low and high bits of the standard representative. -/
def low (x : Z4) : Bool := x.val % 2 == 1

def high (x : Z4) : Bool := x.val / 2 == 1

/-- The original three-coordinate source and binary clock offset, in the generic source. -/
def sourceEquiv : (Z4 × Z4 × Z4 × Z2) ≃ S where
  toFun z := ((z.1, ![z.2.1, z.2.2.1]), ⟨2 * (z.2.2.2.val : Z4), by
    generalize z.2.2.2 = h
    fin_cases h <;> decide⟩)
  invFun s := (s.1.1, s.1.2 0, s.1.2 1, if (s.2 : Z4) = 0 then 0 else 1)
  left_inv := by
    rintro ⟨a, u, v, h⟩
    fin_cases h <;> simp
  right_inv := by
    rintro ⟨⟨a, x⟩, ⟨h, hh⟩⟩
    apply Prod.ext
    · apply Prod.ext rfl
      funext i
      fin_cases i <;> rfl
    · apply Subtype.ext
      fin_cases h
      · rfl
      · exact False.elim ((by decide : χ (1 : Z4) ≠ 0) hh)
      · rfl
      · exact False.elim ((by decide : χ (3 : Z4) ≠ 0) hh)

/-- Correctness for every original source; the query precedes both local replies. -/
def Correct (P : PType) (D : Z4 → Z4 → Bool → Bool → Bool → Z4) : Prop :=
  ∀ z : Z4 × Z4 × Z4 × Z2,
    let s := sourceEquiv z
    let t := clock s
    let b := P.query s.1.1 t
    D s.1.1 t b (P.reply 0 (s.1.2 0) t b) (P.reply 1 (s.1.2 1) t b) = target s

/-- Only values actually produced by a source constrain the decoder. -/
def Actual (P : PType) (a t : Z4) (b r s : Bool) : Prop :=
  ∃ z : S, z.1.1 = a ∧ clock z = t ∧ P.query a t = b ∧
    P.reply 0 (z.1.2 0) t b = r ∧ P.reply 1 (z.1.2 1) t b = s

/-- One common parameter family governs all query, reply, and actual decoder inputs. -/
def NormalForm (P : PType) (D : Z4 → Z4 → Bool → Bool → Bool → Z4)
    (c : Z4 → Bool) (A B c₂ c₃ : Z4 → Bool → Bool) : Prop :=
  (∀ a t, P.query a t = low (t - a) ^^ c t) ∧
  (∀ t p, A t p ^^ B t p = true ^^ p) ∧
  (∀ t b u, P.reply 0 u t b = high u ^^ (A t (b ^^ c t) && low u) ^^ c₂ t (b ^^ c t)) ∧
  (∀ t b v, P.reply 1 v t b = high v ^^ (B t (b ^^ c t) && low v) ^^ c₃ t (b ^^ c t)) ∧
  (∀ a t b r s, Actual P a t b r s →
    D a t b r s = a + bit (b ^^ c t) +
      2 * bit (r ^^ s ^^ c₂ t (b ^^ c t) ^^ c₃ t (b ^^ c t) ^^
        (B t (b ^^ c t) && (b ^^ c t))))

private theorem correct_generic (P : PType) (D : Z4 → Z4 → Bool → Bool → Bool → Z4)
    (hD : Correct P D) (s : S) :
    D s.1.1 (clock s) (P.query s.1.1 (clock s))
      (P.reply 0 (s.1.2 0) (clock s) (P.query s.1.1 (clock s)))
      (P.reply 1 (s.1.2 1) (clock s) (P.query s.1.1 (clock s))) = target s := by
  obtain ⟨z, rfl⟩ := sourceEquiv.surjective s
  exact hD z

private theorem low_characteristic (x y : Z4) : low x = low y ↔ χ x = χ y := by
  fin_cases x <;> fin_cases y <;> decide

private theorem low_bits (l h : Bool) : low (bit l + 2 * bit h) = l := by
  cases l <;> cases h <;> decide

private theorem high_bits (l h : Bool) : high (bit l + 2 * bit h) = h := by
  cases l <;> cases h <;> decide

private theorem bit_decomposition (x : Z4) : bit (low x) + 2 * bit (high x) = x := by
  fin_cases x <;> decide

private theorem affine_of_separated (e : Z4 → Bool)
    (he : ∀ x y, low x = low y → e x = e y → x = y) (x : Z4) :
    e x = high x ^^ ((e 0 ^^ e 1) && low x) ^^ e 0 := by
  have h02 : e 0 ≠ e 2 := fun h => (by decide : (0 : Z4) ≠ 2) (he 0 2 rfl h)
  have h13 : e 1 ≠ e 3 := fun h => (by decide : (1 : Z4) ≠ 3) (he 1 3 rfl h)
  fin_cases x <;> cases h0 : e 0 <;> cases h1 : e 1 <;>
    cases h2 : e 2 <;> cases h3 : e 3 <;> simp_all [low, high]

end D5.S3.ObserverMemory.ContextUpdates.TwoSenderFeedbackClassification
