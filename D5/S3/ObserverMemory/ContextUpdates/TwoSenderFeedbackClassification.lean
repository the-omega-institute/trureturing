/- GID: D5/S3/ObserverMemory/ContextUpdates/TwoSenderFeedbackClassification
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/ContextUpdates/TwoSenderFeedbackClassification
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Two binary senders share affine parameters determined by feedback. -/

import D5.S3.ObserverMemory.ContextUpdates.ExactSnapshotCollisionClassification
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases

namespace D5.S3.ObserverMemory.ContextUpdates.TwoSenderFeedbackClassification

open scoped BigOperators
open D5.S3.ObserverMemory.ContextUpdates.ExactSnapshotPeriodClassification
open D5.S3.ObserverMemory.ContextUpdates.ExactSnapshotCollisionClassification

local notation "Z4" => ZMod 4
local notation "Z2" => ZMod 2
local notation "χ" => RingHom.toAddMonoidHom (ZMod.castHom (by decide : 2 ∣ 4) Z2)
local notation "S" => Source (I := Fin 2) χ
local notation "PType" => Protocol Z4 (Fin 2) Bool (fun _ => Bool)
local notation:max "bit" b:max => (Bool.toNat b : Z4)

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
    fin_cases h <;> rfl
  right_inv := by
    rintro ⟨⟨a, x⟩, ⟨h, hh⟩⟩
    dsimp only
    apply Prod.ext
    · change (a, ![x 0, x 1]) = (a, x)
      apply Prod.ext
      · rfl
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
  (∀ a t, P.query a t = (low (t - a) ^^ c t)) ∧
  (∀ t p, (A t p ^^ B t p) = (true ^^ p)) ∧
  (∀ t b u, P.reply 0 u t b = (high u ^^ (A t (b ^^ c t) && low u) ^^ c₂ t (b ^^ c t))) ∧
  (∀ t b v, P.reply 1 v t b = (high v ^^ (B t (b ^^ c t) && low v) ^^ c₃ t (b ^^ c t))) ∧
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
  fin_cases x <;> rfl

private theorem affine_of_separated (e : Z4 → Bool)
    (he : ∀ x y, low x = low y → e x = e y → x = y) (x : Z4) :
    e x = (high x ^^ ((e 0 ^^ e 1) && low x) ^^ e 0) := by
  have hi (l : Bool) : Function.Injective (fun h : Bool => e (bit l + 2 * bit h)) := by
    intro U V huv
    have hx := he _ _ (by rw [low_bits, low_bits]) huv
    simpa only [high_bits] using congrArg high hx
  have h02 : e 0 ≠ e 2 := Bool.injective_iff.mp (hi false)
  have h13 : e 1 ≠ e 3 := Bool.injective_iff.mp (hi true)
  have h2 := Bool.eq_not_of_ne (Ne.symm h02)
  have h3 := Bool.eq_not_of_ne (Ne.symm h13)
  have hx : x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 := by
    fin_cases x
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr rfl))
  rcases hx with rfl | rfl | rfl | rfl <;>
    simp only [show low 0 = false from rfl, show high 0 = false from rfl,
      show low 1 = true from rfl, show low 2 = false from rfl,
      show low 3 = true from rfl, show high 1 = false from rfl,
      show high 2 = true from rfl, show high 3 = true from rfl, h2, h3] <;>
    cases e 0 <;> cases e 1 <;> decide

private theorem realize (a t u v : Z4) (hp : low (u + v) = low (t - a)) :
    ∃ z : S, z.1.1 = a ∧ clock z = t ∧ z.1.2 0 = u ∧ z.1.2 1 = v := by
  have hχ : χ (t - a - (u + v)) = 0 := by
    rw [map_sub, (low_characteristic (u + v) (t - a)).mp hp, sub_self]
  let z : S := ((a, ![u, v]), ⟨t - a - (u + v), hχ⟩)
  refine ⟨z, rfl, ?_, rfl, rfl⟩
  simp [z, clock, target, Fin.sum_univ_two]

private theorem reachable (P : PType) (a t : Z4) : Reachable P χ a t (P.query a t) := by
  obtain ⟨z, ha, ht, _, _⟩ := realize a t (t - a) 0 (by simp)
  exact ⟨z, ha, ht, rfl⟩

private theorem separated (P : PType) (D : Z4 → Z4 → Bool → Bool → Bool → Z4)
    (hD : Correct P D) (a t : Z4) :
    FiberSeparated χ (fun i x => P.reply i x t (P.query a t)) := by
  let decode : (Z4 × Z4 × (Fin 2 → Bool)) → Z4 :=
    fun o => D o.1 o.2.1 (P.query o.1 o.2.1) (o.2.2 0) (o.2.2 1)
  have hd : ∀ z : S, decode (observe P z) = target z := correct_generic P D hD
  apply fiber_separated_of_branch_exact χ _ (χ (t - a))
    (branch_exact_of_decoder P χ decode hd a t (P.query a t) (reachable P a t))
  intro i x
  fin_cases i
  · refine ⟨![x, t - a - x], ?_, rfl⟩
    simp [Fin.sum_univ_two]
  · refine ⟨![t - a - x, x], ?_, rfl⟩
    simp [Fin.sum_univ_two]

private theorem branch_affine (P : PType) (D : Z4 → Z4 → Bool → Bool → Bool → Z4)
    (hD : Correct P D) (a t : Z4) (i : Fin 2) (x : Z4) :
    P.reply i x t (P.query a t) = (high x ^^
      ((P.reply i 0 t (P.query a t) ^^ P.reply i 1 t (P.query a t)) && low x) ^^
      P.reply i 0 t (P.query a t)) := by
  apply affine_of_separated (fun x => P.reply i x t (P.query a t))
  intro x y hxy hreply
  exact separated P D hD a t i x y ((low_characteristic x y).mp hxy) hreply

private theorem pair_parity (p A B c₂ c₃ r s l : Bool) :
    low ((bit l + 2 * bit (r ^^ c₂ ^^ (A && l))) +
      (bit (l ^^ p) + 2 * bit (s ^^ c₃ ^^ (B && (l ^^ p))))) = p := by
  cases p <;> cases A <;> cases B <;> cases c₂ <;> cases c₃ <;>
    cases r <;> cases s <;> cases l <;> decide

private theorem pair_sum (p A B c₂ c₃ r s l : Bool) :
    (bit l + 2 * bit (r ^^ c₂ ^^ (A && l))) +
      (bit (l ^^ p) + 2 * bit (s ^^ c₃ ^^ (B && (l ^^ p)))) =
    bit p + 2 * bit (r ^^ s ^^ c₂ ^^ c₃ ^^ (B && p) ^^
      ((A ^^ B ^^ true ^^ p) && l)) := by
  cases p <;> cases A <;> cases B <;> cases c₂ <;> cases c₃ <;>
    cases r <;> cases s <;> cases l <;> decide

private theorem affine_inverse (A c r l : Bool) :
    (high (bit l + 2 * bit (r ^^ c ^^ (A && l))) ^^
      (A && low (bit l + 2 * bit (r ^^ c ^^ (A && l)))) ^^ c) = r := by
  rw [low_bits, high_bits]
  cases A <;> cases c <;> cases r <;> cases l <;> decide

private theorem branch_data (P : PType) (D : Z4 → Z4 → Bool → Bool → Bool → Z4)
    (hD : Correct P D) (a t : Z4) :
    let b := P.query a t
    let p := low (t - a)
    let A := P.reply 0 0 t b ^^ P.reply 0 1 t b
    let B := P.reply 1 0 t b ^^ P.reply 1 1 t b
    let c₂ := P.reply 0 0 t b
    let c₃ := P.reply 1 0 t b
    (A ^^ B) = (true ^^ p) ∧
      ∀ r s, Actual P a t b r s ∧
        D a t b r s = a + bit p + 2 * bit (r ^^ s ^^ c₂ ^^ c₃ ^^ (B && p)) := by
  dsimp only
  let b := P.query a t
  let p := low (t - a)
  let A := P.reply 0 0 t b ^^ P.reply 0 1 t b
  let B := P.reply 1 0 t b ^^ P.reply 1 1 t b
  let c₂ := P.reply 0 0 t b
  let c₃ := P.reply 1 0 t b
  have two_realizations (r s l : Bool) : Actual P a t b r s ∧
      D a t b r s = a + bit p + 2 * bit (r ^^ s ^^ c₂ ^^ c₃ ^^ (B && p) ^^
        ((A ^^ B ^^ true ^^ p) && l)) := by
    let u : Z4 := bit l + 2 * bit (r ^^ c₂ ^^ (A && l))
    let v : Z4 := bit (l ^^ p) + 2 * bit (s ^^ c₃ ^^ (B && (l ^^ p)))
    obtain ⟨z, ha, ht, hu, hv⟩ := realize a t u v (pair_parity p A B c₂ c₃ r s l)
    have hr : P.reply 0 u t b = r :=
      (branch_affine P D hD a t 0 u).trans (affine_inverse A c₂ r l)
    have hs : P.reply 1 v t b = s :=
      (branch_affine P D hD a t 1 v).trans (affine_inverse B c₃ s (l ^^ p))
    refine ⟨⟨z, ha, ht, rfl, by rw [hu, hr], by rw [hv, hs]⟩, ?_⟩
    calc
      D a t b r s = target z := by
        have hz := correct_generic P D hD z
        rw [ha, ht, hu, hv] at hz
        change D a t b (P.reply 0 u t b) (P.reply 1 v t b) = target z at hz
        rwa [hr, hs] at hz
      _ = a + (u + v) := by simp [target, Fin.sum_univ_two, ha, hu, hv, add_assoc]
      _ = a + bit p + 2 * bit (r ^^ s ^^ c₂ ^^ c₃ ^^ (B && p) ^^
          ((A ^^ B ^^ true ^^ p) && l)) := by
        rw [show u + v = _ from pair_sum p A B c₂ c₃ r s l]
        rw [add_assoc]
  have hzero := (two_realizations false false false).2
  have hone := (two_realizations false false true).2
  have hc : (A ^^ B) = (true ^^ p) := by
    have heq := hzero.symm.trans hone
    have heq' := add_left_cancel heq
    cases hA : A <;> cases hB : B <;> cases hp : p <;>
      cases h₂ : c₂ <;> cases h₃ : c₃ <;> simp_all +decide
  refine ⟨hc, ?_⟩
  intro r s
  have h := two_realizations r s false
  simpa using h

end D5.S3.ObserverMemory.ContextUpdates.TwoSenderFeedbackClassification
