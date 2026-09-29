/- GID: D5/S3/Factorization/PrimePowers/AffineGcdBehavior
   generality: G
   mirror-B: D5/B/S3/Factorization/PrimePowers/AffineGcdBehavior
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Positive mixed words retain an affine form with gcd-divisible translation. -/

import D5.S3.ObserverMemory.Prediction.ControlledBehaviorUniversality
import Mathlib.Data.PNat.Basic
import Mathlib.Data.Int.GCD
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.OrderOfElement

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Factorization.PrimePowers.AffineGcdBehavior

open D5.S3.ObserverMemory.Prediction.ControlledBehaviorUniversality (runWord)

/-- The common divisor of the target modulus and every permitted addend. -/
def libraryGcd (H : Nat) (A : List ℕ+) : Nat :=
  A.foldr (fun c d => Nat.gcd c d) H

/-- An input is either a positive multiplier or an indexed library addition. -/
abbrev Operation (A : List ℕ+) := Sum ℕ+ (Fin A.length)

/-- The exact action on a positive source. -/
def update (A : List ℕ+) : Operation A → ℕ+ → ℕ+
  | .inl m, x => m * x
  | .inr i, x => x + A.get i

/-- Every finite mixed word, including the empty word, has one integer-affine
action, and its translation is divisible by the gcd of all permitted addends. -/
theorem affine_word_translation (H : Nat) (A : List ℕ+)
    (w : List (Operation A)) :
    ∃ a t : Nat, 0 < a ∧ libraryGcd H A ∣ t ∧
      ∀ x : ℕ+, (runWord (update A) w x).val = a * (x : ℕ) + t := by
  have addend_divides : ∀ (B : List ℕ+) (c : ℕ+),
      c ∈ B → libraryGcd H B ∣ (c : ℕ) := by
    intro B
    induction B with
    | nil =>
        intro c hc
        simp at hc
    | cons b bs ih =>
        intro c hc
        simp only [List.mem_cons] at hc
        simp only [libraryGcd]
        rcases hc with rfl | hc
        · exact Nat.gcd_dvd_left _ _
        · exact (Nat.gcd_dvd_right _ _).trans (ih c hc)
  induction w with
  | nil =>
      refine ⟨1, 0, by omega, dvd_zero _, ?_⟩
      intro x
      simp [runWord]
  | cons op rest ih =>
      obtain ⟨a, t, ha, ht, hrun⟩ := ih
      cases op with
      | inl m =>
          refine ⟨a * (m : ℕ), t, Nat.mul_pos ha m.pos, ht, ?_⟩
          intro x
          simpa [runWord, update, mul_assoc] using hrun (m * x)
      | inr i =>
          have hc := addend_divides A (A.get i) (List.get_mem A i)
          have htrans : libraryGcd H A ∣ a * (A.get i : ℕ) + t := by
            obtain ⟨k, hk⟩ := hc
            obtain ⟨l, hl⟩ := ht
            refine ⟨a * k + l, ?_⟩
            rw [hk, hl]
            rw [Nat.mul_add]
            simp only [Nat.mul_assoc, Nat.mul_comm]
          refine ⟨a, a * (A.get i : ℕ) + t, ha, htrans, ?_⟩
          intro x
          simpa [runWord, update, mul_add, add_assoc] using hrun (x + A.get i)

#print axioms affine_word_translation

/-- Every affine action whose translation is divisible by the library gcd
has one actual word: a positive multiplication followed by original additions. -/
theorem affine_action_realization (H : Nat) (hH : 2 ≤ H) (A : List ℕ+)
    (a : ℕ+) (t : Nat) (ht : libraryGcd H A ∣ t) :
    ∃ ws : List (Fin A.length), ∀ x : ℕ+,
      (((runWord (update A) (Sum.inl a :: ws.map Sum.inr) x).val : Nat) : ZMod H) =
        (((a : Nat) * (x : Nat) + t : Nat) : ZMod H) := by
  haveI : NeZero H := ⟨by omega⟩
  let S : Set (ZMod H) := Set.range (fun i : Fin A.length => ((A.get i : ℕ) : ZMod H))
  let C : AddSubgroup (ZMod H) := AddSubgroup.closure S
  have gcd_mem (B : List ℕ+)
      (hB : ∀ c : ℕ+, c ∈ B → (((c : ℕ) : ZMod H) ∈ C)) :
      ((libraryGcd H B : Nat) : ZMod H) ∈ C := by
    induction B with
    | nil =>
        simp [libraryGcd]
    | cons c bs ih =>
        have hc : (((c : ℕ) : ZMod H) ∈ C) :=
          hB c (List.mem_cons_self ..)
        have htail : ((libraryGcd H bs : Nat) : ZMod H) ∈ C := by
          apply ih
          intro b hb
          exact hB b (List.mem_cons_of_mem _ hb)
        have hbez : (((Nat.gcd (c : Nat) (libraryGcd H bs) : Nat) : ZMod H)) =
            (((c : Nat) : ZMod H) * (Nat.gcdA (c : Nat) (libraryGcd H bs) : ZMod H)) +
            (((libraryGcd H bs : Nat) : ZMod H) *
              (Nat.gcdB (c : Nat) (libraryGcd H bs) : ZMod H)) := by
          simpa only [Int.cast_add, Int.cast_mul, Int.cast_natCast] using
            congrArg (fun z : Int => (z : ZMod H))
              (Nat.gcd_eq_gcd_ab (c : Nat) (libraryGcd H bs))
        have hleft : ((c : Nat) : ZMod H) *
            (Nat.gcdA (c : Nat) (libraryGcd H bs) : ZMod H) ∈ C := by
          simpa [zsmul_eq_mul, mul_comm] using
            C.zsmul_mem hc (Nat.gcdA (c : Nat) (libraryGcd H bs))
        have hright : ((libraryGcd H bs : Nat) : ZMod H) *
            (Nat.gcdB (c : Nat) (libraryGcd H bs) : ZMod H) ∈ C := by
          simpa [zsmul_eq_mul, mul_comm] using
            C.zsmul_mem htail (Nat.gcdB (c : Nat) (libraryGcd H bs))
        have hsum := C.add_mem hleft hright
        change (((Nat.gcd (c : Nat) (libraryGcd H bs) : Nat) : ZMod H)) ∈ C
        rw [hbez]
        exact hsum
  have hd : (((libraryGcd H A : Nat) : ZMod H) ∈ C) := by
    apply gcd_mem A
    intro c hc
    exact AddSubgroup.subset_closure ⟨⟨A.idxOf c, by simpa using List.idxOf_lt_length_of_mem hc⟩,
      by simp⟩
  obtain ⟨b, rfl⟩ := ht
  have htarget : (((libraryGcd H A * b : Nat) : ZMod H) ∈ C) := by
    simpa [nsmul_eq_mul, mul_comm] using C.nsmul_mem hd b
  have hmonoid : ((libraryGcd H A * b : Nat) : ZMod H) ∈
      AddSubmonoid.closure S := by
    rw [← AddSubgroup.closure_toAddSubmonoid_of_finite]
    exact htarget
  have hwords : ∀ z : ZMod H, z ∈ AddSubmonoid.closure S →
      ∃ ws : List (Fin A.length),
        (ws.map fun i => ((A.get i : ℕ) : ZMod H)).sum = z := by
    intro z hz
    induction hz using AddSubmonoid.closure_induction with
    | mem z hz =>
        obtain ⟨i, rfl⟩ := hz
        exact ⟨[i], by simp⟩
    | zero => exact ⟨[], by simp⟩
    | add u v _ _ hu hv =>
        obtain ⟨wu, hwu⟩ := hu
        obtain ⟨wv, hwv⟩ := hv
        refine ⟨wu ++ wv, ?_⟩
        simp only [List.map_append, List.sum_append]
        rw [hwu, hwv]
  obtain ⟨ws, hws⟩ := hwords _ hmonoid
  refine ⟨ws, ?_⟩
  intro x
  have hrun (us : List (Fin A.length)) (y : ℕ+) :
      (((runWord (update A) (us.map Sum.inr) y).val : Nat) : ZMod H) =
        ((y : Nat) : ZMod H) +
          (us.map fun i => ((A.get i : ℕ) : ZMod H)).sum := by
    induction us generalizing y with
    | nil => simp [runWord]
    | cons i is ih =>
        simpa [runWord, update, add_assoc] using ih (y + A.get i)
  have haction := hrun ws (a * x)
  rw [hws] at haction
  simpa only [runWord, update, PNat.mul_coe, Nat.cast_add, Nat.cast_mul] using haction

#print axioms affine_action_realization

end D5.S3.Factorization.PrimePowers.AffineGcdBehavior
