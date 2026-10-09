/- GID: D5/S3/Combinatorics/ErdosUlam/SublatticeDefs
   generality: G
   mirror-B: D5/B/S3/Combinatorics/ErdosUlam/SublatticeDefs
   mirror-E: none(waiver:definitions-and-bridges)
   anchors: [mathlib/module/Mathlib.Data.Nat.Bitwise]
   utility: none
   digest: Finite Boolean sublattices, prefix chains, and their bitmask representation. -/

import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.List.FinRange
import Mathlib.Tactic.Ext

import Mathlib.Tactic

namespace D5.S3.Combinatorics.ErdosUlam.SublatticeDefs

open Finset

/-- Sublattices are nonempty and closed under both lattice operations. -/
def IsSublattice {n : ℕ} (L : Finset (Finset (Fin n))) : Prop :=
  L.Nonempty ∧ ∀ A ∈ L, ∀ B ∈ L, A ∪ B ∈ L ∧ A ∩ B ∈ L

/-- A family is monochromatic when the colouring is constant on it. -/
def Monochromatic {n : ℕ} (χ : Finset (Fin n) → Bool)
    (L : Finset (Finset (Fin n))) : Prop := ∃ b, ∀ A ∈ L, χ A = b

def initialSegment (n r : ℕ) : Finset (Fin n) := univ.filter (fun i => i.val < r)

theorem prefix_subset {n r s : ℕ} (h : r ≤ s) : initialSegment n r ⊆ initialSegment n s := by
  intro i hi
  simp only [initialSegment, mem_filter, mem_univ, true_and] at hi ⊢
  omega

theorem prefix_card (n r : ℕ) (h : r ≤ n) : (initialSegment n r).card = r := by
  have he : (initialSegment n r).card = (univ : Finset (Fin r)).card := by
    apply card_bij (fun i hi => (⟨i.val, by simpa [initialSegment] using hi⟩ : Fin r))
    · intro i hi; simp
    · intro i hi j hj hij; exact Fin.ext (congrArg (fun x : Fin r => x.val) hij)
    · intro j hj
      exact ⟨⟨j.val, lt_of_lt_of_le j.isLt h⟩, by simp [initialSegment, j.isLt], rfl⟩
  simpa using he

def decode (n m : ℕ) : Finset (Fin n) := univ.filter (fun i => m.testBit i.val)

theorem decode_union (n a b : ℕ) : decode n (a ||| b) = decode n a ∪ decode n b := by
  ext i
  simp [decode]

theorem decode_inter (n a b : ℕ) : decode n (a &&& b) = decode n a ∩ decode n b := by
  ext i
  simp [decode]

theorem decode_injective (n : ℕ) : Function.Injective (fun m : Fin (2 ^ n) => decode n m) := by
  intro a b hab
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < n
  · have h := Finset.ext_iff.mp hab ⟨i, hi⟩
    have h' : (a.val.testBit i = true) ↔ (b.val.testBit i = true) := by
      simpa only [decode, mem_filter, mem_univ, true_and] using h
    exact Bool.eq_iff_iff.mpr h'
  · have hpow : 2 ^ n ≤ 2 ^ i := Nat.pow_le_pow_right (by decide) (by omega)
    rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le a.isLt hpow),
      Nat.testBit_eq_false_of_lt (lt_of_lt_of_le b.isLt hpow)]

theorem decode_surjective (n : ℕ) : Function.Surjective (fun m : Fin (2 ^ n) => decode n m) :=
  ((Fintype.bijective_iff_injective_and_card _).2
    ⟨decode_injective n, by simp⟩).2

def weight (n m : ℕ) : ℕ := (List.finRange n).countP (fun i => m.testBit i.val)

theorem decode_card (n m : ℕ) : (decode n m).card = weight n m := by
  have hu : (List.finRange n).toFinset = (univ : Finset (Fin n)) := by ext; simp
  rw [decode, ← hu]
  simpa [weight] using (List.nodup_finRange n).card_eq_countP (P := fun i => m.testBit i.val = true)

def FamilyClosed (l : List ℕ) : Prop :=
  ∀ a ∈ l, ∀ b ∈ l, a ||| b ∈ l ∧ a &&& b ∈ l

theorem family_sublattice (n : ℕ) {l : List ℕ} (hn : l ≠ []) (hc : FamilyClosed l) :
    IsSublattice (l.toFinset.image (decode n)) := by
  constructor
  · rcases List.exists_mem_of_ne_nil _ hn with ⟨a, ha⟩
    exact ⟨decode n a, mem_image.mpr ⟨a, by simpa using ha, rfl⟩⟩
  · intro A hA B hB
    obtain ⟨a, ha, rfl⟩ := mem_image.mp hA
    obtain ⟨b, hb, rfl⟩ := mem_image.mp hB
    obtain ⟨hu, hi⟩ := hc a (by simpa using ha) b (by simpa using hb)
    constructor
    · rw [← decode_union]; exact mem_image.mpr ⟨_, by simpa using hu, rfl⟩
    · rw [← decode_inter]; exact mem_image.mpr ⟨_, by simpa using hi, rfl⟩

theorem family_card (n : ℕ) {l : List ℕ} (hn : l.Nodup)
    (hb : ∀ m ∈ l, m < 2 ^ n) : (l.toFinset.image (decode n)).card = l.length := by
  rw [card_image_iff.mpr, List.toFinset_card_of_nodup hn]
  intro a ha b hb' he
  have h := decode_injective n (a₁ := ⟨a, hb a (by simpa using ha)⟩)
    (a₂ := ⟨b, hb b (by simpa using hb')⟩) he
  exact congrArg Fin.val h


end D5.S3.Combinatorics.ErdosUlam.SublatticeDefs
