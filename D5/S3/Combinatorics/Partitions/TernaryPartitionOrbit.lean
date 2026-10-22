/- GID: D5/S3/Combinatorics/Partitions/TernaryPartitionOrbit
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Partitions/TernaryPartitionOrbit
   mirror-E: none(waiver:structural-counting-foundation)
   anchors: []
   utility: none
   digest: Nonconstant ternary colourings with the same equality partition differ by a unique affine permutation. -/

import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Partitions.TernaryPartitionOrbit

/-!
Admission pre-registration (before the first Lean probe):
  question_answered: Do nonzero ternary modes modulo sign have exactly the same
    information as their anchored equality partitions, for arbitrary index types?
  dominating_theorem_search: not-found-in-searched-scope; repository ternary-mode
    and partition sources and pinned Mathlib ZMod/affine/equivalence sources.
  admission_basis: escape-witness.
  third_value: proof_shape: bind-only; consumer: affine_orbit_classification.
  affine_orbit_classification: proof_shape: content; escape_witness: constructing
    the affine slope from two unequal colours determines every other coordinate,
    including the third-colour case; consumer: anchored_samePartition.
  anchored_samePartition: proof_shape: content (after helper expansion);
    consumer: result.
  result: proof_shape: content (after helper expansion); escape_witness:
    affine_orbit_classification on the live proof path through anchored_samePartition.
  direct_frozen_dependencies: none (Mathlib only).
  utility-none: This is an arbitrary-index structural classification, not a finite
    instance, enumeration, checker or numerical reduction. The three-element
    field arithmetic is a consumed normalization helper, not the delivered result.
-/

/-- Equality of the partitions of the index type induced by two colourings. -/
def SamePartition {α : Type*} (u v : α → ZMod 3) : Prop :=
  ∀ i j, u i = u j ↔ v i = v j

private lemma third_value (r s t : ZMod 3) (hrs : r ≠ s) (hrt : r ≠ t)
    (hst : s ≠ t) : t = -r - s := by
  revert r s t
  decide

/-- Over the three-element field, an equality partition determines each nonconstant
colouring up to one unique affine permutation. The index type need not be finite. -/
private theorem affine_orbit_classification {α : Type*} (u v : α → ZMod 3)
    (hu : ∃ i j, u i ≠ u j) :
    SamePartition u v ↔ ∃! p : ZMod 3 × ZMod 3,
      p.1 ≠ 0 ∧ ∀ i, v i = p.1 * u i + p.2 := by
  constructor
  · intro h
    obtain ⟨i, j, hij⟩ := hu
    have hvij : v i ≠ v j := fun he => hij ((h i j).mpr he)
    let a : ZMod 3 := (v j - v i) / (u j - u i)
    let b : ZMod 3 := v i - a * u i
    have hden : u j - u i ≠ 0 := sub_ne_zero.mpr hij.symm
    have ha : a ≠ 0 := div_ne_zero (sub_ne_zero.mpr hvij.symm) hden
    have hai : v i = a * u i + b := by dsimp [b]; ring
    have haj : v j = a * u j + b := by
      have hm : a * (u j - u i) = v j - v i := div_mul_cancel₀ _ hden
      calc
        v j = (v j - v i) + v i := (sub_add_cancel _ _).symm
        _ = a * (u j - u i) + v i := by rw [hm]
        _ = a * u j + b := by dsimp only [b]; ring
    have hall (k : α) : v k = a * u k + b := by
      by_cases hki : u k = u i
      · rw [(h k i).mp hki, hki]
        exact hai
      by_cases hkj : u k = u j
      · rw [(h k j).mp hkj, hkj]
        exact haj
      have hu3 := third_value (u i) (u j) (u k) hij (Ne.symm hki) (Ne.symm hkj)
      have hv3 := third_value (v i) (v j) (v k) hvij
        (fun he => hki ((h k i).mpr he.symm))
        (fun he => hkj ((h k j).mpr he.symm))
      rw [hu3, hv3, hai, haj]
      calc
        -(a * u i + b) - (a * u j + b) =
            a * (-u i - u j) + b - (3 : ZMod 3) * b := by ring
        _ = a * (-u i - u j) + b := by
          have h3 : (3 : ZMod 3) = 0 := by decide
          rw [h3, zero_mul, sub_zero]
    refine ⟨(a, b), ⟨ha, hall⟩, ?_⟩
    intro p hp
    have hpa : p.1 = a := by
      apply (mul_left_inj' hden).mp
      calc
        p.1 * (u j - u i) = v j - v i := by
          rw [hp.2 i, hp.2 j]
          ring
        _ = a * (u j - u i) := by rw [hai, haj]; ring
    have hpb : p.2 = b := by
      have hi := hp.2 i
      rw [hpa, hai] at hi
      exact add_left_cancel hi.symm
    exact Prod.ext hpa hpb
  · rintro ⟨p, hp, _⟩ i j
    change u i = u j ↔ v i = v j
    rw [hp.2 i, hp.2 j]
    constructor
    · intro h
      rw [h]
    · intro h
      exact (mul_right_inj' hp.1).mp (add_right_cancel h)

/-- Fixing one extra label at zero removes the affine translation freedom. -/
def anchored {α : Type*} (u : α → ZMod 3) : Option α → ZMod 3 :=
  fun x => x.elim 0 u

private theorem anchored_samePartition {α : Type*} (u v : α → ZMod 3)
    (hu : u ≠ 0) :
    SamePartition (anchored u) (anchored v) ↔ v = u ∨ v = -u := by
  have hn : ∃ i j, anchored u i ≠ anchored u j := by
    obtain ⟨i, hi⟩ : ∃ i, u i ≠ 0 := Function.ne_iff.mp hu
    exact ⟨some i, none, hi⟩
  constructor
  · intro h
    obtain ⟨p, hp, _⟩ := (affine_orbit_classification (anchored u) (anchored v) hn).mp h
    have hb : p.2 = 0 := by simpa [anchored] using (hp.2 none).symm
    have ha : p.1 = 1 ∨ p.1 = -1 := by
      have h : ∀ a : ZMod 3, a ≠ 0 → a = 1 ∨ a = -1 := by decide
      exact h p.1 hp.1
    rcases ha with ha | ha
    · left
      funext i
      simpa [anchored, hb, ha] using hp.2 (some i)
    · right
      funext i
      simpa [anchored, hb, ha] using hp.2 (some i)
  · rintro (rfl | rfl)
    · exact fun _ _ => Iff.rfl
    · intro i j
      cases i <;> cases j <;> simp [anchored, eq_comm]

/-- Any selection of one member of each nonzero opposite-mode pair is also a
selection of exactly one colouring for every partition induced by a nonzero
anchored ternary colouring (a nontrivial partition with at most three blocks).
This is the structural reason that the thirteen four-party modes have no duplicate
partition patterns; it applies to arbitrary index types and arbitrary representative sets. -/
theorem result {α : Type*} (P : Set (α → ZMod 3))
    (hP : ∀ u : α → ZMod 3, u ≠ 0 → (u ∈ P ↔ -u ∉ P))
    (u : α → ZMod 3) (hu : u ≠ 0) :
    ∃! v : α → ZMod 3, v ∈ P ∧ SamePartition (anchored u) (anchored v) := by
  by_cases hup : u ∈ P
  · refine ⟨u, ⟨hup, fun _ _ => Iff.rfl⟩, ?_⟩
    intro v hv
    rcases (anchored_samePartition u v hu).mp hv.2 with h | h
    · exact h
    · subst v
      exact False.elim ((hP u hu).mp hup hv.1)
  · have hnu : -u ∈ P := by
      by_contra hn
      exact hup ((hP u hu).mpr hn)
    refine ⟨-u, ⟨hnu, ?_⟩, ?_⟩
    · exact (anchored_samePartition u (-u) hu).mpr (Or.inr rfl)
    · intro v hv
      rcases (anchored_samePartition u v hu).mp hv.2 with h | h
      · subst v
        exact False.elim (hup hv.1)
      · exact h

end D5.S3.Combinatorics.Partitions.TernaryPartitionOrbit
