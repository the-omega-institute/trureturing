/- GID: D5/S3/Factorization/FiniteTranslationStabilizer
   generality: G
   mirror-B: D5/B/S3/Factorization/FiniteTranslationStabilizer
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: A finite set's cardinality annihilates every translation stabilizer. -/

import Mathlib.Algebra.Group.Action.Pointwise.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.SetTheory.Cardinal.NatCard
import Mathlib.Tactic.Abel

namespace D5.S3.Factorization.FiniteTranslationStabilizer

open scoped Pointwise

/-- A translation fixing a finite subset of an additive group is annihilated
by the subset's cardinality. -/
theorem card_nsmul_eq_zero_of_vadd_finset_eq {G : Type*} [AddCommGroup G] [DecidableEq G]
    (s : Finset G) (t : G) (ht : t +ᵥ s = s) : s.card • t = 0 := by
  classical
  have hsum := congrArg (fun u : Finset G => ∑ p ∈ u, p) ht
  rw [Finset.vadd_finset_def, Finset.sum_image] at hsum
  · change (∑ p ∈ s, (t + p)) = ∑ p ∈ s, p at hsum
    rw [Finset.sum_add_distrib, Finset.sum_const] at hsum
    exact add_right_cancel (hsum.trans (zero_add _).symm)
  · intro p _ q _ h
    exact add_left_cancel h

/-- The order of the translation stabilizer divides the number of points in
the stabilized finite set. -/
theorem stabilizer_card_dvd_card {G : Type*} [AddCommGroup G] [DecidableEq G]
    [Finite G] (s : Finset G) :
    Nat.card (AddAction.stabilizer G s) ∣ s.card := by
  classical
  let H := AddAction.stabilizer G s
  let X := {p : G // p ∈ s}
  letI : AddAction H X := {
    vadd := fun h p => ⟨(h : G) + p.1, by
      have hh : (h : G) +ᵥ s = s := h.property
      have hp : (h : G) + p.1 ∈ (h : G) +ᵥ s :=
        Finset.mem_vadd_finset.mpr ⟨p.1, p.2, rfl⟩
      simpa only [hh] using hp⟩
    zero_vadd := fun p => Subtype.ext (by
      change (0 : G) + p.1 = p.1
      simp)
    add_vadd := fun h k p => Subtype.ext (by
      change ((h : G) + (k : G)) + p.1 = (h : G) + ((k : G) + p.1)
      exact add_assoc _ _ _)
  }
  have hfree (p : X) : AddAction.stabilizer H p = ⊥ := by
    rw [AddSubgroup.eq_bot_iff_forall]
    intro h hh
    apply Subtype.ext
    have heq : (h : G) + p.1 = p.1 := congrArg Subtype.val hh
    have h0 : (h : G) + p.1 = (0 : G) + p.1 := heq.trans (zero_add _).symm
    exact add_right_cancel h0
  have hcard := Nat.card_congr (AddAction.selfEquivOrbitsQuotientProd hfree)
  have hs : Nat.card X = s.card := by
    simp only [X, Nat.card_eq_fintype_card, Fintype.card_coe]
  rw [← hs, hcard, Nat.card_prod]
  exact dvd_mul_left _ _

/-- If the stabilizer has as many elements as the stabilized set, the set is
the stabilizer coset through any of its points. -/
theorem eq_stabilizer_coset_of_card_eq {G : Type*} [AddCommGroup G] [DecidableEq G]
    [Fintype G] (s : Finset G) (p : G) (hp : p ∈ s)
    (hcard : Nat.card (AddAction.stabilizer G s) = s.card) :
    s = Finset.univ.image (fun h : AddAction.stabilizer G s => (h : G) + p) := by
  classical
  let H := AddAction.stabilizer G s
  let f : H → G := fun h => (h : G) + p
  have hinj : Function.Injective f := by
    intro h k heq
    exact Subtype.ext (add_right_cancel heq)
  have hsubset : Finset.univ.image f ⊆ s := by
    intro x hx
    obtain ⟨h, _, rfl⟩ := Finset.mem_image.mp hx
    have hh : (h : G) +ᵥ s = s := h.property
    have hmem : f h ∈ (h : G) +ᵥ s :=
      Finset.mem_vadd_finset.mpr ⟨p, hp, rfl⟩
    simpa only [hh] using hmem
  have hsize : (Finset.univ.image f).card = s.card := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ]
    simpa only [H, Nat.card_eq_fintype_card] using hcard
  exact (Finset.eq_of_subset_of_card_le hsubset hsize.ge).symm

/-- A three-point set with a nonzero translation symmetry is a coset of its
three-element translation stabilizer. -/
theorem three_point_eq_stabilizer_coset {G : Type*} [AddCommGroup G] [DecidableEq G]
    [Fintype G] (s : Finset G) (hs : s.card = 3)
    (t : G) (ht : t +ᵥ s = s) (ht0 : t ≠ 0) (p : G) (hp : p ∈ s) :
    s = Finset.univ.image (fun h : AddAction.stabilizer G s => (h : G) + p) := by
  let H := AddAction.stabilizer G s
  have hdiv : Nat.card H ∣ 3 := by
    simpa only [H, hs] using stabilizer_card_dvd_card s
  have hne : Nat.card H ≠ 1 := by
    intro h
    have hsub : Subsingleton H :=
      (Finite.card_le_one_iff_subsingleton).mp (le_of_eq h)
    have hz : (⟨t, ht⟩ : H) = 0 := Subsingleton.elim _ _
    exact ht0 (congrArg Subtype.val hz)
  have hcard : Nat.card H = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hdiv with h | h
    · exact False.elim (hne h)
    · exact h
  exact eq_stabilizer_coset_of_card_eq s p hp (hcard.trans hs.symm)

/-- A nontrivial translation symmetry cycles through all three points. -/
theorem three_point_eq_translation_cycle {G : Type*} [AddCommGroup G] [DecidableEq G]
    (s : Finset G) (hs : s.card = 3) (t : G) (ht : t +ᵥ s = s)
    (ht0 : t ≠ 0) (p : G) (hp : p ∈ s) :
    s = {p, t + p, (2 : ℕ) • t + p} := by
  classical
  have h3 : 3 • t = 0 := by
    simpa only [hs] using card_nsmul_eq_zero_of_vadd_finset_eq s t ht
  have h2 : (2 : ℕ) • t ≠ 0 := by
    intro hz
    have heq : t = (3 : ℕ) • t - (2 : ℕ) • t := by
      simp only [succ_nsmul, one_nsmul]
      abel
    rw [h3, hz, sub_self] at heq
    exact ht0 heq
  have htp : t + p ∈ s := by
    have h : t + p ∈ t +ᵥ s :=
      Finset.mem_vadd_finset.mpr ⟨p, hp, rfl⟩
    simpa only [ht] using h
  have h2tp : (2 : ℕ) • t + p ∈ s := by
    have h : t + (t + p) ∈ t +ᵥ s :=
      Finset.mem_vadd_finset.mpr ⟨t + p, htp, rfl⟩
    have hh : t + (t + p) ∈ s := by simpa only [ht] using h
    convert hh using 1 <;> simp [two_nsmul, add_assoc]
  have hsubset : ({p, t + p, (2 : ℕ) • t + p} : Finset G) ⊆ s := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact hp
    · exact htp
    · exact h2tp
  have hpt : p ≠ t + p := by
    intro heq
    apply ht0
    exact add_right_cancel (by simpa only [zero_add] using heq.symm)
  have ht2 : t + p ≠ (2 : ℕ) • t + p := by
    intro heq
    apply ht0
    have h : t = (2 : ℕ) • t := add_right_cancel heq
    simpa [two_nsmul] using h
  have hp2 : p ≠ (2 : ℕ) • t + p := by
    intro heq
    exact h2 (add_right_cancel (by simpa only [zero_add] using heq.symm))
  have hcard : ({p, t + p, (2 : ℕ) • t + p} : Finset G).card = 3 := by
    simp [hpt, ht2, hp2]
  exact (Finset.eq_of_subset_of_card_le hsubset (hcard.trans hs.symm).ge).symm

#print axioms card_nsmul_eq_zero_of_vadd_finset_eq
#print axioms stabilizer_card_dvd_card
#print axioms eq_stabilizer_coset_of_card_eq
#print axioms three_point_eq_stabilizer_coset
#print axioms three_point_eq_translation_cycle

end D5.S3.Factorization.FiniteTranslationStabilizer
