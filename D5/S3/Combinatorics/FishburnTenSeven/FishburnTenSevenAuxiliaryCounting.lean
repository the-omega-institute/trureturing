/- GID: D5/S3/Combinatorics/FishburnTenSeven/FishburnTenSevenAuxiliaryCounting
   generality: G
   mirror-B: D5/B/S3/Combinatorics/FishburnTenSeven/FishburnTenSevenAuxiliaryCounting
   mirror-E: none(waiver:auxiliary-class-cardinalities)
   anchors: [mathlib/module/Mathlib.Data.List.Permutation]
   utility: none
   digest: Maximum decomposition counts the auxiliary class and its initial-one subclass. -/

import D5.S3.Combinatorics.FishburnTenSeven.FishburnTenSevenAuxiliary
import Mathlib.Data.List.Permutation

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.FishburnTenSeven.FishburnTenSevenAuxiliaryCounting

open D5.S3.Combinatorics Nonnesting Fishburn.FishburnDefs
open FishburnTenSevenAuxiliary

def HStart (size : ℕ) := {p : H size // p.val.head? = some 1}

theorem H_card (size : ℕ) : Nat.card (H size) = if size = 0 then 1 else 2 ^ (size - 1) := by
  classical
  have hfinite (total : ℕ) :
      ({p : List ℕ | p.Perm (List.range' 1 total) ∧ IsFishburn p ∧
        ¬ NonnestingDefs.Occurs [2, 1, 3] p} : Set (List ℕ)).Finite := by
    apply (List.finite_toSet (List.range' 1 total).permutations).subset
    intro p hp
    exact List.mem_permutations.mpr hp.1
  let (total : ℕ) : Finite (H total) := (hfinite total).to_subtype
  have hzero : Nat.card (H 0) = 1 := by
    apply Nat.card_eq_one_iff_exists.mpr
    let hempty : H 0 := by
      refine ⟨[], by simp, ?_, ?_⟩
      · intro before later hgap hlater
        simp at hlater
      · rintro ⟨values, _, _, hsub, _⟩
        have := hsub.length_le
        simp at this
    refine ⟨hempty, ?_⟩
    intro p
    apply Subtype.ext
    have hl := p.property.1.length_eq
    simpa [hempty] using List.length_eq_zero_iff.mp hl
  have hone : Nat.card (H 1) = 1 := by
    rw [Nat.card_congr (H_maximum_equiv 1 (by omega)), Nat.card_sigma]
    simp [hzero]
  have hdouble (total : ℕ) (ht : 1 ≤ total) :
      Nat.card (H (total + 1)) = Nat.card (H total) + Nat.card (H total) := by
    rw [Nat.card_congr (H_maximum_equiv (total + 1) (by omega)), Nat.card_sigma,
      Fin.sum_univ_succ]
    simp only [Fin.val_zero, Nat.sub_zero, Nat.add_sub_cancel, Fin.val_succ]
    congr 1
    rw [Nat.card_congr (H_maximum_equiv total ht), Nat.card_sigma]
    apply Finset.sum_congr rfl
    intro cut _
    have hs : total + 1 - (cut.val + 1) - 1 = total - cut.val - 1 := by omega
    rw [hs]
  induction size with
  | zero => simpa using hzero
  | succ size ih =>
      by_cases hz : size = 0
      · subst size
        simpa using hone
      · rw [hdouble size (by omega), ih]
        simp only [hz, ↓reduceIte, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false,
          Nat.add_sub_cancel]
        have hexponent : size = size - 1 + 1 := by omega
        conv_rhs => rw [hexponent, pow_succ]
        omega

theorem H_start_one_card (size : ℕ) (hsize : 1 ≤ size) :
    Nat.card (HStart size) = if size = 1 then 1 else 2 ^ (size - 2) := by
  classical
  have hinitial (total : ℕ) (ht : 1 ≤ total) (p : HStart (total + 1)) :
      ∃ q : H total, p.val.val = 1 :: q.val.map (· + 1) := by
    obtain ⟨q, hq | hq⟩ := (H_head_decomposition total p.val.val).mp p.val.property
    · have hhead := p.property
      rw [hq] at hhead
      simp only [List.head?_cons, Option.some.injEq] at hhead
      omega
    · exact ⟨q, hq⟩
  have hencode (total : ℕ) (ht : 1 ≤ total) : HStart (total + 1) ≃ H total := by
    let encode (p : HStart (total + 1)) : H total := Classical.choose (hinitial total ht p)
    have he (p : HStart (total + 1)) : p.val.val = 1 :: (encode p).val.map (· + 1) :=
      Classical.choose_spec (hinitial total ht p)
    let decode (q : H total) : HStart (total + 1) :=
      ⟨⟨1 :: q.val.map (· + 1), (H_head_decomposition total _).mpr ⟨q, Or.inr rfl⟩⟩,
        rfl⟩
    refine
      { toFun := encode
        invFun := decode
        left_inv := ?_
        right_inv := ?_ }
    · intro p
      apply Subtype.ext
      exact Subtype.ext (he p).symm
    · intro q
      apply Subtype.ext
      have hmap := (List.cons.inj (he (decode q))).2
      exact ((List.map_inj_right (fun first second he => Nat.add_right_cancel he)).mp
        hmap).symm
  by_cases hone : size = 1
  · subst size
    simp only [↓reduceIte]
    apply Nat.card_eq_one_iff_exists.mpr
    let hempty : H 0 := by
      refine ⟨[], by simp, ?_, ?_⟩
      · intro before later hgap hlater
        simp at hlater
      · rintro ⟨values, _, _, hsub, _⟩
        have := hsub.length_le
        simp at this
    let one : HStart 1 :=
      ⟨⟨[1], (H_head_decomposition 0 [1]).mpr ⟨hempty, Or.inl (by simp [hempty])⟩⟩,
        rfl⟩
    refine ⟨one, ?_⟩
    intro p
    apply Subtype.ext
    apply Subtype.ext
    have hp := p.val.property.1
    have hl : p.val.val.length = 1 := by simpa using hp.length_eq
    obtain ⟨value, he⟩ := List.length_eq_one_iff.mp hl
    have hh := p.property
    rw [he] at hh
    simp only [List.head?_cons, Option.some.injEq] at hh
    change p.val.val = [1]
    rw [he, hh]
  · obtain ⟨total, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : size ≠ 0)
    rw [Nat.card_congr (hencode total (by omega)), H_card]
    simp only [show total ≠ 0 by omega, hone, ↓reduceIte]
    congr 1

end D5.S3.Combinatorics.FishburnTenSeven.FishburnTenSevenAuxiliaryCounting
