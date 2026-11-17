/- GID: D5/S3/FiniteGroups/SubsetProducts/BinaryCodePerfectRestrictedBasis
   generality: I
   mirror-B: D5/B/S3/FiniteGroups/SubsetProducts/BinaryCodePerfectRestrictedBasis
   mirror-E: none(waiver:binary-code-quotient-bridge)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/FiniteGroups/SubsetProducts/BajnokGolayRestrictedBasisRefutation.result; instance=D5/S3/FiniteGroups/SubsetProducts/BajnokGolayRestrictedBasisRefutation.golay_perfect_restricted_basis; premises=D5/S3/FiniteGroups/SubsetProducts/BinaryCodePerfectRestrictedBasis.basis_of_minimum_weight
   digest: Minimum-distance binary codes give unique bounded subset sums in their quotient groups. -/


/-
proof_shape: F2, weight, word, subsets: definition;
  admission_basis: open-problem-resolution (#30733; Refuted).
proof_shape: mem_subsets, word_injective, sum_single_word, weight_sub_le: bind-only;
  escape_witness: none; consumer: basis_of_minimum_weight.
proof_shape: card_subsets: bind-only; escape_witness: none;
  consumer: BajnokGolayRestrictedBasisRefutation.golay_perfect_restricted_basis.
proof_shape: basis_of_minimum_weight: content;
  escape_witness: minimum-distance injectivity and full subset-preimage transfer;
  consumer: BajnokGolayRestrictedBasisRefutation.golay_perfect_restricted_basis.
Direct frozen dependency: D5/S3/FiniteGroups/BajnokBersonJustPerfectRestrictedBasis.IsPerfectRestrictedBasis;
  statement_id sha256:d6d92226693d885c5361c46cd097699517cff4764304c09b541f5eb4da8c95a8.
Four-slot audits for the two public theorems are unfinished: #30740,
https://github.com/the-omega-institute/trureturing/issues/30740.
-/

import D5.S3.FiniteGroups.BajnokBersonJustPerfectRestrictedBasis
import Mathlib.Data.Finset.Powerset
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Algebra.BigOperators.Pi

noncomputable section

namespace D5.S3.FiniteGroups.SubsetProducts.BinaryCodePerfectRestrictedBasis

open Finset
open BajnokBersonJustPerfectRestrictedBasis

attribute [local instance] Classical.propDecidable

abbrev F2 := ZMod 2

def weight {n : ℕ} (v : Fin n → F2) : ℕ :=
  (univ.filter fun i => v i ≠ 0).card

def word {n : ℕ} (S : Finset (Fin n)) : Fin n → F2 :=
  fun i => if i ∈ S then 1 else 0

def subsets (n s : ℕ) : Finset (Finset (Fin n)) :=
  univ.powerset.filter fun S => S.card ≤ s

@[simp] private theorem mem_subsets {n s : ℕ} {S : Finset (Fin n)} :
    S ∈ subsets n s ↔ S.card ≤ s := by
  simp [subsets]

theorem card_subsets (n s : ℕ) :
    (subsets n s).card = ∑ k ∈ range (s + 1), n.choose k := by
  have hd : (↑(range (s + 1)) : Set ℕ).PairwiseDisjoint
      (fun k => (univ : Finset (Fin n)).powersetCard k) := by
    intro i hi j hj hij
    exact disjoint_powersetCard_of_ne hij univ univ
  have h : subsets n s =
      (range (s + 1)).disjiUnion (fun k => (univ : Finset (Fin n)).powersetCard k)
        hd := by
    ext S
    simp only [mem_subsets, mem_disjiUnion, mem_range, mem_powersetCard,
      subset_univ, true_and]
    exact ⟨fun h => ⟨S.card, by omega, rfl⟩, fun ⟨k, hk, he⟩ => by omega⟩
  rw [h, card_disjiUnion]
  simp

private theorem word_injective {n : ℕ} : Function.Injective (@word n) := by
  intro S T h
  ext i
  have hi := congrFun h i
  by_cases hS : i ∈ S <;> by_cases hT : i ∈ T <;> simp_all [word]

private theorem weight_sub_le {n : ℕ} (S T : Finset (Fin n)) :
    weight (word S - word T) ≤ S.card + T.card := by
  apply le_trans (card_le_card (show
      (univ.filter fun i => (word S - word T) i ≠ 0) ⊆ S ∪ T from ?_))
    (card_union_le S T)
  intro i hi
  by_contra hn
  have hS : i ∉ S := fun h => hn (mem_union_left T h)
  have hT : i ∉ T := fun h => hn (mem_union_right S h)
  simpa [word, hS, hT] using (mem_filter.mp hi).2

private theorem sum_single_word {n : ℕ} (S : Finset (Fin n)) :
    ∑ i ∈ S, Pi.single i (1 : F2) = word S := by
  ext j
  simp only [sum_apply]
  by_cases hj : j ∈ S
  · rw [sum_eq_single j]
    · simp [word, hj]
    · intro i hi hij
      simp [Pi.single_apply, hij, Ne.symm hij]
    · exact fun h => (h hj).elim
  · rw [sum_eq_zero]
    · simp [word, hj]
    · intro i hi
      have hij : i ≠ j := fun h => hj (h ▸ hi)
      simp [Pi.single_apply, hij, Ne.symm hij]

/-- The cardinality equality upgrades unique correctable errors to all quotient elements. -/
theorem basis_of_minimum_weight (n s : ℕ) (C : Submodule F2 (Fin n → F2))
    (hs : 1 ≤ s)
    (hmin : ∀ v ∈ C, v ≠ 0 → 2 * s < weight v)
    (hcard : Nat.card ((Fin n → F2) ⧸ C) = (subsets n s).card) :
    ∃ A : Finset ((Fin n → F2) ⧸ C),
      A.card = n ∧ IsPerfectRestrictedBasis s A := by
  classical
  let Q := (Fin n → F2) ⧸ C
  letI : Fintype Q := Fintype.ofFinite Q
  let a : Fin n → Q := fun i => C.mkQ (Pi.single i 1)
  have hsum (S : Finset (Fin n)) : ∑ i ∈ S, a i = C.mkQ (word S) := by
    rw [← sum_single_word]
    exact (map_sum C.mkQ _ _).symm
  have hinj : Function.Injective
      (fun S : {S // S ∈ subsets n s} => ∑ i ∈ S.1, a i) := by
    intro S T he
    apply Subtype.ext
    apply word_injective
    have hc : word S.1 - word T.1 ∈ C := by
      apply (Submodule.Quotient.eq C).mp
      simpa only [hsum, Submodule.mkQ_apply] using he
    by_contra hn
    have hz : word S.1 - word T.1 ≠ 0 := sub_ne_zero.mpr hn
    have hw := hmin _ hc hz
    have hbound := weight_sub_le S.1 T.1
    have hS := mem_subsets.mp S.2
    have hT := mem_subsets.mp T.2
    omega
  have ha : Function.Injective a := by
    intro i j hij
    have h := hinj (a₁ := ⟨{i}, mem_subsets.mpr (by simpa using hs)⟩)
      (a₂ := ⟨{j}, mem_subsets.mpr (by simpa using hs)⟩) (by simpa using hij)
    exact singleton_injective (congrArg Subtype.val h)
  have hsurj : Function.Surjective
      (fun S : {S // S ∈ subsets n s} => ∑ i ∈ S.1, a i) := by
    apply (Fintype.bijective_iff_injective_and_card _).mpr ⟨hinj, ?_⟩ |>.2
    simpa only [Nat.card_eq_fintype_card, Fintype.card_coe] using hcard.symm
  let A : Finset Q := univ.image a
  refine ⟨A, ?_, ?_⟩
  · dsimp [A]
    rw [card_image_of_injective _ ha, card_univ, Fintype.card_fin]
  · intro g
    obtain ⟨S, hSg⟩ := hsurj g
    refine ⟨S.1.image a, ⟨image_subset_image (subset_univ _), ?_, ?_⟩, ?_⟩
    · rw [card_image_of_injective _ ha]
      exact mem_subsets.mp S.2
    · rw [sum_image (fun i _ j _ h => ha h)]
      exact hSg
    · intro T hT
      let U : Finset (Fin n) := univ.filter fun i => a i ∈ T
      have hUT : U.image a = T := by
        ext g'
        constructor
        · rintro hg'
          obtain ⟨i, hi, rfl⟩ := mem_image.mp hg'
          exact (mem_filter.mp hi).2
        · intro hg'
          obtain ⟨i, hi, rfl⟩ := mem_image.mp (hT.1 hg')
          exact mem_image.mpr ⟨i, mem_filter.mpr ⟨mem_univ _, hg'⟩, rfl⟩
      have hU : U.card ≤ s := by
        rw [← card_image_of_injective U ha, hUT]
        exact hT.2.1
      have hUsum : ∑ i ∈ U, a i = g := by
        calc
          _ = ∑ x ∈ U.image a, x := (sum_image (fun i _ j _ h => ha h)).symm
          _ = g := by rw [hUT]; exact hT.2.2
      have he := hinj (a₁ := ⟨U, mem_subsets.mpr hU⟩) (a₂ := S) (hUsum.trans hSg.symm)
      have he' : U = S.1 := congrArg Subtype.val he
      rw [← hUT, he']

end D5.S3.FiniteGroups.SubsetProducts.BinaryCodePerfectRestrictedBasis
