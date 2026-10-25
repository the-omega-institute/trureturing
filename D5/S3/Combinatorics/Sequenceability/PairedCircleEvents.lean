/- GID: D5/S3/Combinatorics/Sequenceability/PairedCircleEvents
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Sequenceability/PairedCircleEvents
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Data.Finset.Powerset]
   utility: none
   digest: Original C3 coordinate pair inventories and actual common-circle intersection counts. -/

import D5.S3.Combinatorics.Sequenceability.PairedZeroSubsetSpectrum
import D5.S3.Combinatorics.CircularWords.SimultaneousPairContraction
import Mathlib.Data.Finset.Powerset

/-! These events use the original additive labels, with coefficient one. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Sequenceability.PairedCircleEvents

open D5.S3.Combinatorics.Sequenceability.PairedZeroSubsetSpectrum
open D5.S3.Combinatorics.CircularWords.DisjointBlockContraction
open D5.S3.Combinatorics.CircularWords.CircularOrderCount
open D5.S3.Combinatorics.CircularWords.SimultaneousPairContraction
open Finset
open scoped BigOperators Classical
noncomputable section

theorem pairs_subset {r : ℕ} (I : Finset (Fin r)) : pairs I ⊆ alphabet r := by
  intro x hx
  obtain ⟨y,hy,rfl⟩ := mem_image.mp hx
  exact mem_image.mpr ⟨y,mem_univ _,rfl⟩

theorem pairs_injective (r : ℕ) : Function.Injective (@pairs r) := by
  intro I J h
  ext i
  have hh : label (i,true) ∈ pairs I ↔ label (i,true) ∈ pairs J := by rw [h]
  simpa only [mem_pairs] using hh

theorem pairs_disjoint {r : ℕ} {I J : Finset (Fin r)} (h : Disjoint I J) :
    Disjoint (pairs I) (pairs J) := by
  apply Finset.disjoint_left.mpr
  intro x hx hy
  obtain ⟨z,hz,rfl⟩ := mem_image.mp hx
  exact Finset.disjoint_left.mp h (mem_product.mp hz).1 ((mem_pairs J z).mp hy)

theorem pairs_complement {r : ℕ} (I : Finset (Fin r)) :
    pairs (univ \ I) = alphabet r \ pairs I := by
  ext x
  by_cases hx : x ∈ alphabet r
  · obtain ⟨z,hz,rfl⟩ := mem_image.mp hx
    simp only [mem_pairs,mem_sdiff,mem_univ,true_and]
    simp [alphabet]
  · have hl : x ∉ pairs (univ \ I) := fun h => hx (pairs_subset _ h)
    simp [hl,hx]

theorem pairs_sum_zero {r : ℕ} (I : Finset (Fin r)) : (∑ x ∈ pairs I, x) = 0 := by
  apply (sum_eq_zero_iff _ (pairs_subset I)).mpr
  intro i
  simpa [label] using (mem_pairs I (i,true)).trans (mem_pairs I (i,false)).symm

theorem alphabet_sum_zero (r : ℕ) : (∑ x ∈ alphabet r, x) = 0 := by
  rw [←pairs_univ]
  exact pairs_sum_zero _

/-- One designated opposite-pair circular adjacency event. -/
def adjacency {r : ℕ} (i : Fin r) (C : Cycle (V r)) : Prop :=
  Arc (alphabet r) (pairs {i}) C

/-- The actual count of any prescribed intersection through degree three. -/
theorem adjacency_intersection_card {r : ℕ} (hr : 12 ≤ r) (T : Finset (Fin r))
    (hT : T.card ≤ 3) :
    ((circles (alphabet r)).filter (fun C => ∀ i ∈ T, adjacency i C)).card =
      2^T.card * (2*r-T.card-1).factorial := by
  let F := T.image (fun i => pairs {i})
  have hinj : Function.Injective (fun i : Fin r => pairs {i}) := by
    intro i j h
    simpa using pairs_injective r h
  have hcard : F.card = T.card := card_image_of_injective _ hinj
  have hsub : ∀ S ∈ F, S ⊆ alphabet r := by
    intro S hS
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hS
    exact pairs_subset _
  have htwo : ∀ S ∈ F, S.card=2 := by
    intro S hS
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hS
    simp [pairs_card]
  have hd : (F : Set (Finset (V r))).Pairwise (fun S U => Disjoint S U) := by
    intro S hS U hU hne
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hS
    obtain ⟨j,hj,rfl⟩ := mem_image.mp hU
    exact pairs_disjoint (by simp [show i ≠ j by rintro rfl; exact hne rfl])
  have hs : 2*F.card < (alphabet r).card := by rw [hcard,alphabet_card]; omega
  have hc := joint_pair_card (alphabet r) F hsub htwo hd hs
  let e : {C : Cycle (V r) // Joint (alphabet r) F C} ≃
      {C : Cycle (V r) // C ∈ (circles (alphabet r)).filter
        (fun C => ∀ i ∈ T, adjacency i C)} :=
    { toFun := fun C => ⟨C.val, Finset.mem_filter.mpr ⟨C.property.1, by
        intro i hi
        exact C.property.2 (pairs {i}) (mem_image_of_mem _ hi)⟩⟩
      invFun := fun C => ⟨C.val, (Finset.mem_filter.mp C.property).1, by
        intro S hS
        obtain ⟨i, hi, rfl⟩ := mem_image.mp hS
        exact (Finset.mem_filter.mp C.property).2 i hi⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e,Nat.card_eq_fintype_card,Fintype.card_coe] at hc
  simpa only [hcard,alphabet_card] using hc

/-- Finite subset enumeration turns the actual common-circle counts into binomial moments. -/
theorem adjacency_moment {r p : ℕ} (hr : 12 ≤ r) (hp : p ≤ 3) :
    (∑ T ∈ (univ : Finset (Fin r)).powersetCard p,
      (((circles (alphabet r)).filter (fun C => ∀ i ∈ T, adjacency i C)).card : ℚ)) =
      (r.choose p : ℚ) * (2^p * (2*r-p-1).factorial : ℕ) := by
  have he : ∀ T ∈ (univ : Finset (Fin r)).powersetCard p,
      ((circles (alphabet r)).filter (fun C => ∀ i ∈ T, adjacency i C)).card =
        2^p * (2*r-p-1).factorial := by
    intro T hT
    have hcard := (mem_powersetCard.mp hT).2
    rw [adjacency_intersection_card hr T (by omega),hcard]
  calc
    _ = ∑ _T ∈ (univ : Finset (Fin r)).powersetCard p,
        ((2^p * (2*r-p-1).factorial : ℕ) : ℚ) := by
      apply sum_congr rfl
      intro T hT
      rw [he T hT]
    _ = _ := by simp [Finset.card_powersetCard]

end
end D5.S3.Combinatorics.Sequenceability.PairedCircleEvents
