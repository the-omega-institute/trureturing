/- GID: D5/S3/Combinatorics/Sequenceability/OriginalCyclicSevenCarrierLowerBound
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Sequenceability/OriginalCyclicSevenCarrierLowerBound
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Data.Finset.Powerset, mathlib/module/Mathlib.Data.ZMod.Basic]
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Combinatorics/Sequenceability/OriginalCyclicSevenCarrierLowerBound.cyclic_seven_carrier_card_lower_bound; premises=D5/S3/Combinatorics/Sequenceability/OriginalTranslatedQuotientCarrierLowerBound.cyclic_carrier_card_lower_bound
   digest: Six distinct signed quotient classes exclude orders twenty and twenty-one, forcing a 154-element cyclic carrier. -/

import D5.S3.Combinatorics.Sequenceability.OriginalTranslatedQuotientCarrierLowerBound
import Mathlib.Data.Finset.Powerset
import Mathlib.Order.Interval.Finset.Nat

/-!
The finite certificate ranges over 210 six-element subsets of {1,...,10}
for each of the two quotient orders. It does not enumerate label tuples.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u

namespace D5.S3.Combinatorics.Sequenceability.OriginalCyclicSevenCarrierLowerBound

open scoped Classical BigOperators
open OriginalFiniteOrderSharpness (Index Coordinate q a triple)
open OriginalCyclicFiveCarrierLowerBound (normalized_signed_classes)
open OriginalTranslatedQuotientCarrierLowerBound (quotient_data)

/-- In either remaining quotient order, every choice of six standard positive
representatives contains a signed zero relation at three different residues. -/
private lemma six_residue_certificate :
    ∀ n ∈ ({20, 21} : Finset ℕ),
      ∀ S ∈ (Finset.Icc 1 10).powersetCard 6,
        ∃ x ∈ S, ∃ y ∈ S, ∃ z ∈ S,
          x < y ∧ y < z ∧ (x + y = z ∨ x + y + z = n) := by
  decide +kernel

private lemma six_small_residues_impossible
    (n : ℕ) (hn : n = 20 ∨ n = 21) (r : Fin 6 → ℕ)
    (hpos : ∀ i, 0 < r i) (hbound : ∀ i, 2 * r i ≤ n)
    (hinj : Function.Injective r)
    (hadd : ∀ i j k, i ≠ j → i ≠ k → j ≠ k → r i + r j ≠ r k)
    (hsum : ∀ i j k, i ≠ j → i ≠ k → j ≠ k → r i + r j + r k ≠ n) : False := by
  classical
  let S := Finset.univ.image r
  have hsub : S ⊆ Finset.Icc 1 10 := by
    intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    have hp := hpos i
    have hb := hbound i
    apply Finset.mem_Icc.mpr
    constructor <;> omega
  have hcard : S.card = 6 := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  have hS : S ∈ (Finset.Icc 1 10).powersetCard 6 :=
    Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩
  have hn' : n ∈ ({20, 21} : Finset ℕ) := by
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hn
  obtain ⟨x, hx, y, hy, z, hz, hxy, hyz, he⟩ := six_residue_certificate n hn' S hS
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hy
  obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hz
  have hij : i ≠ j := by intro h; subst j; omega
  have hik : i ≠ k := by intro h; subst k; omega
  have hjk : j ≠ k := by intro h; subst k; omega
  rcases he with he | he
  · exact hadd i j k hij hik hjk he
  · exact hsum i j k hij hik hjk he

/-- The complete original six-pair support pattern in a finite cyclic carrier
with distinguished additive order seven needs at least 154 elements. -/
theorem cyclic_seven_carrier_card_lower_bound
    {G : Type u} [AddCommGroup G] [Finite G] [IsAddCyclic G]
    (f : Coordinate 7 → G) (hq : addOrderOf (f (q 7)) = 7)
    (hzero : ∀ C : Finset (Coordinate 7),
      (C.Nonempty ∧ (∑ x ∈ C, f x) = 0) ↔ ∃ i : Index 7, C = triple 7 i) :
    154 ≤ Nat.card G := by
  classical
  let H := AddSubgroup.zmultiples (f (q 7))
  let A : Fin 6 → G ⧸ H := fun i => (f (a 7 i) : G ⧸ H)
  letI : IsAddCyclic (G ⧸ H) :=
    isAddCyclic_of_surjective (QuotientAddGroup.mk' H) (QuotientAddGroup.mk'_surjective H)
  have hd := quotient_data 7 (by decide) f hq hzero
  have hH : Nat.card H = 7 := by
    dsimp only [H]
    rw [Nat.card_zmultiples, hq]
  have hG : Nat.card G = Nat.card (G ⧸ H) * 7 := by
    simpa only [hH] using AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup H
  have htwenty : 20 ≤ Nat.card (G ⧸ H) := by
    have hb := OriginalTranslatedQuotientCarrierLowerBound.cyclic_carrier_card_lower_bound
      7 (by decide) f hq hzero
    rw [hG] at hb
    norm_num at hb
    omega
  have hquot : 22 ≤ Nat.card (G ⧸ H) := by
    by_contra hsmall
    have hn : Nat.card (G ⧸ H) = 20 ∨ Nat.card (G ⧸ H) = 21 := by omega
    obtain ⟨r, hpos, hbound, hinj, hadd, hsum⟩ :=
      normalized_signed_classes 6 (by omega) A hd.1 hd.2.1 hd.2.2.1 hd.2.2.2
    exact six_small_residues_impossible _ hn r hpos hbound hinj hadd hsum
  rw [hG]
  omega

end D5.S3.Combinatorics.Sequenceability.OriginalCyclicSevenCarrierLowerBound
