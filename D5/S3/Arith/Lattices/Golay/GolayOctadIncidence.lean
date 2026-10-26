/- GID: D5/S3/Arith/Lattices/Golay/GolayOctadIncidence
   generality: I
   mirror-B: D5/B/S3/Arith/Lattices/Golay/GolayOctadIncidence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Structural Steiner five-subset coverage and coordinate incidence of Golay octads. -/

import D5.S3.Arith.Lattices.Golay.GolayOctadCount
import D5.S3.Arith.Lattices.Golay.LeechSignedSupport
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Finset.Powerset

/-! # The Golay Steiner system and its coordinate incidences

Minimum distance bounds intersections of distinct octads by four. The flags
consisting of an octad and one of its five-subsets therefore inject into the
five-subsets of the coordinate set. Equal cardinalities give unique coverage.
Counting completions of one- and two-coordinate subsets gives the incidences.
These are classical properties of the extended binary Golay code.
-/

set_option Elab.async false

open scoped BigOperators
noncomputable section
namespace D5.S3.Arith.Lattices.Golay.GolayOctadIncidence
open GolayEncoder GolayOctadCount LeechSignedSupport
attribute [local instance] Classical.propDecidable
attribute [local instance 10] Fintype.ofFinite

private theorem bit_cases (a : F2) : a = 0 ∨ a = 1 := by
  have ha := ZMod.val_lt a
  have h : a.val = 0 ∨ a.val = 1 := by omega
  rcases h with h | h
  · left; apply ZMod.val_injective 2; simpa using h
  · right; apply ZMod.val_injective 2; change a.val = 1; exact h

private theorem support_sub (v w : Word) :
    wordSupport (v - w) = (wordSupport v \ wordSupport w) ∪
      (wordSupport w \ wordSupport v) := by
  ext i
  simp only [mem_wordSupport, Pi.sub_apply, Finset.mem_union, Finset.mem_sdiff]
  rcases bit_cases (v i) with h | h <;>
    rcases bit_cases (w i) with k | k <;> norm_num [h, k]

private theorem octad_intersection_le (c d : Octad) (hcd : c ≠ d) :
    (wordSupport (c.val : Word) ∩ wordSupport (d.val : Word)).card ≤ 4 := by
  have hn : (c.val : Word) - (d.val : Word) ≠ 0 := by
    intro h
    apply hcd
    apply Subtype.ext
    exact Subtype.ext (sub_eq_zero.mp h)
  have hm := minimum_weight _ (code.sub_mem c.val.property d.val.property) hn
  have hd : weight ((c.val : Word) - (d.val : Word)) ≤
      (8 - (wordSupport (c.val : Word) ∩ wordSupport (d.val : Word)).card) +
      (8 - (wordSupport (c.val : Word) ∩ wordSupport (d.val : Word)).card) := by
    rw [← wordSupport_card, support_sub]
    have h := Finset.card_union_le
      (wordSupport (c.val : Word) \ wordSupport (d.val : Word))
      (wordSupport (d.val : Word) \ wordSupport (c.val : Word))
    rw [Finset.card_sdiff, Finset.card_sdiff,
      Finset.inter_comm (wordSupport (d.val : Word)),
      wordSupport_card, wordSupport_card, c.property, d.property] at h
    exact h
  omega

private theorem same_five (T : Finset (Fin 24)) (hT : T.card = 5)
    (c d : Octad) (hc : T ⊆ wordSupport (c.val : Word))
    (hd : T ⊆ wordSupport (d.val : Word)) : c = d := by
  by_contra hcd
  have hi := octad_intersection_le c d hcd
  have ht := Finset.card_le_card (Finset.subset_inter hc hd)
  omega

private abbrev Five := ↥((Finset.univ : Finset (Fin 24)).powersetCard 5)
private abbrev Flag := (c : Octad) × ↥((wordSupport (c.val : Word)).powersetCard 5)

private def forget (p : Flag) : Five :=
  ⟨p.2.val, Finset.mem_powersetCard.mpr
    ⟨Finset.subset_univ _, (Finset.mem_powersetCard.mp p.2.property).2⟩⟩

private theorem forget_bijective : Function.Bijective forget := by
  apply (Fintype.bijective_iff_injective_and_card forget).mpr
  constructor
  · rintro ⟨c, S⟩ ⟨d, T⟩ h
    have hv : S.val = T.val := congrArg Subtype.val h
    have hc : c = d := same_five S.val (Finset.mem_powersetCard.mp S.property).2 c d
      (Finset.mem_powersetCard.mp S.property).1
      (hv ▸ (Finset.mem_powersetCard.mp T.property).1)
    subst d
    have hST : S = T := Subtype.ext hv
    subst T
    rfl
  · have hc : Fintype.card Octad = 759 := by
      simpa only [Nat.card_eq_fintype_card] using octad_card
    have hf (c : Octad) :
        Fintype.card ↥((wordSupport (c.val : Word)).powersetCard 5) = 56 := by
      rw [Fintype.card_coe, Finset.card_powersetCard, wordSupport_card, c.property]
      norm_num [Nat.choose]
    change Fintype.card ((c : Octad) × ↥((wordSupport (c.val : Word)).powersetCard 5)) =
      Fintype.card ↥((Finset.univ : Finset (Fin 24)).powersetCard 5)
    rw [Fintype.card_sigma]
    simp only [hf, Finset.sum_const, Finset.card_univ, smul_eq_mul, hc,
      Fintype.card_coe, Finset.card_powersetCard]
    norm_num [Nat.choose]

/-- Every five-coordinate subset belongs to exactly one actual Golay octad. -/
theorem steiner_five (T : Finset (Fin 24)) (hT : T.card = 5) :
    ∃! c : Octad, T ⊆ wordSupport (c.val : Word) := by
  obtain ⟨p, hp⟩ := forget_bijective.surjective
    ⟨T, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hT⟩⟩
  have hv : p.2.val = T := congrArg Subtype.val hp
  refine ⟨p.1, hv ▸ (Finset.mem_powersetCard.mp p.2.property).1, ?_⟩
  intro c hc
  exact same_five T hT c p.1 hc (hv ▸ (Finset.mem_powersetCard.mp p.2.property).1)

private theorem completion_identity (T : Finset (Fin 24)) (hT : T.card ≤ 5) :
    (Finset.univ.filter fun c : Octad => T ⊆ wordSupport (c.val : Word)).card *
      Nat.choose (8 - T.card) (5 - T.card) = Nat.choose (24 - T.card) (5 - T.card) := by
  have hs := forget_bijective.sum_comp (fun f : Five => if T ⊆ f.val then (1 : ℕ) else 0)
  change (∑ p : Flag, if T ⊆ p.2.val then (1 : ℕ) else 0) =
    ∑ f : Five, if T ⊆ f.val then (1 : ℕ) else 0 at hs
  rw [Fintype.sum_sigma] at hs
  change (∑ c : Octad, ∑ S : ↥((wordSupport (c.val : Word)).powersetCard 5),
      if T ⊆ S.val then (1 : ℕ) else 0) =
    ∑ S : ↥((Finset.univ : Finset (Fin 24)).powersetCard 5),
      if T ⊆ S.val then (1 : ℕ) else 0 at hs
  have hsum (s : Finset (Finset (Fin 24))) :
      (∑ S : s, if T ⊆ S.val then (1 : ℕ) else 0) =
      ∑ S ∈ s, if T ⊆ S then (1 : ℕ) else 0 :=
    (Finset.sum_subtype s (fun _ => Iff.rfl)
      (fun S => if T ⊆ S then (1 : ℕ) else 0)).symm
  simp_rw [hsum] at hs
  have local_count (c : Octad) :
      (∑ S ∈ (wordSupport (c.val : Word)).powersetCard 5,
        if T ⊆ S then (1 : ℕ) else 0) =
      if T ⊆ wordSupport (c.val : Word) then Nat.choose (8 - T.card) (5 - T.card) else 0 := by
    by_cases ht : T ⊆ wordSupport (c.val : Word)
    · rw [ite_eq_left ht, ← Finset.card_filter,
        Finset.card_filter_powersetCard_subset T _ 5 ht hT,
        wordSupport_card, c.property]
    · rw [ite_eq_right ht]
      apply Finset.sum_eq_zero
      intro S hS
      have hn : ¬ T ⊆ S := fun h => ht (h.trans (Finset.mem_powersetCard.mp hS).1)
      simp [hn]
  simp_rw [local_count] at hs
  rw [← Finset.card_filter,
    Finset.card_filter_powersetCard_subset T _ 5 (Finset.subset_univ _) hT] at hs
  simpa only [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, Finset.card_univ,
    Fintype.card_fin] using hs

/-- Incidences for any two distinct coordinates of the actual Golay octads. -/
theorem coordinate_incidence (i j : Fin 24) (hij : i ≠ j) :
    (Finset.univ.filter fun c : Octad => i ∈ wordSupport (c.val : Word)).card = 253 ∧
    (Finset.univ.filter fun c : Octad => j ∈ wordSupport (c.val : Word)).card = 253 ∧
    (Finset.univ.filter fun c : Octad =>
      i ∈ wordSupport (c.val : Word) ∧ j ∈ wordSupport (c.val : Word)).card = 77 ∧
    (Finset.univ.filter fun c : Octad =>
      (i ∈ wordSupport (c.val : Word) ∧ j ∉ wordSupport (c.val : Word)) ∨
      (i ∉ wordSupport (c.val : Word) ∧ j ∈ wordSupport (c.val : Word))).card = 352 ∧
    (Finset.univ.filter fun c : Octad =>
      i ∉ wordSupport (c.val : Word) ∧ j ∉ wordSupport (c.val : Word)).card = 330 := by
  have hi := completion_identity {i} (by simp)
  have hj := completion_identity {j} (by simp)
  have hp := completion_identity {i, j} (by simp [hij])
  have hpair : ({i, j} : Finset (Fin 24)).card = 2 := by simp [hij]
  norm_num only [Nat.choose, Finset.card_singleton, hpair,
    Finset.insert_subset_iff, Finset.singleton_subset_iff] at hi hj hp
  have hi' : (Finset.univ.filter fun c : Octad =>
      i ∈ wordSupport (c.val : Word)).card = 253 := by omega
  have hj' : (Finset.univ.filter fun c : Octad =>
      j ∈ wordSupport (c.val : Word)).card = 253 := by omega
  have hp' : (Finset.univ.filter fun c : Octad =>
      i ∈ wordSupport (c.val : Word) ∧ j ∈ wordSupport (c.val : Word)).card = 77 := by omega
  have partition (c : Octad) :
      (if i ∈ wordSupport (c.val : Word) then (1 : ℕ) else 0) +
      (if j ∈ wordSupport (c.val : Word) then 1 else 0) =
      2 * (if i ∈ wordSupport (c.val : Word) ∧ j ∈ wordSupport (c.val : Word) then 1 else 0) +
      (if (i ∈ wordSupport (c.val : Word) ∧ j ∉ wordSupport (c.val : Word)) ∨
          (i ∉ wordSupport (c.val : Word) ∧ j ∈ wordSupport (c.val : Word)) then 1 else 0) := by
    by_cases h : i ∈ wordSupport (c.val : Word) <;>
      by_cases k : j ∈ wordSupport (c.val : Word) <;> simp [h, k]
  have partition' (c : Octad) : (1 : ℕ) =
      (if i ∈ wordSupport (c.val : Word) ∧ j ∈ wordSupport (c.val : Word) then 1 else 0) +
      (if (i ∈ wordSupport (c.val : Word) ∧ j ∉ wordSupport (c.val : Word)) ∨
          (i ∉ wordSupport (c.val : Word) ∧ j ∈ wordSupport (c.val : Word)) then 1 else 0) +
      (if i ∉ wordSupport (c.val : Word) ∧ j ∉ wordSupport (c.val : Word) then 1 else 0) := by
    by_cases h : i ∈ wordSupport (c.val : Word) <;>
      by_cases k : j ∈ wordSupport (c.val : Word) <;> simp [h, k]
  have hx := Finset.sum_congr (s₁ := (Finset.univ : Finset Octad)) rfl (fun c _ => partition c)
  have hn := Finset.sum_congr (s₁ := (Finset.univ : Finset Octad)) rfl (fun c _ => partition' c)
  have hcard : Fintype.card Octad = 759 := by
    simpa only [Nat.card_eq_fintype_card] using octad_card
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.card_filter,
    hi', hj', hp'] at hx
  simp only [Finset.sum_add_distrib, ← Finset.card_filter, Finset.sum_const,
    Finset.card_univ, smul_eq_mul, mul_one, hcard, hp'] at hn
  exact ⟨hi', hj', hp', by omega, by omega⟩

#print axioms steiner_five
#print axioms coordinate_incidence

end D5.S3.Arith.Lattices.Golay.GolayOctadIncidence
