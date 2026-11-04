/- GID: D5/S3/Quantum/SpinChains/BubbleEigenstateDegeneracy
   generality: I
   mirror-B: D5/B/S3/Quantum/SpinChains/BubbleEigenstateDegeneracy
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Closed counting formula for labelled hard-core bubble placements on a cycle. -/

module

public import D5.S3.Combinatorics.Geometry.MiuraRunCompositions
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Fintype.BigOperators

/-! Labelled placements of separated three-site bubbles on a periodic chain. -/

@[expose] public section

namespace D5.S3.Quantum.SpinChains.BubbleEigenstateDegeneracy

open scoped BigOperators
open D5.S3.Combinatorics.Geometry.MiuraRunCompositions

/-- Clockwise distances between distinct centres are at least five sites.
The quantification over ordered pairs imposes the condition in both directions. -/
def Admissible (L : ℕ) (B : Finset (Fin L)) : Prop :=
  ∀ a ∈ B, ∀ b ∈ B, a ≠ b →
    5 ≤ if a.val < b.val then b.val - a.val else L + b.val - a.val

/-- Count centre sets and their subsets of centres labelled X; all other centres are Y. -/
noncomputable def bubbleCount (L : ℕ) (E : ℤ) : ℕ := by
  classical
  exact ∑ B ∈ (Finset.univ : Finset (Finset (Fin L))).filter (Admissible L),
    (B.powerset.filter (fun x => 2 * (x.card : ℤ) - B.card = E)).card

/-- The closed form counts placements without identifying translations. -/
def claim : Prop :=
  ∀ L : ℕ, 5 ≤ L → ∀ E : ℤ,
    (bubbleCount L E : ℤ) = (if E = 0 then 1 else 0) +
      ∑ n ∈ Finset.Icc 1 (L / 5),
        ((L * (L - 4 * n - 1).choose (n - 1) / n : ℕ) : ℤ) *
          (if ((n : ℤ) + E) % 2 = 0 ∧ |E| ≤ (n : ℤ) then
            (n.choose (((n : ℤ) + E) / 2).toNat : ℤ) else 0)

private noncomputable def placements (L n : ℕ) : Finset (Finset (Fin L)) := by
  classical
  exact Finset.univ.filter (fun B => Admissible L B ∧ B.card = n)

private lemma packing_bound (L : ℕ) (hL : 5 ≤ L) (B : Finset (Fin L))
    (hB : Admissible L B) : 5 * B.card ≤ L := by
  classical
  let f : B × Fin 5 → Fin L := fun p =>
    ⟨if p.1.val.val + p.2.val < L then p.1.val.val + p.2.val
      else p.1.val.val + p.2.val - L, by
      have ha := p.1.val.isLt
      have hi := p.2.isLt
      split_ifs <;> omega⟩
  have hf : Function.Injective f := by
    rintro ⟨a, i⟩ ⟨b, j⟩ he
    have he := congrArg Fin.val he
    change (if a.val.val + i.val < L then a.val.val + i.val
      else a.val.val + i.val - L) =
      (if b.val.val + j.val < L then b.val.val + j.val
      else b.val.val + j.val - L) at he
    have ha := a.val.isLt
    have hb := b.val.isLt
    have hi := i.isLt
    have hj := j.isLt
    have hab : a = b := by
      by_contra hne
      have hab : a.val ≠ b.val := fun h => hne (Subtype.ext h)
      have hdir := hB a.val a.property b.val b.property hab
      have hrev := hB b.val b.property a.val a.property hab.symm
      split_ifs at he hdir hrev <;> omega
    subst b
    have hij : i = j := by
      apply Fin.ext
      split_ifs at he <;> omega
    exact Prod.ext rfl hij
  have hc := Fintype.card_le_of_injective f hf
  simpa only [Fintype.card_prod, Fintype.card_coe, Fintype.card_fin, Nat.mul_comm] using hc

private noncomputable def marked_gap_equiv (L n : ℕ) (hL : 5 ≤ L)
    (hn : 1 ≤ n) (hbound : 5 * n ≤ L) :
    (Σ B : {B // B ∈ placements L n}, {a // a ∈ B.val}) ≃
      Fin L × PositiveLengths (L - 4 * n) n := by
  sorry

private lemma marked_count (L n : ℕ) (hL : 5 ≤ L) (hn : 1 ≤ n)
    (hbound : 5 * n ≤ L) :
    n * (placements L n).card = L * (L - 4 * n - 1).choose (n - 1) := by
  classical
  have hc := Nat.card_congr (marked_gap_equiv L n hL hn hbound)
  rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Fin L), Fintype.card_fin,
    positive_lengths_card (L - 4 * n) n hn (by omega), Nat.card_eq_fintype_card,
    Fintype.card_sigma] at hc
  have hs : (∑ B : {B // B ∈ placements L n}, Fintype.card {a // a ∈ B.val}) =
      (placements L n).card * n := by
    have hb (B : {B // B ∈ placements L n}) : B.val.card = n :=
      (Finset.mem_filter.mp B.property).2.2
    simp only [Fintype.card_coe, hb, Finset.sum_const, Finset.card_univ,
      Fintype.card_coe, smul_eq_mul]
  rw [hs, Nat.mul_comm] at hc
  exact hc

private lemma placement_count (L n : ℕ) (hL : 5 ≤ L) (hn : 1 ≤ n)
    (hbound : 5 * n ≤ L) :
    (placements L n).card = L * (L - 4 * n - 1).choose (n - 1) / n ∧
      n ∣ L * (L - 4 * n - 1).choose (n - 1) := by
  have hc := marked_count L n hL hn hbound
  constructor
  · rw [← hc, Nat.mul_div_right _ (by omega : 0 < n)]
  · exact ⟨(placements L n).card, hc.symm⟩

private lemma label_count (L : ℕ) (B : Finset (Fin L)) (E : ℤ) :
    (B.powerset.filter (fun x => 2 * (x.card : ℤ) - B.card = E)).card =
      if ((B.card : ℤ) + E) % 2 = 0 ∧ |E| ≤ (B.card : ℤ) then
        B.card.choose (((B.card : ℤ) + E) / 2).toNat else 0 := by
  classical
  split_ifs with h
  · have hbounds := abs_le.mp h.2
    have he (k : ℕ) : 2 * (k : ℤ) - B.card = E ↔
        k = (((B.card : ℤ) + E) / 2).toNat := by
      omega
    have hf : B.powerset.filter (fun x => 2 * (x.card : ℤ) - B.card = E) =
        B.powersetCard (((B.card : ℤ) + E) / 2).toNat := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_powersetCard, he]
    rw [hf, Finset.card_powersetCard]
  · apply Finset.card_eq_zero.mpr
    apply Finset.filter_eq_empty_iff.mpr
    intro x hx he
    have hc := Finset.card_le_card (Finset.mem_powerset.mp hx)
    apply h
    refine ⟨?_, abs_le.mpr ⟨?_, ?_⟩⟩ <;> omega

private lemma vacuum_count (L : ℕ) (E : ℤ) :
    ∑ B ∈ placements L 0,
      (B.powerset.filter (fun x => 2 * (x.card : ℤ) - B.card = E)).card =
        if E = 0 then 1 else 0 := by
  classical
  have hp : placements L 0 = {∅} := by
    ext B
    simp only [placements, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.card_eq_zero, Finset.mem_singleton]
    constructor
    · exact And.right
    · intro h
      subst B
      exact ⟨by intro a ha; exact False.elim (Finset.notMem_empty a ha), rfl⟩
  rw [hp, Finset.sum_singleton, label_count]
  by_cases h : E = 0
  · subst E
    simp
  · simp [h, Ne.symm h]

private lemma sum_by_size (L : ℕ) (hL : 5 ≤ L) (E : ℤ) :
    bubbleCount L E = (if E = 0 then 1 else 0) +
      ∑ n ∈ Finset.Icc 1 (L / 5),
        (placements L n).card *
          (if ((n : ℤ) + E) % 2 = 0 ∧ |E| ≤ (n : ℤ) then
            n.choose (((n : ℤ) + E) / 2).toNat else 0) := by
  classical
  let S := (Finset.univ : Finset (Finset (Fin L))).filter (Admissible L)
  let f := fun B : Finset (Fin L) =>
    (B.powerset.filter (fun x => 2 * (x.card : ℤ) - B.card = E)).card
  have hm : ∀ B ∈ S, B.card ∈ Finset.Icc 0 (L / 5) := by
    intro B hB
    have hb := packing_bound L hL B (Finset.mem_filter.mp hB).2
    exact Finset.mem_Icc.mpr ⟨Nat.zero_le _, by omega⟩
  have hp (n : ℕ) : S.filter (fun B => B.card = n) = placements L n := by
    ext B
    simp only [S, placements, Finset.mem_filter, Finset.mem_univ, true_and]
  have hs : bubbleCount L E =
      ∑ n ∈ Finset.Icc 0 (L / 5), ∑ B ∈ placements L n, f B := by
    change (∑ B ∈ S, f B) = _
    rw [← Finset.sum_fiberwise_of_maps_to hm f]
    simp only [hp]
  rw [hs, ← Finset.insert_Icc_succ_left_eq_Icc (Nat.zero_le (L / 5)),
    Finset.sum_insert (by simp), show (Order.succ (0 : ℕ)) = 1 from rfl]
  rw [show (∑ B ∈ placements L 0, f B) = (if E = 0 then 1 else 0) from
    vacuum_count L E]
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  have hb (B : Finset (Fin L)) (hB : B ∈ placements L n) : B.card = n :=
    (Finset.mem_filter.mp hB).2.2
  calc
    (∑ B ∈ placements L n, f B) = ∑ _B ∈ placements L n,
        (if ((n : ℤ) + E) % 2 = 0 ∧ |E| ≤ (n : ℤ) then
          n.choose (((n : ℤ) + E) / 2).toNat else 0) := by
      apply Finset.sum_congr rfl
      intro B hB
      dsimp only [f]
      rw [label_count, hb B hB]
    _ = _ := by rw [Finset.sum_const, smul_eq_mul]

theorem result : claim := by
  intro L hL E
  rw [sum_by_size L hL E]
  simp only [Nat.cast_add, Nat.cast_sum, Nat.cast_mul, Nat.cast_ite, Nat.cast_one,
    Nat.cast_zero]
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  obtain ⟨hn1, hnL⟩ := Finset.mem_Icc.mp hn
  rw [(placement_count L n hL hn1 (by omega)).1]

end D5.S3.Quantum.SpinChains.BubbleEigenstateDegeneracy
