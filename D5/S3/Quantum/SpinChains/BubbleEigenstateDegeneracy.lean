/- GID: D5/S3/Quantum/SpinChains/BubbleEigenstateDegeneracy
   generality: I
   mirror-B: D5/B/S3/Quantum/SpinChains/BubbleEigenstateDegeneracy
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Closed counting formula for labelled hard-core bubble placements on a cycle. -/

import D5.S3.Combinatorics.Geometry.MiuraRunCompositions
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators

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
  sorry

private noncomputable def marked_gap_equiv (L n : ℕ) (hL : 5 ≤ L)
    (hn : 1 ≤ n) (hbound : 5 * n ≤ L) :
    (Σ B : {B // B ∈ placements L n}, {a // a ∈ B.val}) ≃
      Fin L × PositiveLengths (L - 4 * n) n := by
  sorry

private lemma marked_count (L n : ℕ) (hL : 5 ≤ L) (hn : 1 ≤ n)
    (hbound : 5 * n ≤ L) :
    n * (placements L n).card = L * (L - 4 * n - 1).choose (n - 1) := by
  sorry

private lemma placement_count (L n : ℕ) (hL : 5 ≤ L) (hn : 1 ≤ n)
    (hbound : 5 * n ≤ L) :
    (placements L n).card = L * (L - 4 * n - 1).choose (n - 1) / n ∧
      n ∣ L * (L - 4 * n - 1).choose (n - 1) := by
  sorry

private lemma label_count (L : ℕ) (B : Finset (Fin L)) (E : ℤ) :
    (B.powerset.filter (fun x => 2 * (x.card : ℤ) - B.card = E)).card =
      if ((B.card : ℤ) + E) % 2 = 0 ∧ |E| ≤ (B.card : ℤ) then
        B.card.choose (((B.card : ℤ) + E) / 2).toNat else 0 := by
  sorry

private lemma vacuum_count (L : ℕ) (E : ℤ) :
    ∑ B ∈ placements L 0,
      (B.powerset.filter (fun x => 2 * (x.card : ℤ) - B.card = E)).card =
        if E = 0 then 1 else 0 := by
  sorry

private lemma sum_by_size (L : ℕ) (hL : 5 ≤ L) (E : ℤ) :
    bubbleCount L E = (if E = 0 then 1 else 0) +
      ∑ n ∈ Finset.Icc 1 (L / 5),
        (placements L n).card *
          (if ((n : ℤ) + E) % 2 = 0 ∧ |E| ≤ (n : ℤ) then
            n.choose (((n : ℤ) + E) / 2).toNat else 0) := by
  sorry

theorem result : claim := by
  intro L hL E
  rw [sum_by_size L hL E]
  push_cast
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  obtain ⟨hn1, hnL⟩ := Finset.mem_Icc.mp hn
  rw [(placement_count L n hL hn1 (by omega)).1]

end D5.S3.Quantum.SpinChains.BubbleEigenstateDegeneracy
