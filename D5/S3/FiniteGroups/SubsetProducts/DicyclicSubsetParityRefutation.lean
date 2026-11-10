/- GID: D5/S3/FiniteGroups/SubsetProducts/DicyclicSubsetParityRefutation
   generality: I
   mirror-B: D5/B/S3/FiniteGroups/SubsetProducts/DicyclicSubsetParityRefutation
   mirror-E: none(waiver:exact-parity-obstruction)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/FiniteGroups/SubsetProducts/DicyclicSubsetParityRefutation.claim; result=D5/S3/FiniteGroups/SubsetProducts/DicyclicSubsetParityRefutation.result; claim=D5/S3/FiniteGroups/SubsetProducts/DicyclicSubsetParityRefutation.claim
   digest: The three product-versus-right-quotient classes cannot all have even cardinality in Dic_12 at subset size four. -/

import Mathlib.GroupTheory.SpecificGroups.Quaternion
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Ring.Parity

/-! Sagar Mandal and Neetu, Exact and Asymptotic Counts of MSTD, MDTS,
and Balanced Sets in Dicyclic Groups, arXiv:2602.09073v1, Question 6.3.
https://arxiv.org/abs/2602.09073v1; Main.tex line 792.
The source asks about ALL distinct subsets and literal right quotients.
Source SHA-256: 7ed61ecf73935d71b750c85a2f03f635b3669ae370d87e41f16c653c0e48f959.
`QuaternionGroup n` is the actual order-4n dicyclic group. The refutation
uses only trichotomy and the odd total of 495 four-element subsets at n = 3;
it does not replace the group operation or compute a restricted family.
-/

set_option maxRecDepth 4096

noncomputable section

namespace D5.S3.FiniteGroups.SubsetProducts.DicyclicSubsetParityRefutation

open Finset
attribute [local instance] Classical.propDecidable

/-- The literal set AA, with duplicates removed. -/
def productSet {G : Type*} [Group G] [DecidableEq G] (A : Finset G) : Finset G :=
  (A.product A).image fun xy => xy.1 * xy.2

/-- The literal RIGHT quotient set AA^(-1), with duplicates removed. -/
def rightQuotientSet {G : Type*} [Group G] [DecidableEq G] (A : Finset G) : Finset G :=
  (A.product A).image fun xy => xy.1 * xy.2⁻¹

/-- All distinct m-subsets whose product set is larger than their right quotient set. -/
def sumDominantCount (G : Type*) [Group G] [Fintype G] [DecidableEq G] (m : ℕ) : ℕ :=
  ((univ : Finset G).powersetCard m |>.filter fun A =>
    (rightQuotientSet A).card < (productSet A).card).card

/-- All distinct m-subsets whose product set is smaller than their right quotient set. -/
def differenceDominantCount (G : Type*) [Group G] [Fintype G] [DecidableEq G] (m : ℕ) : ℕ :=
  ((univ : Finset G).powersetCard m |>.filter fun A =>
    (productSet A).card < (rightQuotientSet A).card).card

/-- All distinct m-subsets with equal product and right quotient cardinalities. -/
def balancedCount (G : Type*) [Group G] [Fintype G] [DecidableEq G] (m : ℕ) : ℕ :=
  ((univ : Finset G).powersetCard m |>.filter fun A =>
    (productSet A).card = (rightQuotientSet A).card).card

/-- Exact affirmative statement of Mandal--Neetu Question 6.3, including both parities of n. -/
def claim : Prop :=
  ∀ (n : ℕ) (hn : 3 ≤ n),
    letI : NeZero n := ⟨by omega⟩
    ∀ (m : ℕ), 2 ≤ m → m ≤ 2 * n →
      Even (sumDominantCount (QuaternionGroup n) m) ∧
      Even (differenceDominantCount (QuaternionGroup n) m) ∧
      Even (balancedCount (QuaternionGroup n) m)

private theorem comparison_partition {α : Type*} (s : Finset α) (f g : α → ℕ) :
    (s.filter fun a => g a < f a).card +
      (s.filter fun a => f a < g a).card +
      (s.filter fun a => f a = g a).card = s.card := by
  classical
  have h₁ := card_filter_add_card_filter_not (s := s) (fun a => g a < f a)
  have h₂ := card_filter_add_card_filter_not
    (s := s.filter fun a => ¬ g a < f a) (fun a => f a < g a)
  have hl : ((s.filter fun a => ¬ g a < f a).filter fun a => f a < g a) =
      s.filter (fun a => f a < g a) := by
    apply Finset.ext
    intro a
    simp only [mem_filter]
    constructor
    · rintro ⟨⟨ha, _⟩, hlt⟩
      exact ⟨ha, hlt⟩
    · rintro ⟨ha, hlt⟩
      exact ⟨⟨ha, by omega⟩, hlt⟩
  have he : ((s.filter fun a => ¬ g a < f a).filter fun a => ¬ f a < g a) =
      s.filter (fun a => f a = g a) := by
    apply Finset.ext
    intro a
    simp only [mem_filter]
    constructor
    · rintro ⟨⟨ha, hge⟩, hle⟩
      exact ⟨ha, by omega⟩
    · rintro ⟨ha, heq⟩
      exact ⟨⟨ha, by omega⟩, by omega⟩
  rw [hl, he] at h₂
  omega

private theorem counts_total (G : Type*) [Group G] [Fintype G] [DecidableEq G]
    (m : ℕ) : sumDominantCount G m + differenceDominantCount G m +
      balancedCount G m = Nat.choose (Fintype.card G) m := by
  simpa only [sumDominantCount, differenceDominantCount, balancedCount,
    card_powersetCard, card_univ] using
    (comparison_partition ((univ : Finset G).powersetCard m)
      (fun A => (productSet A).card) (fun A => (rightQuotientSet A).card))

/-- The exact universal statement is false: its instance n = 3, m = 4 is impossible. -/
theorem result : Not claim := by
  intro h
  obtain ⟨hS, hD, hB⟩ := h 3 (by norm_num) 4 (by norm_num) (by norm_num)
  have hc := counts_total (QuaternionGroup 3) 4
  have hnum : Nat.choose (Fintype.card (QuaternionGroup 3)) 4 = 495 := by
    rw [QuaternionGroup.card]
    norm_num [Nat.choose]
  have hev : Even (Nat.choose (Fintype.card (QuaternionGroup 3)) 4) :=
    hc ▸ (hS.add hD).add hB
  rw [hnum] at hev
  obtain ⟨k, hk⟩ := hev
  omega

end D5.S3.FiniteGroups.SubsetProducts.DicyclicSubsetParityRefutation
