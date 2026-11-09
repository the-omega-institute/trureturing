/- GID: D5/S3/FiniteGroups/DicyclicSubsetParityRefutation
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/DicyclicSubsetParityRefutation
   mirror-E: none(waiver:exact-parity-obstruction)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/FiniteGroups/DicyclicSubsetParityRefutation.claim; result=D5/S3/FiniteGroups/DicyclicSubsetParityRefutation.result; claim=D5/S3/FiniteGroups/DicyclicSubsetParityRefutation.claim
   digest: The three product-versus-right-quotient classes cannot all have even cardinality in Dic_12 at subset size four. -/

import Mathlib.GroupTheory.SpecificGroups.Quaternion
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Omega

/-! Mandal--Neetu, arXiv:2602.09073v1, Question 6.3, Main.tex line 792.
The source asks about ALL distinct subsets and literal right quotients.
Source SHA-256: 7ed61ecf73935d71b750c85a2f03f635b3669ae370d87e41f16c653c0e48f959.
`QuaternionGroup n` is the actual order-4n dicyclic group. The refutation
uses only trichotomy and the odd total of 495 four-element subsets at n = 3;
it does not replace the group operation or compute a restricted family.
-/

noncomputable section

namespace D5.S3.FiniteGroups.DicyclicSubsetParityRefutation

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
    ext a
    simp only [mem_filter]
    omega
  have he : ((s.filter fun a => ¬ g a < f a).filter fun a => ¬ f a < g a) =
      s.filter (fun a => f a = g a) := by
    ext a
    simp only [mem_filter]
    omega
  rw [hl, he] at h₂
  omega

/-- The exact universal statement is false: its instance n = 3, m = 4 is impossible. -/
theorem result : Not claim := by
  intro h
  obtain ⟨hS, hD, hB⟩ := h 3 (by norm_num) 4 (by norm_num) (by norm_num)
  have hp := comparison_partition
    ((univ : Finset (QuaternionGroup 3)).powersetCard 4)
    (fun A => (productSet A).card) (fun A => (rightQuotientSet A).card)
  have hc : sumDominantCount (QuaternionGroup 3) 4 +
      differenceDominantCount (QuaternionGroup 3) 4 +
      balancedCount (QuaternionGroup 3) 4 = 495 := by
    calc
      _ = ((univ : Finset (QuaternionGroup 3)).powersetCard 4).card := hp
      _ = 495 := by
        rw [card_powersetCard, card_univ, QuaternionGroup.card]
        norm_num [Nat.choose]
  have hev : Even (495 : ℕ) := hc ▸ (hS.add hD).add hB
  norm_num at hev

#print axioms result
#print claim
#check result

end D5.S3.FiniteGroups.DicyclicSubsetParityRefutation
