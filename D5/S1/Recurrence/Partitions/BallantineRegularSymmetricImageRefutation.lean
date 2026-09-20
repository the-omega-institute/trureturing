/- GID: D5/S1/Recurrence/Partitions/BallantineRegularSymmetricImageRefutation
   generality: I
   mirror-B: D5/B/S1/Recurrence/Partitions/BallantineRegularSymmetricImageRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: [mathlib/module/Mathlib.Combinatorics.Enumerative.Partition.Basic, mathlib/module/Mathlib.Tactic.NormNum]
   utility: kind=certified-instance; basis=refutes=gid:D5/S1/Recurrence/Partitions/BallantineRegularSymmetricImageRefutation.claim; result=D5/S1/Recurrence/Partitions/BallantineRegularSymmetricImageRefutation.result; claim=D5/S1/Recurrence/Partitions/BallantineRegularSymmetricImageRefutation.claim
   digest: Conjecture 16 is false for d=5 and n=4. -/
/- proof_shape: result: bind-only
   escape_witness: none
   admission_basis: open-problem-resolution (issue #8751)
   Direct frozen dependencies: none (pinned Mathlib only) -/

import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.Tactic.NormNum

namespace D5.S1.Recurrence.Partitions.BallantineRegularSymmetricImageRefutation

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.defProp false

/-- `pre_k(lambda)`: the parts of the elementary symmetric partition, one product for every
`k`-element set of positions of `lambda`. `Multiset.powersetCard` counts positions, so repeated
parts retain their multiplicity. -/
def pre (k : ℕ) {n : ℕ} (l : Nat.Partition n) : Multiset ℕ :=
  (l.parts.powersetCard k).map Multiset.prod

/-- `ImP_k(n) = pre_k(P_k(n))`: the image set of partitions of `n` with at least `k` parts. -/
def imP (k n : ℕ) : Finset (Multiset ℕ) :=
  (Finset.univ.filter (fun l : Nat.Partition n => k ≤ l.parts.card)).image (pre k)

/-- A multiset of parts is `d`-regular when none of its parts is divisible by `d`. -/
def IsRegular (d : ℕ) (mu : Multiset ℕ) : Prop :=
  ∀ x ∈ mu, ¬d ∣ x

local instance isRegularDecidable (d : ℕ) (mu : Multiset ℕ) : Decidable (IsRegular d mu) := by
  unfold IsRegular
  infer_instance

/-- The number `r_{d,k}(n)` of `d`-regular members of `ImP_k(n)`. -/
def r (d k n : ℕ) : ℕ :=
  ((imP k n).filter (IsRegular d)).card

/-- The printed table in Conjecture 16, transcribed column by column. Natural-number division
represents the printed floor values before the result is cast to an integer. -/
def table (d n : ℕ) : ℤ :=
  if d = 2 then
    if n % 2 = 0 then (((n + 2) / 4 : ℕ) : ℤ) else 0
  else if d = 3 then
    match n % 6 with
    | 0 => ((2 * (n / 6) : ℕ) : ℤ)
    | 1 => ((n / 6 : ℕ) : ℤ)
    | 2 => ((n / 6 + 1 : ℕ) : ℤ)
    | 3 => ((2 * (n / 6) + 1 : ℕ) : ℤ)
    | 4 => ((n / 6 + 1 : ℕ) : ℤ)
    | 5 => ((n / 6 + 1 : ℕ) : ℤ)
    | _ => 0
  else if d = 4 then
    match n % 4 with
    | 0 => ((n / 4 : ℕ) : ℤ)
    | 1 => ((n / 4 : ℕ) : ℤ)
    | 2 => ((n / 4 + 1 : ℕ) : ℤ)
    | 3 => ((n / 4 + 1 : ℕ) : ℤ)
    | _ => 0
  else if d = 5 then
    match n % 10 with
    | 0 => ((3 * (n / 10) : ℕ) : ℤ)
    | 1 => ((4 * (n / 10) : ℕ) : ℤ)
    | 2 => ((3 * (n / 10) : ℕ) : ℤ)
    | 3 => ((3 * (n / 10) + 1 : ℕ) : ℤ)
    | 4 => ((3 * (n / 10) + 1 : ℕ) : ℤ)
    | 5 => ((3 * (n / 10) + 2 : ℕ) : ℤ)
    | 6 => ((4 * (n / 10) + 2 : ℕ) : ℤ)
    | 7 => ((3 * (n / 10) + 2 : ℕ) : ℤ)
    | 8 => ((3 * (n / 10) + 2 : ℕ) : ℤ)
    | 9 => ((3 * (n / 10) + 3 : ℕ) : ℤ)
    | _ => 0
  else 0

/-- Conjecture 16, for every `n` and each of the four printed columns. -/
def claim : Prop :=
  ∀ n : ℕ, ∀ d ∈ ({2, 3, 4, 5} : Finset ℕ),
    (r d 2 n : ℤ) - r d 3 n = table d n

private def compositionsFour : Finset (Composition 4) :=
  { ⟨[4], by decide, by decide⟩,
    ⟨[3, 1], by decide, by decide⟩,
    ⟨[1, 3], by decide, by decide⟩,
    ⟨[2, 2], by decide, by decide⟩,
    ⟨[2, 1, 1], by decide, by decide⟩,
    ⟨[1, 2, 1], by decide, by decide⟩,
    ⟨[1, 1, 2], by decide, by decide⟩,
    ⟨[1, 1, 1, 1], by decide, by decide⟩ }

private def partitionsFour : Finset (Nat.Partition 4) :=
  { ⟨{4}, by simp, by decide⟩,
    ⟨{3, 1}, by simp, by decide⟩,
    ⟨{2, 2}, by simp, by decide⟩,
    ⟨{2, 1, 1}, by simp, by decide⟩,
    ⟨{1, 1, 1, 1}, by simp, by decide⟩ }

/-- The `d = 5`, `n = 4` entry has value two, while the printed table gives one. -/
theorem result : ¬claim := by
  have partition_univ_eq_composition_image (n : ℕ) :
      (Finset.univ : Finset (Nat.Partition n)) =
        (Finset.univ : Finset (Composition n)).image (Nat.Partition.ofComposition n) := by
    ext p
    simp only [Finset.mem_univ, Finset.mem_image, true_iff]
    exact (Nat.Partition.ofComposition_surj p).imp fun c hc => ⟨trivial, hc⟩
  have composition_univ_four :
      (Finset.univ : Finset (Composition 4)) = compositionsFour := by
    symm
    apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
    rw [Finset.card_univ, composition_card]
    norm_num [compositionsFour]
  have partition_univ_four :
      (Finset.univ : Finset (Nat.Partition 4)) = partitionsFour := by
    rw [partition_univ_eq_composition_image 4, composition_univ_four]
    ext p
    simp [compositionsFour, partitionsFour, Nat.Partition.ofComposition,
      Nat.Partition.ext_iff]
    aesop (config := { warnOnNonterminal := false }) <;> decide
  have imP_two_four :
      imP 2 4 = ({{3}, {4}, {2, 2, 1}, {1, 1, 1, 1, 1, 1}} : Finset (Multiset ℕ)) := by
    rw [imP, partition_univ_four]
    simp [partitionsFour, Finset.filter_insert, Finset.filter_singleton, pre,
      Multiset.powersetCard_one]
    rw [show (2 ::ₘ 1 ::ₘ {2} : Multiset ℕ) = 2 ::ₘ 2 ::ₘ {1} by decide]
  have imP_three_four :
      imP 3 4 = ({{2}, {1, 1, 1, 1}} : Finset (Multiset ℕ)) := by
    rw [imP, partition_univ_four]
    simp [partitionsFour, Finset.filter_insert, Finset.filter_singleton, pre,
      Multiset.powersetCard_one]
  have imP_two_four_regular_five :
      ({{3}, {4}, {2, 2, 1}, {1, 1, 1, 1, 1, 1}} : Finset (Multiset ℕ)).filter
          (IsRegular 5) = {{3}, {4}, {2, 2, 1}, {1, 1, 1, 1, 1, 1}} := by
    apply Finset.filter_eq_self.mpr
    intro mu hmu
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmu
    rcases hmu with rfl | rfl | rfl | rfl <;> norm_num [IsRegular]
  have imP_three_four_regular_five :
      ({{2}, {1, 1, 1, 1}} : Finset (Multiset ℕ)).filter (IsRegular 5) =
        {{2}, {1, 1, 1, 1}} := by
    apply Finset.filter_eq_self.mpr
    intro mu hmu
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmu
    rcases hmu with rfl | rfl <;> norm_num [IsRegular]
  intro h
  have hr2 : r 5 2 4 = 4 := by
    rw [r, imP_two_four, imP_two_four_regular_five]
    decide
  have hr3 : r 5 3 4 = 2 := by
    rw [r, imP_three_four, imP_three_four_regular_five]
    norm_num
  have h54 := h 4 5 (by decide)
  norm_num [hr2, hr3, table] at h54

example : ({1, 1} : Multiset ℕ).powersetCard 1 = {{1}, {1}} := by
  decide

example :
    pre 2 (Nat.Partition.ofSums 7 {3, 2, 1, 1} (by decide)) = {6, 3, 3, 2, 2, 1} := by
  decide

example : table 5 4 = 1 := by
  decide

example :
    imP 2 4 = ({{3}, {4}, {2, 2, 1}, {1, 1, 1, 1, 1, 1}} : Finset (Multiset ℕ)) ∧
    imP 3 4 = ({{2}, {1, 1, 1, 1}} : Finset (Multiset ℕ)) ∧
    r 5 2 4 = 4 ∧
    r 5 3 4 = 2 ∧
    (r 2 2 4 : ℤ) - r 2 3 4 = table 2 4 ∧
    (r 3 2 4 : ℤ) - r 3 3 4 = table 3 4 ∧
    (r 4 2 4 : ℤ) - r 4 3 4 = table 4 4 := by
  have partition_univ_eq_composition_image (n : ℕ) :
      (Finset.univ : Finset (Nat.Partition n)) =
        (Finset.univ : Finset (Composition n)).image (Nat.Partition.ofComposition n) := by
    ext p
    simp only [Finset.mem_univ, Finset.mem_image, true_iff]
    exact (Nat.Partition.ofComposition_surj p).imp fun c hc => ⟨trivial, hc⟩
  have composition_univ_four :
      (Finset.univ : Finset (Composition 4)) = compositionsFour := by
    symm
    apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
    rw [Finset.card_univ, composition_card]
    norm_num [compositionsFour]
  have partition_univ_four :
      (Finset.univ : Finset (Nat.Partition 4)) = partitionsFour := by
    rw [partition_univ_eq_composition_image 4, composition_univ_four]
    ext p
    simp [compositionsFour, partitionsFour, Nat.Partition.ofComposition,
      Nat.Partition.ext_iff]
    aesop (config := { warnOnNonterminal := false }) <;> decide
  have imP_two_four :
      imP 2 4 = ({{3}, {4}, {2, 2, 1}, {1, 1, 1, 1, 1, 1}} : Finset (Multiset ℕ)) := by
    rw [imP, partition_univ_four]
    simp [partitionsFour, Finset.filter_insert, Finset.filter_singleton, pre,
      Multiset.powersetCard_one]
    rw [show (2 ::ₘ 1 ::ₘ {2} : Multiset ℕ) = 2 ::ₘ 2 ::ₘ {1} by decide]
  have imP_three_four :
      imP 3 4 = ({{2}, {1, 1, 1, 1}} : Finset (Multiset ℕ)) := by
    rw [imP, partition_univ_four]
    simp [partitionsFour, Finset.filter_insert, Finset.filter_singleton, pre,
      Multiset.powersetCard_one]
  have imP_two_four_regular_five :
      ({{3}, {4}, {2, 2, 1}, {1, 1, 1, 1, 1, 1}} : Finset (Multiset ℕ)).filter
          (IsRegular 5) = {{3}, {4}, {2, 2, 1}, {1, 1, 1, 1, 1, 1}} := by
    apply Finset.filter_eq_self.mpr
    intro mu hmu
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmu
    rcases hmu with rfl | rfl | rfl | rfl <;> norm_num [IsRegular]
  have imP_three_four_regular_five :
      ({{2}, {1, 1, 1, 1}} : Finset (Multiset ℕ)).filter (IsRegular 5) =
        {{2}, {1, 1, 1, 1}} := by
    apply Finset.filter_eq_self.mpr
    intro mu hmu
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmu
    rcases hmu with rfl | rfl <;> norm_num [IsRegular]
  have hr2 : r 5 2 4 = 4 := by
    rw [r, imP_two_four, imP_two_four_regular_five]
    decide
  have hr3 : r 5 3 4 = 2 := by
    rw [r, imP_three_four, imP_three_four_regular_five]
    norm_num
  have hd2 : (r 2 2 4 : ℤ) - r 2 3 4 = table 2 4 := by
    simp only [r]
    rw [imP_two_four, imP_three_four]
    simp [Finset.filter_insert, Finset.filter_singleton, IsRegular, table]
  have hd3 : (r 3 2 4 : ℤ) - r 3 3 4 = table 3 4 := by
    simp only [r]
    rw [imP_two_four, imP_three_four]
    simp [Finset.filter_insert, Finset.filter_singleton, IsRegular, table]
    decide
  have hd4 : (r 4 2 4 : ℤ) - r 4 3 4 = table 4 4 := by
    simp only [r]
    rw [imP_two_four, imP_three_four]
    simp [Finset.filter_insert, Finset.filter_singleton, IsRegular, table]
    decide
  exact ⟨imP_two_four, imP_three_four, hr2, hr3, hd2, hd3, hd4⟩

example : (r 5 2 1 : ℤ) - r 5 3 1 = table 5 1 := by
  have hi2 : imP 2 1 = ∅ := by
    simp [imP, Nat.Partition.partition_one_parts]
  have hi3 : imP 3 1 = ∅ := by
    simp [imP, Nat.Partition.partition_one_parts]
  simp [r, hi2, hi3, table]

#print axioms result

end D5.S1.Recurrence.Partitions.BallantineRegularSymmetricImageRefutation
