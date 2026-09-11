import Mathlib

/- Semantic probes for A110037. These finite checks are not deposited results. -/
namespace A110037BoundaryProbe

/-- A distinct partition is represented by its finite set of positive parts.
For each part p, the sum of all smaller parts is its suffix sum in descending order. -/
def nonsquashingDistinctPartitions (n : ℕ) : Finset (Finset ℕ) :=
  ((Finset.Icc 1 n).powerset).filter fun s =>
    s.sum id = n ∧ ∀ p ∈ s, (s.filter (fun q => q < p)).sum id ≤ p

/-- A073089's independent branch recurrence; zero is only a totalization outside its offset. -/
def paperfoldVariant (n : ℕ) : ℕ :=
  if n ≤ 1 then 0
  else if n % 4 = 0 then 1
  else if n % 4 = 2 then 0
  else if n % 8 = 3 then 1
  else if n % 8 = 7 then 0
  else if n % 16 = 5 then 1
  else if n % 16 = 13 then 0
  else paperfoldVariant ((n + 1) / 2)
termination_by n

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

private theorem b_six : (nonsquashingDistinctPartitions 6).card = 4 := by decide
private theorem b_ten : (nonsquashingDistinctPartitions 10).card = 9 := by decide

private theorem six_parts : nonsquashingDistinctPartitions 6 =
    {{6}, {5, 1}, {4, 2}, {3, 2, 1}} := by decide

private theorem initial_counts :
    (List.range 13).map (fun n => (nonsquashingDistinctPartitions n).card) =
      [1, 1, 1, 2, 2, 3, 4, 5, 6, 7, 9, 10, 13] := by decide

private theorem paperfold_small (n : ℕ) (hn : n ≤ 16) :
    paperfoldVariant n =
      [0, 0, 0, 1, 1, 1, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 1].getD n 0 := by
  interval_cases n <;> (rw [paperfoldVariant]; norm_num)
  rw [paperfoldVariant]
  norm_num

private theorem initial_paperfold :
    (List.range 16).map (fun n => paperfoldVariant (n + 1)) =
      [0, 0, 1, 1, 1, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 1] := by
  norm_num [List.range_succ, paperfold_small]

/-- Literal Corollary 4 (21), with the printed unrestricted odd-index quantifier. -/
def printedOddRule : Prop :=
  ∀ n : ℕ, Odd n → (nonsquashingDistinctPartitions n).card % 2 =
    ((nonsquashingDistinctPartitions (n - 1)).card + 1) % 2

private theorem zero_one :
    (nonsquashingDistinctPartitions 0).card = 1 ∧
    (nonsquashingDistinctPartitions 1).card = 1 := by decide

private theorem printed_odd_rule_false : ¬ printedOddRule := by
  intro h
  have h1 := h 1 (by decide)
  have hne : (nonsquashingDistinctPartitions 1).card % 2 ≠
      ((nonsquashingDistinctPartitions (1 - 1)).card + 1) % 2 := by decide
  exact hne h1

private theorem target_at_two :
    (-1 : ℤ) ^ (2 / 2 : ℕ) * ((nonsquashingDistinctPartitions 2).card % 2 : ℕ) =
      (paperfoldVariant 2 : ℤ) - paperfoldVariant 3 := by
  have h : (nonsquashingDistinctPartitions 2).card = 1 := by decide
  rw [paperfold_small 2 (by decide), paperfold_small 3 (by decide)]
  norm_num [h]

private theorem target_at_three :
    (-1 : ℤ) ^ (3 / 2 : ℕ) * ((nonsquashingDistinctPartitions 3).card % 2 : ℕ) =
      (paperfoldVariant 3 : ℤ) - paperfoldVariant 4 := by
  have h : (nonsquashingDistinctPartitions 3).card = 2 := by decide
  rw [paperfold_small 3 (by decide), paperfold_small 4 (by decide)]
  norm_num [h]

#print axioms b_six
#print axioms b_ten
#print axioms printed_odd_rule_false

end A110037BoundaryProbe
