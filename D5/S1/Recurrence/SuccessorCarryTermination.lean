/- GID: D5/S1/Recurrence/SuccessorCarryTermination
   generality: I
   mirror-B: D5/B/S1/Recurrence/SuccessorCarryTermination
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Zeckendorf successor carry positions are bounded by the highest Fibonacci index. -/

import Mathlib.Data.Nat.Fib.Zeckendorf

/- Provenance: pinned mathlib supplies the canonical Zeckendorf representation,
   its decoding theorem, and the two-index descent of successive greedy tails.
   The carry trace, its conservation law, and the uniform index bound are new. -/

namespace D5.S1.Recurrence.SuccessorCarryTermination

local instance : IsTrans Nat fun a b => b + 2 <= a where
  trans _a _b _c hba hcb := hcb.trans (le_self_add.trans hba)

/-- Occupied Fibonacci indices removed when the canonical representation is incremented. -/
def successorCarryPositions (n : Nat) : Finset Nat :=
  n.zeckendorf.toFinset \ (n + 1).zeckendorf.toFinset

/-- Fibonacci indices introduced by incrementing the canonical representation. -/
def successorIntroducedPositions (n : Nat) : Finset Nat :=
  (n + 1).zeckendorf.toFinset \ n.zeckendorf.toFinset

@[simp] theorem mem_successorCarryPositions {n k : Nat} :
    k ∈ successorCarryPositions n ↔
      k ∈ n.zeckendorf ∧ k ∉ (n + 1).zeckendorf := by
  simp [successorCarryPositions]

private theorem zeckendorf_nodup (n : Nat) : n.zeckendorf.Nodup := by
  have h := Nat.isZeckendorfRep_zeckendorf n
  rw [List.IsZeckendorfRep, List.isChain_iff_pairwise, List.pairwise_append] at h
  exact h.1.imp fun hab => by omega

private theorem zeckendorf_length_le_greatestFib :
    forall n : Nat, n.zeckendorf.length <= n.greatestFib := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      cases n with
      | zero => simp
      | succ n =>
          rw [Nat.zeckendorf_succ, List.length_cons]
          have hrem_lt :
              n + 1 - Nat.fib (Nat.greatestFib (n + 1)) < n + 1 := by
            apply Nat.sub_lt (Nat.succ_pos n)
            exact Nat.fib_pos.2 (Nat.greatestFib_pos.2 (Nat.succ_pos n))
          have htail := ih
            (n + 1 - Nat.fib (Nat.greatestFib (n + 1))) hrem_lt
          have hdrop :=
            Nat.greatestFib_sub_fib_greatestFib_le_greatestFib
              (n := n + 1) (Nat.succ_ne_zero n)
          have htwo : 2 <= Nat.greatestFib (n + 1) := by
            rw [Nat.le_greatestFib]
            simp
          omega

/--
The successor carry chain is finite, with no more removed positions than the
highest Fibonacci index of the original canonical representation.
-/
theorem successor_carry_chain_terminates (n : Nat) :
    (successorCarryPositions n).card <= Nat.greatestFib n := by
  calc
    (successorCarryPositions n).card <= n.zeckendorf.toFinset.card :=
      Finset.card_le_card Finset.sdiff_subset
    _ <= n.zeckendorf.length := List.toFinset_card_le _
    _ <= Nat.greatestFib n := zeckendorf_length_le_greatestFib n

/-- Removed Fibonacci weight plus the increment equals the introduced weight. -/
theorem successor_carry_value_conservation (n : Nat) :
    (∑ k ∈ successorCarryPositions n, Nat.fib k) + 1 =
      ∑ k ∈ successorIntroducedPositions n, Nat.fib k := by
  let before := n.zeckendorf.toFinset
  let after := (n + 1).zeckendorf.toFinset
  let retained := before ∩ after
  have hbefore : ∑ k ∈ before, Nat.fib k = n := by
    dsimp only [before]
    rw [List.sum_toFinset Nat.fib (zeckendorf_nodup n), Nat.sum_zeckendorf_fib]
  have hafter : ∑ k ∈ after, Nat.fib k = n + 1 := by
    dsimp only [after]
    rw [List.sum_toFinset Nat.fib (zeckendorf_nodup (n + 1)),
      Nat.sum_zeckendorf_fib]
  have hbeforeParts :=
    Finset.sum_sdiff (f := Nat.fib) (Finset.inter_subset_left : retained ⊆ before)
  have hafterParts :=
    Finset.sum_sdiff (f := Nat.fib) (Finset.inter_subset_right : retained ⊆ after)
  have hbeforeDiff : before \ retained = successorCarryPositions n := by
    ext k
    simp [before, after, retained, successorCarryPositions]
  have hafterDiff : after \ retained = successorIntroducedPositions n := by
    ext k
    simp [before, after, retained, successorIntroducedPositions]
  rw [hbeforeDiff, hbefore] at hbeforeParts
  rw [hafterDiff, hafter] at hafterParts
  omega

end D5.S1.Recurrence.SuccessorCarryTermination
