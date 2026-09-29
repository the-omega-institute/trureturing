/- GID: D5/S3/Observer/Budget/DyadicDeadlineStaircase
   generality: G
   mirror-B: D5/B/S3/Observer/Budget/DyadicDeadlineStaircase
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact binary staircase for the operational deadline-family clock minimum. -/

import D5.S3.Observer.Budget.DyadicPrefixDelayRange

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.Budget.DyadicDeadlineStaircase

open DyadicForwardWaitingOptimality DyadicPrefixDelayRange

/-- A binary prefix with at most one missing one-bit is the all-ones prefix
or is obtained by deleting exactly one of its binary places. -/
private theorem binary_prefix_top_or_one_missing (d : Nat) :
    ∀ t : Nat, t < 2 ^ d →
      t.bitIndices.length ≤ d ∧
      (t.bitIndices.length = d → t = 2 ^ d - 1) ∧
      (t.bitIndices.length + 1 = d →
        ∃ k : Nat, k < d ∧ t + 2 ^ k = 2 ^ d - 1) := by
  induction d with
  | zero =>
      intro t ht
      have h : t = 0 := by simpa using ht
      subst t
      simp [Nat.bitIndices]
  | succ d ih =>
      intro t ht
      have hp : 2 ^ (d + 1) = 2 * 2 ^ d := by rw [pow_succ]; omega
      let q := t / 2
      have hq : q < 2 ^ d := by dsimp [q]; rw [hp] at ht; omega
      obtain ⟨bound, top, missing⟩ := ih q hq
      rcases (show t % 2 = 0 ∨ t % 2 = 1 by omega) with he | ho
      · have hform : t = 2 * q := by dsimp [q]; omega
        have hweight : t.bitIndices.length = q.bitIndices.length := by
          rw [hform, Nat.bitIndices_two_mul, List.length_map]
        refine ⟨by omega, ?_, ?_⟩
        · intro hw
          omega
        · intro hw
          have hfull := top (by omega)
          refine ⟨0, by omega, ?_⟩
          rw [hform, hfull, hp]
          norm_num
          omega
      · have hform : t = 2 * q + 1 := by dsimp [q]; omega
        have hweight : t.bitIndices.length = q.bitIndices.length + 1 := by
          rw [hform, Nat.bitIndices_two_mul_add_one]
          simp
        refine ⟨by omega, ?_, ?_⟩
        · intro hw
          have hfull := top (by omega)
          rw [hform, hfull, hp]
          omega
        · intro hw
          obtain ⟨k, hk, hmiss⟩ := missing (by omega)
          refine ⟨k + 1, by omega, ?_⟩
          rw [hform, hp, pow_succ]
          omega

private theorem binary_prefix_exception_weights (d : Nat) :
    (2 ^ d - 1).bitIndices.length = d ∧
    ∀ k : Nat, k < d → (2 ^ d - 1 - 2 ^ k).bitIndices.length + 1 = d := by
  induction d with
  | zero =>
      constructor
      · simp [Nat.bitIndices]
      · intro k hk
        omega
  | succ d ih =>
      obtain ⟨fullWeight, missingWeight⟩ := ih
      have hp : 2 ^ (d + 1) = 2 * 2 ^ d := by rw [pow_succ]; omega
      have hfull : 0 < 2 ^ d := Nat.two_pow_pos d
      constructor
      · have hform : 2 ^ (d + 1) - 1 = 2 * (2 ^ d - 1) + 1 := by
          rw [hp]; omega
        rw [hform, Nat.bitIndices_two_mul_add_one]
        simp [fullWeight]
      · intro k hk
        by_cases hz : k = 0
        · subst k
          have hform : 2 ^ (d + 1) - 1 - 2 ^ 0 = 2 * (2 ^ d - 1) := by
            rw [hp]; omega
          rw [hform, Nat.bitIndices_two_mul, List.length_map, fullWeight]
        · have hk' : k - 1 < d := by omega
          have hpow : 2 ^ (k - 1) < 2 ^ d :=
            Nat.pow_lt_pow_right (by decide) hk'
          have hpowk : 2 ^ k = 2 * 2 ^ (k - 1) := by
            conv_lhs => rw [show k = (k - 1) + 1 by omega, pow_succ]
            omega
          have hform : 2 ^ (d + 1) - 1 - 2 ^ k =
              2 * (2 ^ d - 1 - 2 ^ (k - 1)) + 1 := by
            rw [hp, hpowk]
            omega
          rw [hform, Nat.bitIndices_two_mul_add_one]
          simp only [List.length_cons, List.length_map]
          have := missingWeight (k - 1) hk'
          omega

/-- Exactly the all-ones prefix and the one-bit deletions can acquire a
second terminal parity after the sharp common deadline. -/
theorem exceptional_prefix_timing (d : Nat) :
    let P := 2 ^ (d + 1)
    let W := sharpWait (d + 1)
    earliestTime d (2 ^ d - 1) + P = W + P ∧
    (∀ k : Nat, k < d →
      earliestTime d (2 ^ d - 1 - 2 ^ k) + P = W + 2 ^ (k + 1)) ∧
    (∀ t : Nat, t < 2 ^ d → t.bitIndices.length + 2 ≤ d →
      earliestTime d t + P ≤ W) ∧
    (∀ t : Nat, t < 2 ^ d →
      t.bitIndices.length ≤ d ∧
      (t.bitIndices.length = d → t = 2 ^ d - 1) ∧
      (t.bitIndices.length + 1 = d →
        ∃ k : Nat, k < d ∧ t + 2 ^ k = 2 ^ d - 1)) := by
  dsimp only
  let P := 2 ^ (d + 1)
  let W := sharpWait (d + 1)
  have hp : P = 2 * 2 ^ d := by dsimp [P]; rw [pow_succ]; omega
  have hW : sharpWait (d + 1) = d * 2 ^ (d + 1) + 1 := by
    simp [sharpWait]
  obtain ⟨fullWeight, missingWeight⟩ := binary_prefix_exception_weights d
  have hpos : 0 < 2 ^ d := Nat.two_pow_pos d
  refine ⟨?_, ?_, ?_, binary_prefix_top_or_one_missing d⟩
  · have hval : 2 * (2 ^ d - 1) < P := by rw [hp]; omega
    dsimp [P] at hval
    dsimp [earliestTime]
    rw [fullWeight, hW]
    rw [Nat.mul_comm (2 ^ (d + 1)) d]
    omega
  · intro k hk
    have hpow : 2 ^ k < 2 ^ d := Nat.pow_lt_pow_right (by decide) hk
    have hstep : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ]; omega
    have hval : (2 ^ d - 1 - 2 ^ k) + 2 ^ k = 2 ^ d - 1 := by omega
    have hsmall : 2 * (2 ^ d - 1 - 2 ^ k) < P := by rw [hp]; omega
    have hwt := missingWeight k hk
    have hmul : P * (2 ^ d - 1 - 2 ^ k).bitIndices.length + P = P * d := by
      calc
        _ = P * ((2 ^ d - 1 - 2 ^ k).bitIndices.length + 1) := by ring
        _ = P * d := by rw [hwt]
    dsimp [P] at hmul hsmall
    dsimp [earliestTime]
    rw [hW, hstep]
    rw [Nat.mul_comm (2 ^ (d + 1)) d] at hmul
    omega
  · intro t ht hwt
    have hval : 2 * t < P := by rw [hp]; omega
    have hmul : P * t.bitIndices.length + 2 * P ≤ P * d := by
      have hm := Nat.mul_le_mul_left P hwt
      nlinarith [hm]
    dsimp [P] at hmul hval
    dsimp [earliestTime]
    rw [hW]
    rw [Nat.mul_comm (2 ^ (d + 1)) d] at hmul
    omega

#print axioms exceptional_prefix_timing

end D5.S3.Observer.Budget.DyadicDeadlineStaircase
