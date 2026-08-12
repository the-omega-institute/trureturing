/- GID: D5/S1/Words/Powers/GoldenDesubstitution
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:block-boundary-bookkeeping)
   anchors: []
   digest: Golden substitution blocks start exactly at the true letters. -/

import D5.S1.Words.GoldenSubstFixed

namespace D5.S1.Words.Powers

open D5.S1.Words
open D5.S0.Tower.GoldenGapWord

/-! ### Block arithmetic

`goldenSubstStart` enumerates the left endpoints of the Fibonacci substitution blocks
that tile the infinite golden word.  A block is `[true, false]` above a `true` letter and
`[true]` above a `false` letter, so every block starts with `true` and contains no other
`true`.  Block boundaries are therefore exactly the `true` positions, which is the
recognizability statement the descent needs. -/

theorem substLength_pos (b : Bool) : 0 < (subst b).length := by
  cases b <;> simp [subst]

theorem substLength_le_two (b : Bool) : (subst b).length ≤ 2 := by
  cases b <;> simp [subst]

theorem goldenSubstStart_zero : goldenSubstStart 0 = 0 := by
  simp [goldenSubstStart, goldenWindowTrueCount]

theorem goldenSubstStart_step_true {i : Nat} (h : goldenWord i = true) :
    goldenSubstStart (i + 1) = goldenSubstStart i + 2 := by
  rw [goldenSubstStart_succ, h]
  rfl

theorem goldenSubstStart_step_false {i : Nat} (h : goldenWord i = false) :
    goldenSubstStart (i + 1) = goldenSubstStart i + 1 := by
  rw [goldenSubstStart_succ, h]
  rfl

theorem goldenSubstStart_lt_succ (i : Nat) :
    goldenSubstStart i < goldenSubstStart (i + 1) := by
  rw [goldenSubstStart_succ]
  have := substLength_pos (goldenWord i)
  omega

theorem goldenSubstStart_strictMono : StrictMono goldenSubstStart :=
  strictMono_nat_of_lt_succ goldenSubstStart_lt_succ

theorem goldenSubstStart_mono : Monotone goldenSubstStart :=
  goldenSubstStart_strictMono.monotone

/-- Blocks are nonempty, so `goldenSubstStart` advances by at least one per letter. -/
theorem goldenSubstStart_add_le (i j : Nat) :
    goldenSubstStart i + j ≤ goldenSubstStart (i + j) := by
  induction j with
  | zero => simp
  | succ j ih =>
      have hlt := goldenSubstStart_lt_succ (i + j)
      have he : i + (j + 1) = (i + j) + 1 := by omega
      rw [he]
      omega

/-! ### Recognizability -/

private theorem subst_head (b : Bool) (h : 0 < (subst b).length) :
    (subst b).get ⟨0, h⟩ = true := by
  cases b <;> rfl

private theorem subst_second (b : Bool) (h : 1 < (subst b).length) :
    (subst b).get ⟨1, h⟩ = false := by
  cases b with
  | false => simp [subst] at h
  | true => rfl

/-- Every substitution block begins on a `true` letter. -/
theorem goldenWord_goldenSubstStart (i : Nat) :
    goldenWord (goldenSubstStart i) = true := by
  have h := golden_word_substitution_fixed i ⟨0, substLength_pos _⟩
  have h2 := h.trans (subst_head (goldenWord i) (substLength_pos _))
  simpa using h2

/-- The letter just after a block start records the block length, hence the source letter. -/
theorem goldenWord_goldenSubstStart_succ (i : Nat) :
    goldenWord (goldenSubstStart i + 1) = ! goldenWord i := by
  by_cases hb : goldenWord i = true
  · have hlen : 1 < (subst (goldenWord i)).length := by
      rw [hb]; simp [subst]
    have h := golden_word_substitution_fixed i ⟨1, hlen⟩
    rw [subst_second _ hlen] at h
    rw [h, hb]
    rfl
  · have hb' : goldenWord i = false := by simpa using hb
    have hstart := goldenWord_goldenSubstStart (i + 1)
    rw [goldenSubstStart_step_false hb'] at hstart
    rw [hstart, hb']
    rfl

/-- Every position lies in a unique substitution block. -/
theorem exists_goldenSubstStart_window (n : Nat) :
    ∃ k, goldenSubstStart k ≤ n ∧ n < goldenSubstStart (k + 1) := by
  induction n with
  | zero =>
      refine ⟨0, by simp [goldenSubstStart_zero], ?_⟩
      have h := goldenSubstStart_lt_succ 0
      have h0 := goldenSubstStart_zero
      omega
  | succ n ih =>
      obtain ⟨k, hk1, hk2⟩ := ih
      by_cases hlt : n + 1 < goldenSubstStart (k + 1)
      · exact ⟨k, by omega, hlt⟩
      · have h := goldenSubstStart_lt_succ (k + 1)
        exact ⟨k + 1, by omega, by omega⟩

/-- Recognizability: the block boundaries are exactly the `true` positions. -/
theorem exists_goldenSubstStart_of_true {n : Nat} (h : goldenWord n = true) :
    ∃ k, goldenSubstStart k = n := by
  obtain ⟨k, hk1, hk2⟩ := exists_goldenSubstStart_window n
  refine ⟨k, ?_⟩
  by_contra hne
  have hlt : goldenSubstStart k < n := lt_of_le_of_ne hk1 hne
  by_cases hb : goldenWord k = true
  · rw [goldenSubstStart_step_true hb] at hk2
    have hn : n = goldenSubstStart k + 1 := by omega
    rw [hn, goldenWord_goldenSubstStart_succ, hb] at h
    exact Bool.noConfusion h
  · have hb' : goldenWord k = false := by simpa using hb
    rw [goldenSubstStart_step_false hb'] at hk2
    omega

/-! ### The two forbidden patterns -/

/-- The golden word has no two consecutive `false` letters. -/
theorem golden_no_two_false {n : Nat} (h0 : goldenWord n = false) :
    goldenWord (n + 1) = true := by
  obtain ⟨k, hk1, hk2⟩ := exists_goldenSubstStart_window n
  have hlt : goldenSubstStart k < n := by
    rcases Nat.lt_or_ge (goldenSubstStart k) n with h | h
    · exact h
    · exfalso
      have heq : goldenSubstStart k = n := le_antisymm hk1 h
      rw [← heq, goldenWord_goldenSubstStart] at h0
      exact Bool.noConfusion h0
  have hbk : goldenWord k = true := by
    by_contra hb
    have hb' : goldenWord k = false := by simpa using hb
    rw [goldenSubstStart_step_false hb'] at hk2
    omega
  have hstep := goldenSubstStart_step_true hbk
  rw [hstep] at hk2
  have hnext : n + 1 = goldenSubstStart (k + 1) := by omega
  rw [hnext, goldenWord_goldenSubstStart]

/-- The golden word has no three consecutive `true` letters. -/
theorem golden_no_three_true {n : Nat} (h0 : goldenWord n = true)
    (h1 : goldenWord (n + 1) = true) : goldenWord (n + 2) = false := by
  obtain ⟨k, hk⟩ := exists_goldenSubstStart_of_true h0
  have hk1 := goldenWord_goldenSubstStart_succ k
  rw [hk, h1] at hk1
  have hbk : goldenWord k = false := by
    cases hb : goldenWord k with
    | false => rfl
    | true => rw [hb] at hk1; exact absurd hk1 (by simp)
  have hs1 : goldenSubstStart (k + 1) = n + 1 := by
    rw [goldenSubstStart_step_false hbk, hk]
  have h2 := goldenWord_goldenSubstStart_succ (k + 1)
  rw [hs1] at h2
  have he : n + 1 + 1 = n + 2 := by omega
  rw [he] at h2
  rw [h2, golden_no_two_false hbk]
  rfl

theorem goldenWord_zero : goldenWord 0 = true := by
  have h := goldenWord_goldenSubstStart 0
  rwa [goldenSubstStart_zero] at h

end D5.S1.Words.Powers
