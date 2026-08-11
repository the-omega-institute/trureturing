/- GID: D5/S1/Phase/GoldenBeattyCount
   generality: G
   mirror-B: D5/B/S1/Phase/GoldenBeattyCount
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The golden shift s(v)=⌊(v+1)/φ⌋ satisfies s(v)≤N exactly when v<⌊(N+1)φ⌋, so the count of v∈ℕ with s(v)≤N is exactly ⌊(N+1)φ⌋; the biconditional is proved by floor arithmetic and the irrationality of (N+1)φ. -/

import Mathlib

namespace D5.S1.Phase.GoldenBeattyCount

open Real

/-- Golden Beatty count (obs 6.146): the golden shift `s(v) = ⌊(v+1)/φ⌋` satisfies `s(v) ≤ N`
exactly when `v < ⌊(N+1)φ⌋`, so the number of `v ∈ ℕ` with `s(v) ≤ N` is exactly `⌊(N+1)φ⌋`. -/
theorem golden_beatty_count (N v : ℕ) :
    ⌊((v : ℝ) + 1) / goldenRatio⌋₊ ≤ N ↔ v < ⌊((N : ℝ) + 1) * goldenRatio⌋₊ := by
  have hφ : (0 : ℝ) < goldenRatio := goldenRatio_pos
  have hpos : (0 : ℝ) ≤ ((v : ℝ) + 1) / goldenRatio := by positivity
  have hNφ : (0 : ℝ) ≤ ((N : ℝ) + 1) * goldenRatio := by positivity
  have hirr : Irrational (((N : ℝ) + 1) * goldenRatio) := by
    have h1 : ((N : ℝ) + 1) = ((N + 1 : ℕ) : ℝ) := by push_cast; ring
    rw [h1]
    exact goldenRatio_irrational.natCast_mul (Nat.succ_ne_zero N)
  have hne : ((N : ℝ) + 1) * goldenRatio ≠ ((v : ℝ) + 1) := by
    have := hirr.ne_nat (v + 1)
    push_cast at this ⊢
    simpa using this
  constructor
  · intro h
    have h1 : ((v : ℝ) + 1) / goldenRatio < (N : ℝ) + 1 := by
      have hlt := (Nat.floor_lt hpos).mp (Nat.lt_succ_of_le h)
      push_cast at hlt; linarith
    have h2 : ((v : ℝ) + 1) < ((N : ℝ) + 1) * goldenRatio := by
      rw [div_lt_iff₀ hφ] at h1; linarith
    have h4 : (v + 1 : ℕ) ≤ ⌊((N : ℝ) + 1) * goldenRatio⌋₊ := by
      rw [Nat.le_floor_iff hNφ]; push_cast; linarith
    omega
  · intro h
    have h4 : (v + 1 : ℕ) ≤ ⌊((N : ℝ) + 1) * goldenRatio⌋₊ := by omega
    have h3 : ((v : ℝ) + 1) ≤ ((N : ℝ) + 1) * goldenRatio := by
      have := (Nat.le_floor_iff hNφ).mp h4; push_cast at this; linarith
    have h2 : ((v : ℝ) + 1) < ((N : ℝ) + 1) * goldenRatio :=
      lt_of_le_of_ne h3 (Ne.symm hne)
    have h1 : ((v : ℝ) + 1) / goldenRatio < ((N + 1 : ℕ) : ℝ) := by
      rw [div_lt_iff₀ hφ]; push_cast; linarith
    have := (Nat.floor_lt hpos).mpr h1
    omega

end D5.S1.Phase.GoldenBeattyCount
