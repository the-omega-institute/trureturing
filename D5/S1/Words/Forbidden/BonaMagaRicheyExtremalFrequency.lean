/- GID: D5/S1/Words/Forbidden/BonaMagaRicheyExtremalFrequency
   generality: I
   mirror-B: D5/B/S1/Words/Forbidden/BonaMagaRicheyExtremalFrequency
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S1/Words/Forbidden/BonaMagaRicheyExtremalFrequency.claim; result=D5/S1/Words/Forbidden/BonaMagaRicheyExtremalFrequency.result; claim=D5/S1/Words/Forbidden/BonaMagaRicheyExtremalFrequency.claim
   digest: The universal extremal-frequency assertion fails at the one-letter word. -/

import D5.S1.Words.Forbidden.BalancedBordersHalfFrequency

open Filter
open scoped Topology

namespace D5.S1.Words.Forbidden.BonaMagaRicheyExtremalFrequency

open D5.S1.Words.Forbidden.ForbiddenWordCounting

/-- The proposed word, with truncated subtraction irrelevant when k is positive. -/
def proposedWord (k : ℕ) : List Bool := true :: List.replicate (k - 1) false

/-- Actual limits exist for the candidate and every word of the same length. -/
def MaximizesFrequency (k : ℕ) (u : List Bool) : Prop :=
  u.length = k ∧ ∃ r : ℝ, Tendsto (rho u) atTop (𝓝 r) ∧
    ∀ v : List Bool, v.length = k →
      ∃ s : ℝ, Tendsto (rho v) atTop (𝓝 s) ∧ s ≤ r

/-- Both proposed optimizers, over the entire positive-length binary-word domain. -/
def claim : Prop :=
  ∀ k : ℕ, 1 ≤ k →
    MaximizesFrequency k (proposedWord k) ∧
      MaximizesFrequency k (proposedWord k).reverse

private theorem singleton_tendsto (b : Bool) :
    Tendsto (rho [b]) atTop (𝓝 (if b then 0 else 1 : ℝ)) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  exact (BalancedBordersHalfFrequency.rho_singleton hn).symm

theorem result : ¬ claim := by
  intro h
  obtain ⟨_, r, hr, hmax⟩ := (h 1 (by norm_num)).1
  have hzero : r = 0 := tendsto_nhds_unique
    (by simpa only [proposedWord, Nat.sub_self, List.replicate_zero] using hr)
    (singleton_tendsto true)
  obtain ⟨s, hs, hle⟩ := hmax [false] (by simp)
  have hone : s = 1 := tendsto_nhds_unique hs (singleton_tendsto false)
  have hstrict : (0 : ℝ) < 1 := by norm_num
  exact (not_le_of_gt hstrict) (by simpa only [hzero, hone] using hle)

end D5.S1.Words.Forbidden.BonaMagaRicheyExtremalFrequency
