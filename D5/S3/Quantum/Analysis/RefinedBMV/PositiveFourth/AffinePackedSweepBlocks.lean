/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveFourth/AffinePackedSweepBlocks
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Split a packed affine sign sweep at a checked intermediate state. -/

import D5.S3.Quantum.Analysis.RefinedBMV.PositiveFourth.AffinePackedSweep

namespace RefinedBMV.ThreeBlockGram.PositiveSpectrum.GroupedAffineMasks

open private shiftSweep updated from
  D5.S3.Quantum.Analysis.RefinedBMV.PositiveFourth.AffinePackedSweep

def advanceSweep (s : ℕ) :
    ℕ → ℤ → List (AffineRate × ℤ) → ℤ × List (AffineRate × ℤ)
  | 0, total, ws => (total, ws)
  | _ + 1, _, [] => (0, [])
  | n + 1, _, (a, _) :: ws =>
    let next := updated s a ws
    advanceSweep s n next.1 next.2

theorem shiftSweep_add (s : ℕ) (test : ℤ → Bool) (n m : ℕ)
    (total : ℤ) (ws : List (AffineRate × ℤ)) :
    shiftSweep s test (n + m) total ws =
      (shiftSweep s test n total ws &&
        let next := advanceSweep s n total ws
        shiftSweep s test m next.1 next.2) := by
  induction n generalizing total ws with
  | zero =>
    simp [advanceSweep, shiftSweep]
  | succ n ih =>
    cases ws with
    | nil =>
      cases m <;> simp [Nat.succ_add, advanceSweep, shiftSweep]
    | cons w ws =>
      obtain ⟨a, weight⟩ := w
      simp only [Nat.succ_add, advanceSweep, shiftSweep, ih, Bool.and_assoc]

end RefinedBMV.ThreeBlockGram.PositiveSpectrum.GroupedAffineMasks
