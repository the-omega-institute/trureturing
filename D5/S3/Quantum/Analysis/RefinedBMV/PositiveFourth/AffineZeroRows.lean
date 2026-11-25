/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveFourth/AffineZeroRows
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A row with identically zero weights passes every affine prefix check. -/

import D5.S3.Quantum.Analysis.RefinedBMV.PositiveFourth.AffinePackedSweep

/-! An annihilating chain preserves an all-zero row. -/

namespace RefinedBMV.ThreeBlockGram.PositiveSpectrum.GroupedAffineMasks

open DimThree.PackedCheck (polynomialMask)
open private masked from
  D5.S3.Quantum.Analysis.RefinedBMV.PositiveFourth.GroupedAffineMasks
open private shiftFactor shiftRow updated shiftSweep from
  D5.S3.Quantum.Analysis.RefinedBMV.PositiveFourth.AffinePackedSweep

private def zeroWeights (ws : List (AffineRate × ℤ)) : Bool :=
  ws.all fun pair => pair.2 == 0

private theorem zeroWeights_cons {r : AffineRate} {w : ℤ} {ws : List (AffineRate × ℤ)}
    (hz : zeroWeights ((r, w) :: ws) = true) : w = 0 ∧ zeroWeights ws = true := by
  simpa only [zeroWeights, List.all_cons, Bool.and_eq_true, Prod.snd, beq_iff_eq] using hz

private theorem updated_zero (s : ℕ) (a : AffineRate)
    (ws : List (AffineRate × ℤ)) (hz : zeroWeights ws = true) :
    updated s a ws = (0, ws) := by
  induction ws with
  | nil => rfl
  | cons pair tail ih =>
    obtain ⟨r, w⟩ := pair
    obtain ⟨rfl, htail⟩ := zeroWeights_cons hz
    simp [updated, ih htail, shiftFactor, Int.shiftLeft_eq]

private theorem sum_zero (ws : List (AffineRate × ℤ)) (hz : zeroWeights ws = true) :
    (ws.map Prod.snd).sum = 0 := by
  induction ws with
  | nil => rfl
  | cons pair tail ih =>
    obtain ⟨r, w⟩ := pair
    obtain ⟨rfl, htail⟩ := zeroWeights_cons hz
    simp [ih htail]

private theorem shiftSweep_zero (s : ℕ) (test : ℤ → Bool) (h0 : test 0 = true)
    (steps : ℕ) (ws : List (AffineRate × ℤ)) (hz : zeroWeights ws = true) :
    shiftSweep s test steps 0 ws = true := by
  induction steps generalizing ws with
  | zero => rfl
  | succ n ih =>
    cases ws with
    | nil => rfl
    | cons pair tail =>
      obtain ⟨r, w⟩ := pair
      have htail := (zeroWeights_cons hz).2
      simp [shiftSweep, h0, updated_zero s r tail htail, ih tail htail]

/-- Decide whether the packed weights vanish at this row. -/
def Certificate.zeroShiftRow (certificate : Certificate) (width row : ℕ) : Bool :=
  zeroWeights (shiftRow certificate (width + 1) row)

theorem Certificate.checkShiftRow_of_zeroShiftRow
    (certificate : Certificate) (width digits row : ℕ)
    (hz : certificate.zeroShiftRow width row = true) :
    certificate.checkShiftRow width digits row = true := by
  unfold Certificate.zeroShiftRow at hz
  dsimp only [Certificate.checkShiftRow]
  rw [sum_zero _ hz]
  exact shiftSweep_zero _ _ (by simp [masked]) _ _ hz

end RefinedBMV.ThreeBlockGram.PositiveSpectrum.GroupedAffineMasks
