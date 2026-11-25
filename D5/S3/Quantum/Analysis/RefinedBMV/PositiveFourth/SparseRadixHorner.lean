/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveFourth/SparseRadixHorner
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Evaluate sparse radix data by merging adjacent sorted index intervals. -/

import D5.S3.Quantum.Analysis.RefinedBMV.PositiveFourth.AffineRadixIdentity

/-! Balanced evaluation keeps each intermediate value within the span of
its group before merging it with its neighbor. -/

namespace RefinedBMV.ThreeBlockGram.PositiveSpectrum.AffineRadixIdentity

open RefinedBMV.DividedDifference.SparseExpansion

private def pairValue (bits : ℕ) (a : ℕ × ℤ) : ℤ := a.2 <<< (bits * a.1)

private def mergePair (bits : ℕ) (a c : ℕ × ℤ) : ℕ × ℤ :=
  let k := min a.1 c.1
  (k, (a.2 <<< (bits * (a.1 - k))) + (c.2 <<< (bits * (c.1 - k))))

private theorem pairValue_mergePair (bits : ℕ) (a c : ℕ × ℤ) :
    pairValue bits (mergePair bits a c) = pairValue bits a + pairValue bits c := by
  simp only [pairValue, mergePair, Int.shiftLeft_eq, pow_mul, add_mul, mul_assoc, ← pow_add]
  rw [Nat.sub_add_cancel (min_le_left _ _), Nat.sub_add_cancel (min_le_right _ _)]

private def mergePass (bits : ℕ) : List (ℕ × ℤ) → List (ℕ × ℤ)
  | a :: c :: tail => mergePair bits a c :: mergePass bits tail
  | tail => tail

private theorem mergePass_value (bits : ℕ) : ∀ rows : List (ℕ × ℤ),
    ((mergePass bits rows).map (pairValue bits)).sum = (rows.map (pairValue bits)).sum
  | [] => rfl
  | [_] => rfl
  | a :: c :: tail => by
    simp only [mergePass, List.map_cons, List.sum_cons, pairValue_mergePair,
      mergePass_value bits tail, add_assoc]

private def mergeRounds (bits : ℕ) : ℕ → List (ℕ × ℤ) → List (ℕ × ℤ)
  | 0, rows => rows
  | n + 1, rows => mergeRounds bits n (mergePass bits rows)

private theorem mergeRounds_value (bits n : ℕ) (rows : List (ℕ × ℤ)) :
    ((mergeRounds bits n rows).map (pairValue bits)).sum =
      (rows.map (pairValue bits)).sum := by
  induction n generalizing rows with
  | zero => rfl
  | succ n ih => rw [mergeRounds, ih, mergePass_value]

/-- Evaluate adjacent groups in balanced rounds with signed shifts. -/
def packedPowers (bits : ℕ) (entries : List (ℕ × ℤ)) : ℤ :=
  ((mergeRounds bits (entries.length.log2 + 1) entries).map
    (pairValue bits)).sum

theorem packedPowers_eq (bits : ℕ) (entries : List (ℕ × ℤ)) :
    packedPowers bits entries = (entries.map fun (k, a) => a * ((2 : ℤ)^bits) ^ k).sum := by
  rw [packedPowers, mergeRounds_value]
  apply congrArg List.sum
  apply List.map_congr_left
  rintro ⟨k, a⟩ _
  simp only [pairValue, Int.shiftLeft_eq, pow_mul]

end RefinedBMV.ThreeBlockGram.PositiveSpectrum.AffineRadixIdentity
