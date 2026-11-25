import D5.S3.Quantum.Analysis.RefinedBMV.PositiveFourth.AffineMixedMiddleSlicedRow8Part0
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveFourth.AffineMixedMiddleSlicedRow8Part1
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveFourth.AffineMixedMiddleSlicedRow8Part2
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveFourth.AffineMixedMiddleSlicedRow8Part3
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveFourth.AffineMixedMiddleSlicedRow8Part4
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveFourth.AffineMixedMiddleSlicedRow8Part5
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveFourth.AffineMixedMiddleSlicedRow8Part6
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveFourth.AffineMixedMiddleSlicedRow8Part7
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveFourth.AffineMixedMiddleSlicedRow8Part8
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveFourth.AffineMixedMiddleSlicedRow8Part9
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveFourth.AffineMixedMiddleSlicedRow8Part10
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveFourth.AffineMixedMiddleSlicedRow8Part11
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveFourth.AffineMixedMiddleSlicedRow8Part12
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveFourth.AffineMixedMiddleSlicedRow8Part13
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveFourth.AffineMixedMiddleSlicedRow8Part14
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveFourth.AffineMixedMiddleSlicedRow8Part15
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveFourth.AffineMixedMiddleSlicedRow8Part16
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveFourth.AffineMixedMiddleSlicedRow8Part17
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveFourth.AffineMixedMiddleSlicedRow8Part18
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveFourth.AffineMixedMiddleSlicedRow8Part19
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveFourth.AffineMixedMiddleSlicedRow8Part20
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveFourth.AffineMixedMiddleSlicedRow8Part21
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveFourth.AffineMixedMiddleSlicedRow8Part22
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveFourth.AffineMixedMiddleSlicedRow8Part23
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveFourth.AffineMixedMiddleSlicedRow8Part24

namespace RefinedBMV.ThreeBlockGram.PositiveSpectrum.GroupedAffineMasks.MixedMiddle

open private shiftRow from D5.S3.Quantum.Analysis.RefinedBMV.PositiveFourth.AffinePackedSweep

def slicedRow8Weights : List (AffineRate × ℤ) :=
    weightRow8Slice0 ++
    weightRow8Slice1 ++
    weightRow8Slice2 ++
    weightRow8Slice3 ++
    weightRow8Slice4 ++
    weightRow8Slice5 ++
    weightRow8Slice6 ++
    weightRow8Slice7 ++
    weightRow8Slice8 ++
    weightRow8Slice9 ++
    weightRow8Slice10 ++
    weightRow8Slice11 ++
    weightRow8Slice12 ++
    weightRow8Slice13 ++
    weightRow8Slice14 ++
    weightRow8Slice15 ++
    weightRow8Slice16 ++
    weightRow8Slice17 ++
    weightRow8Slice18 ++
    weightRow8Slice19 ++
    weightRow8Slice20 ++
    weightRow8Slice21 ++
    weightRow8Slice22 ++
    weightRow8Slice23 ++
    weightRow8Slice24

set_option maxRecDepth 30000 in
set_option maxHeartbeats 5000000 in
theorem checkedSlicedRow8Weights :
    shiftRow certificate 6431 8 = slicedRow8Weights := by
  calc
    shiftRow certificate 6431 8 =
        shiftRowSlices certificate 6431 8 0 [16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 11] := by
      symm
      simpa only [List.drop_zero] using
        shiftRowSlices_eq_drop certificate 6431 8 0 [16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 11] (by decide +kernel)
    _ = slicedRow8Weights := by
      simp only [shiftRowSlices, Nat.reduceAdd, slicedRow8Weights, List.append_nil, List.append_assoc,
        checkedWeightRow8Slice0,
      checkedWeightRow8Slice1,
      checkedWeightRow8Slice2,
      checkedWeightRow8Slice3,
      checkedWeightRow8Slice4,
      checkedWeightRow8Slice5,
      checkedWeightRow8Slice6,
      checkedWeightRow8Slice7,
      checkedWeightRow8Slice8,
      checkedWeightRow8Slice9,
      checkedWeightRow8Slice10,
      checkedWeightRow8Slice11,
      checkedWeightRow8Slice12,
      checkedWeightRow8Slice13,
      checkedWeightRow8Slice14,
      checkedWeightRow8Slice15,
      checkedWeightRow8Slice16,
      checkedWeightRow8Slice17,
      checkedWeightRow8Slice18,
      checkedWeightRow8Slice19,
      checkedWeightRow8Slice20,
      checkedWeightRow8Slice21,
      checkedWeightRow8Slice22,
      checkedWeightRow8Slice23,
      checkedWeightRow8Slice24]

#print axioms checkedSlicedRow8Weights

end RefinedBMV.ThreeBlockGram.PositiveSpectrum.GroupedAffineMasks.MixedMiddle
