import D5.S3.Quantum.Analysis.RefinedBMV.PositiveFourth.AffineMixedMiddleSlicedRow8
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveFourth.AffinePackedSweepBlocks

namespace RefinedBMV.ThreeBlockGram.PositiveSpectrum.GroupedAffineMasks.MixedMiddle

open DimThree.PackedCheck (polynomialMask)
open private masked from
  D5.S3.Quantum.Analysis.RefinedBMV.PositiveFourth.GroupedAffineMasks
open private shiftSweep from
  D5.S3.Quantum.Analysis.RefinedBMV.PositiveFourth.AffinePackedSweep

set_option maxRecDepth 30000 in
set_option maxHeartbeats 5000000 in
theorem checkedRow8FirstEightPrefixes :
    shiftSweep 6431 (masked (polynomialMask 6430 679)) 8
      (slicedRow8Weights.map Prod.snd).sum slicedRow8Weights = true := by
  decide +kernel

#print axioms checkedRow8FirstEightPrefixes

end RefinedBMV.ThreeBlockGram.PositiveSpectrum.GroupedAffineMasks.MixedMiddle
