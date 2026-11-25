import D5.S3.Quantum.Analysis.RefinedBMV.PositiveFourth.AffineMixedMiddleSlicedRow8

namespace RefinedBMV.ThreeBlockGram.PositiveSpectrum.GroupedAffineMasks.MixedMiddle

open DimThree.PackedCheck (polynomialMask)
open private masked from
  D5.S3.Quantum.Analysis.RefinedBMV.PositiveFourth.GroupedAffineMasks
open private shiftSweep from
  D5.S3.Quantum.Analysis.RefinedBMV.PositiveFourth.AffinePackedSweep

set_option maxRecDepth 30000 in
set_option maxHeartbeats 5000000 in
private theorem exactRowSweep :
    shiftSweep 6431 (masked (polynomialMask 6430 679)) certificate.rootsV.length
      (slicedRow8Weights.map Prod.snd).sum slicedRow8Weights = true := by
  decide +kernel

set_option maxRecDepth 30000 in
theorem checkedSlicedPackedRow8 : certificate.checkShiftRow 6430 679 8 = true := by
  simpa only [Certificate.checkShiftRow, show 6430 + 1 = 6431 by decide,
    checkedSlicedRow8Weights] using exactRowSweep

#print axioms checkedSlicedPackedRow8

end RefinedBMV.ThreeBlockGram.PositiveSpectrum.GroupedAffineMasks.MixedMiddle
