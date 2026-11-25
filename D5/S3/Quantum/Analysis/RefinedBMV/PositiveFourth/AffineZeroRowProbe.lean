import D5.S3.Quantum.Analysis.RefinedBMV.PositiveFourth.AffineAxisMiddleData
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveFourth.AffineZeroRows

/-! A zero row needs no successive prefix computations. -/

open RefinedBMV.ThreeBlockGram.PositiveSpectrum.GroupedAffineMasks.AxisMiddle

set_option maxRecDepth 30000 in
set_option maxHeartbeats 5000000 in
theorem affineZeroRowProbe : certificate.checkShiftRow 1578 193 0 = true := by
  apply certificate.checkShiftRow_of_zeroShiftRow
  decide +kernel

#print axioms affineZeroRowProbe
