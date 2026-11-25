import D5.S3.Quantum.Analysis.RefinedBMV.PositiveFourth.AffineAxisLastData
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveFourth.AffineZeroRows

namespace RefinedBMV.ThreeBlockGram.PositiveSpectrum.GroupedAffineMasks.AxisLast

set_option maxRecDepth 30000 in
set_option maxHeartbeats 5000000 in
theorem checkedPackedRow1 : certificate.checkShiftRow 2157 251 1 = true := by
  apply certificate.checkShiftRow_of_zeroShiftRow
  decide +kernel

end RefinedBMV.ThreeBlockGram.PositiveSpectrum.GroupedAffineMasks.AxisLast
