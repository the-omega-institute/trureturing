import D5.S3.Quantum.Analysis.RefinedBMV.PositiveFourth.AffineAxisFirstData
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveFourth.AffineZeroRows

namespace RefinedBMV.ThreeBlockGram.PositiveSpectrum.GroupedAffineMasks.AxisFirst

set_option maxRecDepth 30000 in
set_option maxHeartbeats 5000000 in
theorem checkedPackedRow5 : certificate.checkShiftRow 2157 251 5 = true := by
  apply certificate.checkShiftRow_of_zeroShiftRow
  decide +kernel

end RefinedBMV.ThreeBlockGram.PositiveSpectrum.GroupedAffineMasks.AxisFirst
