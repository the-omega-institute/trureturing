import D5.S3.Quantum.Analysis.RefinedBMV.PositiveFourth.AffineAxisMiddleData
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveFourth.AffineZeroRows

/-! The first eight affine rows vanish. -/

namespace RefinedBMV.ThreeBlockGram.PositiveSpectrum.GroupedAffineMasks.AxisMiddle

set_option maxRecDepth 30000 in
set_option maxHeartbeats 5000000 in
theorem checkedZeroRow0 : certificate.checkShiftRow 1578 193 0 = true := by
  apply certificate.checkShiftRow_of_zeroShiftRow
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 5000000 in
theorem checkedZeroRow1 : certificate.checkShiftRow 1578 193 1 = true := by
  apply certificate.checkShiftRow_of_zeroShiftRow
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 5000000 in
theorem checkedZeroRow2 : certificate.checkShiftRow 1578 193 2 = true := by
  apply certificate.checkShiftRow_of_zeroShiftRow
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 5000000 in
theorem checkedZeroRow3 : certificate.checkShiftRow 1578 193 3 = true := by
  apply certificate.checkShiftRow_of_zeroShiftRow
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 5000000 in
theorem checkedZeroRow4 : certificate.checkShiftRow 1578 193 4 = true := by
  apply certificate.checkShiftRow_of_zeroShiftRow
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 5000000 in
theorem checkedZeroRow5 : certificate.checkShiftRow 1578 193 5 = true := by
  apply certificate.checkShiftRow_of_zeroShiftRow
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 5000000 in
theorem checkedZeroRow6 : certificate.checkShiftRow 1578 193 6 = true := by
  apply certificate.checkShiftRow_of_zeroShiftRow
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 5000000 in
theorem checkedZeroRow7 : certificate.checkShiftRow 1578 193 7 = true := by
  apply certificate.checkShiftRow_of_zeroShiftRow
  decide +kernel

end RefinedBMV.ThreeBlockGram.PositiveSpectrum.GroupedAffineMasks.AxisMiddle
