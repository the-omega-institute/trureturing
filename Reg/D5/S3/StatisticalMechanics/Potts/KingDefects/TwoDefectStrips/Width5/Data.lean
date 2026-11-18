import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width5.Data

/-! Shared observational dependence for the successor-list registrations. -/
namespace Reg.D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width5.Data
open _root_.D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width5.Data
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem successors_vary : successors (fun _ => 0) 0 ≠ successors ![0,1,0,1,0] 0 := by
  decide +kernel
end Reg.D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width5.Data
