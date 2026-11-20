import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Data
/-! Successor lists depend on the source row at each residual budget. -/
namespace Reg.D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Data
open _root_.D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Data
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem successors_vary : ∀ d : Fin 3,
    successors (fun _ => 0) d.val ≠ successors ![0,1,0,1,0,1] d.val := by
  decide +kernel
end Reg.D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Data
