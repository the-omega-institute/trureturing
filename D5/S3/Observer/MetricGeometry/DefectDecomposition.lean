/- GID: D5/S3/Observer/MetricGeometry/DefectDecomposition
   generality: G
   mirror-B: D5/B/S3/Observer/MetricGeometry/DefectDecomposition
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A Lipschitz update splits the total projection defect into two component defects. -/

import Mathlib.Topology.MetricSpace.Lipschitz

namespace D5.S3.Observer.MetricGeometry.DefectDecomposition

/-- The total defect of the projected update is bounded by the update-naturality
defect plus the Lipschitz-amplified diagonal-projection defect. -/
theorem defect_decomposition
    {HighTable LowTable HighOutput LowOutput : Type*}
    [PseudoMetricSpace LowOutput]
    (diagHigh : HighTable → HighOutput)
    (diagLow : LowTable → LowOutput)
    (projectTable : HighTable → LowTable)
    (projectOutput : HighOutput → LowOutput)
    (updateHigh : HighOutput → HighOutput)
    (updateLow : LowOutput → LowOutput)
    (K : NNReal)
    (hupdate : LipschitzWith K updateLow)
    (E : HighTable) :
    dist (projectOutput (updateHigh (diagHigh E)))
        (updateLow (diagLow (projectTable E))) ≤
      dist (projectOutput (updateHigh (diagHigh E)))
          (updateLow (projectOutput (diagHigh E))) +
        K * dist (projectOutput (diagHigh E)) (diagLow (projectTable E)) := by
  calc
    dist (projectOutput (updateHigh (diagHigh E)))
        (updateLow (diagLow (projectTable E))) ≤
      dist (projectOutput (updateHigh (diagHigh E)))
          (updateLow (projectOutput (diagHigh E))) +
        dist (updateLow (projectOutput (diagHigh E)))
          (updateLow (diagLow (projectTable E))) := dist_triangle _ _ _
    _ ≤ dist (projectOutput (updateHigh (diagHigh E)))
          (updateLow (projectOutput (diagHigh E))) +
        K * dist (projectOutput (diagHigh E)) (diagLow (projectTable E)) :=
      add_le_add_right (hupdate.dist_le_mul _ _) _

end D5.S3.Observer.MetricGeometry.DefectDecomposition
