/- GID: D5/S3/Quantum/Analysis/RefinedBMV/ThreeSpectrum/GroupedData
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The cleared discriminant coefficient table grouped by affine rates. -/

import D5.S3.Quantum.Analysis.RefinedBMV.ThreeSpectrum.GroupedColumns0
import D5.S3.Quantum.Analysis.RefinedBMV.ThreeSpectrum.GroupedColumns1
import D5.S3.Quantum.Analysis.RefinedBMV.ThreeSpectrum.GroupedColumns2
import D5.S3.Quantum.Analysis.RefinedBMV.ThreeSpectrum.GroupedColumns3

/-! Integer coefficient data for the refined BMV discriminant. -/

/- Generated from bmv-positive-three-spectra-discriminant.py (SHA-256 67c59b361cb44b2a297da090f2dbc65e1056feadb148050596a5df317feea9b2). -/

namespace RefinedBMV.DividedDifference.SparseExpansion.GroupedMasks

/-- Exact sparse discriminant grouped by the original gap exponents.
Both root lists use the key (intercept + slope, slope, intercept). -/
def quartic : Certificate where
  rootsX := [(12, 3), (12, 4), (12, 5), (15, 3), (12, 6), (15, 4), (12, 7), (15, 5), (12, 8), (18, 3), (15, 6), (18, 4), (15, 7), (18, 5), (15, 8), (21, 3), (18, 6), (15, 9), (21, 4), (18, 7), (21, 5), (18, 8), (21, 6), (18, 9), (24, 4), (21, 7), (18, 10), (24, 5), (21, 8), (24, 6), (21, 9), (24, 7), (21, 10), (27, 5), (24, 8), (21, 11), (27, 6), (24, 9), (27, 7), (24, 10), (27, 8), (24, 11), (30, 6), (27, 9), (24, 12), (30, 7), (27, 10), (30, 8), (27, 11), (30, 9), (27, 12), (33, 7), (30, 10), (33, 8), (30, 11), (33, 9), (30, 12), (33, 10), (36, 8), (33, 11), (36, 9), (33, 12), (36, 10), (36, 11), (36, 12)]
  columns := columns0 ++ columns1 ++ columns2 ++ columns3

end RefinedBMV.DividedDifference.SparseExpansion.GroupedMasks
