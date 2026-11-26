/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveCenter/GeometricCertificate/Band5
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact kernel checks for band 5 of the left geometric strip. -/

import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.GeometricCertificate.CachedVerification

/-! # Finite verification for one band of the left strip -/

namespace RefinedBMV.PositiveCenter.LocalTaylor

open private band checkCover Box from
  D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.LeftStripGeometricCertificate

private def bandBox : Box := band (5 / 2) 3

set_option maxRecDepth 12000 in
set_option maxHeartbeats 16000000 in
private theorem quarter00 : checkCover 3 (left_strip_box bandBox "00") = true := by
  verify_left_strip_cover_cached ["00", "010", "011", "100", "101", "110", "111"]

set_option maxRecDepth 12000 in
set_option maxHeartbeats 16000000 in
private theorem quarter01 : checkCover 3 (left_strip_box bandBox "01") = true := by
  verify_left_strip_cover_cached ["000", "001", "010", "011", "100", "101", "110", "111"]

set_option maxRecDepth 12000 in
set_option maxHeartbeats 16000000 in
private theorem quarter10 : checkCover 3 (left_strip_box bandBox "10") = true := by
  verify_left_strip_cover_cached ["000", "001", "010", "011", "100", "101", "110", "111"]

set_option maxRecDepth 12000 in
set_option maxHeartbeats 16000000 in
private theorem quarter11 : checkCover 3 (left_strip_box bandBox "11") = true := by
  verify_left_strip_cover_cached ["000", "001", "010", "011", "100", "101", "110", "111"]

theorem band5 : checkCover 5 (band (5 / 2) 3) = true :=
  coverSplit (coverSplit quarter00 quarter01) (coverSplit quarter10 quarter11)

end RefinedBMV.PositiveCenter.LocalTaylor
