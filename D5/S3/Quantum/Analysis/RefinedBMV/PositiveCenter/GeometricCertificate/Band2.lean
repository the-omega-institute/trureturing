import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.GeometricCertificate.Verification

/-! # Finite verification for one band of the left strip -/

namespace RefinedBMV.PositiveCenter.LocalTaylor

open private band checkCover from
  D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.LeftStripGeometricCertificate

-- Each successful leaf is checked with the centered enclosure arithmetic.
set_option maxRecDepth 12000 in
set_option maxHeartbeats 40000000 in
theorem band2 : checkCover 5 (band (5/4) (3/2)) = true := by
  verify_cover "0000 0001 0010 0011 0100 0101 0110 0111 1000 1001 1010 1011 1100 1101 1110 1111"

end RefinedBMV.PositiveCenter.LocalTaylor
