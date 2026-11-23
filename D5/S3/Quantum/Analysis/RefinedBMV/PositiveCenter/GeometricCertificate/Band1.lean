import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.GeometricCertificate.Verification

/-! # Finite verification for one band of the left strip -/

namespace RefinedBMV.PositiveCenter.LocalTaylor

open private band checkCover from
  D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.LeftStripGeometricCertificate

-- Each successful leaf is checked with the centered enclosure arithmetic.
set_option maxRecDepth 12000 in
set_option maxHeartbeats 40000000 in
theorem band1 : checkCover 5 (band 1 (5/4)) = true := by
  verify_cover "00000 00001 0001 00100 00101 0011 01000 01001 0101 01100 01101 0111 10000 10001 10010 10011 10100 10101 10110 10111 11000 11001 1101 11100 11101 1111"

end RefinedBMV.PositiveCenter.LocalTaylor
