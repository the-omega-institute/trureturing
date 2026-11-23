import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.GeometricCertificate.Verification

/-! # Finite verification for one band of the left strip -/

namespace RefinedBMV.PositiveCenter.LocalTaylor

open private band checkCover from
  D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.LeftStripGeometricCertificate

-- Each successful leaf is checked with the centered enclosure arithmetic.
set_option maxRecDepth 12000 in
set_option maxHeartbeats 40000000 in
theorem band4 : checkCover 5 (band 2 (5/2)) = true := by
  verify_cover "00000 00001 00010 00011 0010 0011 0100 01010 01011 0110 01110 01111 10000 10001 10010 10011 10100 10101 10110 10111 11000 11001 11010 11011 11100 11101 11110 11111"

end RefinedBMV.PositiveCenter.LocalTaylor
