import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.GeometricCertificate.Verification

/-! # Finite verification for one band of the left strip -/

namespace RefinedBMV.PositiveCenter.LocalTaylor

open private band check checkCover Box from
  D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.LeftStripGeometricCertificate

private def bandBox : Box := band (5 / 4) (3 / 2)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 2500000 in
private theorem leaf0000 : check (left_strip_box bandBox "0000") = true := by
  verify_left_strip_leaf

set_option maxRecDepth 12000 in
set_option maxHeartbeats 2500000 in
private theorem leaf0001 : check (left_strip_box bandBox "0001") = true := by
  verify_left_strip_leaf

set_option maxRecDepth 12000 in
set_option maxHeartbeats 2500000 in
private theorem leaf0010 : check (left_strip_box bandBox "0010") = true := by
  verify_left_strip_leaf

set_option maxRecDepth 12000 in
set_option maxHeartbeats 2500000 in
private theorem leaf0011 : check (left_strip_box bandBox "0011") = true := by
  verify_left_strip_leaf

set_option maxRecDepth 12000 in
set_option maxHeartbeats 2500000 in
private theorem leaf0100 : check (left_strip_box bandBox "0100") = true := by
  verify_left_strip_leaf

set_option maxRecDepth 12000 in
set_option maxHeartbeats 2500000 in
private theorem leaf0101 : check (left_strip_box bandBox "0101") = true := by
  verify_left_strip_leaf

set_option maxRecDepth 12000 in
set_option maxHeartbeats 2500000 in
private theorem leaf0110 : check (left_strip_box bandBox "0110") = true := by
  verify_left_strip_leaf

set_option maxRecDepth 12000 in
set_option maxHeartbeats 2500000 in
private theorem leaf0111 : check (left_strip_box bandBox "0111") = true := by
  verify_left_strip_leaf

set_option maxRecDepth 12000 in
set_option maxHeartbeats 2500000 in
private theorem leaf1000 : check (left_strip_box bandBox "1000") = true := by
  verify_left_strip_leaf

set_option maxRecDepth 12000 in
set_option maxHeartbeats 2500000 in
private theorem leaf1001 : check (left_strip_box bandBox "1001") = true := by
  verify_left_strip_leaf

set_option maxRecDepth 12000 in
set_option maxHeartbeats 2500000 in
private theorem leaf1010 : check (left_strip_box bandBox "1010") = true := by
  verify_left_strip_leaf

set_option maxRecDepth 12000 in
set_option maxHeartbeats 2500000 in
private theorem leaf1011 : check (left_strip_box bandBox "1011") = true := by
  verify_left_strip_leaf

set_option maxRecDepth 12000 in
set_option maxHeartbeats 2500000 in
private theorem leaf1100 : check (left_strip_box bandBox "1100") = true := by
  verify_left_strip_leaf

set_option maxRecDepth 12000 in
set_option maxHeartbeats 2500000 in
private theorem leaf1101 : check (left_strip_box bandBox "1101") = true := by
  verify_left_strip_leaf

set_option maxRecDepth 12000 in
set_option maxHeartbeats 2500000 in
private theorem leaf1110 : check (left_strip_box bandBox "1110") = true := by
  verify_left_strip_leaf

set_option maxRecDepth 12000 in
set_option maxHeartbeats 2500000 in
private theorem leaf1111 : check (left_strip_box bandBox "1111") = true := by
  verify_left_strip_leaf

theorem band2 : checkCover 5 (band (5 / 4) (3 / 2)) = true :=
  (coverSplit
    (coverSplit
      (coverSplit
        (coverSplit
          (coverLeaf leaf0000)
          (coverLeaf leaf0001))
        (coverSplit
          (coverLeaf leaf0010)
          (coverLeaf leaf0011)))
      (coverSplit
        (coverSplit
          (coverLeaf leaf0100)
          (coverLeaf leaf0101))
        (coverSplit
          (coverLeaf leaf0110)
          (coverLeaf leaf0111))))
    (coverSplit
      (coverSplit
        (coverSplit
          (coverLeaf leaf1000)
          (coverLeaf leaf1001))
        (coverSplit
          (coverLeaf leaf1010)
          (coverLeaf leaf1011)))
      (coverSplit
        (coverSplit
          (coverLeaf leaf1100)
          (coverLeaf leaf1101))
        (coverSplit
          (coverLeaf leaf1110)
          (coverLeaf leaf1111)))))

end RefinedBMV.PositiveCenter.LocalTaylor
