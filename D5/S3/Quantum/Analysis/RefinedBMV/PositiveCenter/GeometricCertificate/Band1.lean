import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.GeometricCertificate.Verification

/-! # Finite verification for one band of the left strip -/

namespace RefinedBMV.PositiveCenter.LocalTaylor

open private band check checkCover Box from
  D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.LeftStripGeometricCertificate

private def bandBox : Box := band 1 (5 / 4)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 2500000 in
private theorem leaf00000 : check (left_strip_box bandBox "00000") = true := by
  verify_left_strip_leaf

set_option maxRecDepth 12000 in
set_option maxHeartbeats 2500000 in
private theorem leaf00001 : check (left_strip_box bandBox "00001") = true := by
  verify_left_strip_leaf

set_option maxRecDepth 12000 in
set_option maxHeartbeats 2500000 in
private theorem leaf0001 : check (left_strip_box bandBox "0001") = true := by
  verify_left_strip_leaf

set_option maxRecDepth 12000 in
set_option maxHeartbeats 2500000 in
private theorem leaf00100 : check (left_strip_box bandBox "00100") = true := by
  verify_left_strip_leaf

set_option maxRecDepth 12000 in
set_option maxHeartbeats 2500000 in
private theorem leaf00101 : check (left_strip_box bandBox "00101") = true := by
  verify_left_strip_leaf

set_option maxRecDepth 12000 in
set_option maxHeartbeats 2500000 in
private theorem leaf0011 : check (left_strip_box bandBox "0011") = true := by
  verify_left_strip_leaf

set_option maxRecDepth 12000 in
set_option maxHeartbeats 2500000 in
private theorem leaf01000 : check (left_strip_box bandBox "01000") = true := by
  verify_left_strip_leaf

set_option maxRecDepth 12000 in
set_option maxHeartbeats 2500000 in
private theorem leaf01001 : check (left_strip_box bandBox "01001") = true := by
  verify_left_strip_leaf

set_option maxRecDepth 12000 in
set_option maxHeartbeats 2500000 in
private theorem leaf0101 : check (left_strip_box bandBox "0101") = true := by
  verify_left_strip_leaf

set_option maxRecDepth 12000 in
set_option maxHeartbeats 2500000 in
private theorem leaf01100 : check (left_strip_box bandBox "01100") = true := by
  verify_left_strip_leaf

set_option maxRecDepth 12000 in
set_option maxHeartbeats 2500000 in
private theorem leaf01101 : check (left_strip_box bandBox "01101") = true := by
  verify_left_strip_leaf

set_option maxRecDepth 12000 in
set_option maxHeartbeats 2500000 in
private theorem leaf0111 : check (left_strip_box bandBox "0111") = true := by
  verify_left_strip_leaf

set_option maxRecDepth 12000 in
set_option maxHeartbeats 2500000 in
private theorem leaf10000 : check (left_strip_box bandBox "10000") = true := by
  verify_left_strip_leaf

set_option maxRecDepth 12000 in
set_option maxHeartbeats 2500000 in
private theorem leaf10001 : check (left_strip_box bandBox "10001") = true := by
  verify_left_strip_leaf

set_option maxRecDepth 12000 in
set_option maxHeartbeats 2500000 in
private theorem leaf10010 : check (left_strip_box bandBox "10010") = true := by
  verify_left_strip_leaf

set_option maxRecDepth 12000 in
set_option maxHeartbeats 2500000 in
private theorem leaf10011 : check (left_strip_box bandBox "10011") = true := by
  verify_left_strip_leaf

set_option maxRecDepth 12000 in
set_option maxHeartbeats 2500000 in
private theorem leaf10100 : check (left_strip_box bandBox "10100") = true := by
  verify_left_strip_leaf

set_option maxRecDepth 12000 in
set_option maxHeartbeats 2500000 in
private theorem leaf10101 : check (left_strip_box bandBox "10101") = true := by
  verify_left_strip_leaf

set_option maxRecDepth 12000 in
set_option maxHeartbeats 2500000 in
private theorem leaf10110 : check (left_strip_box bandBox "10110") = true := by
  verify_left_strip_leaf

set_option maxRecDepth 12000 in
set_option maxHeartbeats 2500000 in
private theorem leaf10111 : check (left_strip_box bandBox "10111") = true := by
  verify_left_strip_leaf

set_option maxRecDepth 12000 in
set_option maxHeartbeats 2500000 in
private theorem leaf11000 : check (left_strip_box bandBox "11000") = true := by
  verify_left_strip_leaf

set_option maxRecDepth 12000 in
set_option maxHeartbeats 2500000 in
private theorem leaf11001 : check (left_strip_box bandBox "11001") = true := by
  verify_left_strip_leaf

set_option maxRecDepth 12000 in
set_option maxHeartbeats 2500000 in
private theorem leaf1101 : check (left_strip_box bandBox "1101") = true := by
  verify_left_strip_leaf

set_option maxRecDepth 12000 in
set_option maxHeartbeats 2500000 in
private theorem leaf11100 : check (left_strip_box bandBox "11100") = true := by
  verify_left_strip_leaf

set_option maxRecDepth 12000 in
set_option maxHeartbeats 2500000 in
private theorem leaf11101 : check (left_strip_box bandBox "11101") = true := by
  verify_left_strip_leaf

set_option maxRecDepth 12000 in
set_option maxHeartbeats 2500000 in
private theorem leaf1111 : check (left_strip_box bandBox "1111") = true := by
  verify_left_strip_leaf

theorem band1 : checkCover 5 (band 1 (5 / 4)) = true :=
  (coverSplit
    (coverSplit
      (coverSplit
        (coverSplit
          (coverSplit
            (coverLeaf leaf00000)
            (coverLeaf leaf00001))
          (coverLeaf leaf0001))
        (coverSplit
          (coverSplit
            (coverLeaf leaf00100)
            (coverLeaf leaf00101))
          (coverLeaf leaf0011)))
      (coverSplit
        (coverSplit
          (coverSplit
            (coverLeaf leaf01000)
            (coverLeaf leaf01001))
          (coverLeaf leaf0101))
        (coverSplit
          (coverSplit
            (coverLeaf leaf01100)
            (coverLeaf leaf01101))
          (coverLeaf leaf0111))))
    (coverSplit
      (coverSplit
        (coverSplit
          (coverSplit
            (coverLeaf leaf10000)
            (coverLeaf leaf10001))
          (coverSplit
            (coverLeaf leaf10010)
            (coverLeaf leaf10011)))
        (coverSplit
          (coverSplit
            (coverLeaf leaf10100)
            (coverLeaf leaf10101))
          (coverSplit
            (coverLeaf leaf10110)
            (coverLeaf leaf10111))))
      (coverSplit
        (coverSplit
          (coverSplit
            (coverLeaf leaf11000)
            (coverLeaf leaf11001))
          (coverLeaf leaf1101))
        (coverSplit
          (coverSplit
            (coverLeaf leaf11100)
            (coverLeaf leaf11101))
          (coverLeaf leaf1111)))))

end RefinedBMV.PositiveCenter.LocalTaylor
