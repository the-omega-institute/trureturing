import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.GeometricCertificate.Verification

/-! # Finite verification for one band of the left strip -/

namespace RefinedBMV.PositiveCenter.LocalTaylor

open private band check checkCover Box from
  D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.LeftStripGeometricCertificate

private def bandBox : Box := band 2 (5 / 2)

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
private theorem leaf00010 : check (left_strip_box bandBox "00010") = true := by
  verify_left_strip_leaf

set_option maxRecDepth 12000 in
set_option maxHeartbeats 2500000 in
private theorem leaf00011 : check (left_strip_box bandBox "00011") = true := by
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
private theorem leaf01010 : check (left_strip_box bandBox "01010") = true := by
  verify_left_strip_leaf

set_option maxRecDepth 12000 in
set_option maxHeartbeats 2500000 in
private theorem leaf01011 : check (left_strip_box bandBox "01011") = true := by
  verify_left_strip_leaf

set_option maxRecDepth 12000 in
set_option maxHeartbeats 2500000 in
private theorem leaf0110 : check (left_strip_box bandBox "0110") = true := by
  verify_left_strip_leaf

set_option maxRecDepth 12000 in
set_option maxHeartbeats 2500000 in
private theorem leaf01110 : check (left_strip_box bandBox "01110") = true := by
  verify_left_strip_leaf

set_option maxRecDepth 12000 in
set_option maxHeartbeats 2500000 in
private theorem leaf01111 : check (left_strip_box bandBox "01111") = true := by
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
private theorem leaf11010 : check (left_strip_box bandBox "11010") = true := by
  verify_left_strip_leaf

set_option maxRecDepth 12000 in
set_option maxHeartbeats 2500000 in
private theorem leaf11011 : check (left_strip_box bandBox "11011") = true := by
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
private theorem leaf11110 : check (left_strip_box bandBox "11110") = true := by
  verify_left_strip_leaf

set_option maxRecDepth 12000 in
set_option maxHeartbeats 2500000 in
private theorem leaf11111 : check (left_strip_box bandBox "11111") = true := by
  verify_left_strip_leaf

theorem band4 : checkCover 5 (band 2 (5 / 2)) = true :=
  (coverSplit
    (coverSplit
      (coverSplit
        (coverSplit
          (coverSplit
            (coverLeaf leaf00000)
            (coverLeaf leaf00001))
          (coverSplit
            (coverLeaf leaf00010)
            (coverLeaf leaf00011)))
        (coverSplit
          (coverLeaf leaf0010)
          (coverLeaf leaf0011)))
      (coverSplit
        (coverSplit
          (coverLeaf leaf0100)
          (coverSplit
            (coverLeaf leaf01010)
            (coverLeaf leaf01011)))
        (coverSplit
          (coverLeaf leaf0110)
          (coverSplit
            (coverLeaf leaf01110)
            (coverLeaf leaf01111)))))
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
          (coverSplit
            (coverLeaf leaf11010)
            (coverLeaf leaf11011)))
        (coverSplit
          (coverSplit
            (coverLeaf leaf11100)
            (coverLeaf leaf11101))
          (coverSplit
            (coverLeaf leaf11110)
            (coverLeaf leaf11111))))))

end RefinedBMV.PositiveCenter.LocalTaylor
