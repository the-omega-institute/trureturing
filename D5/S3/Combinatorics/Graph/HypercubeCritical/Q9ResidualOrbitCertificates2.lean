import D5.S3.Combinatorics.Graph.HypercubeCritical.Q9ResidualOrbitCertificateData

/-! Checked orbit certificates for 4 remaining deficit profiles. -/

namespace D5.S3.Combinatorics.Graph.HypercubeCritical


private def residualOrbitCertificates2 : List ResidualOrbitCertificate :=
  [⟨![2, 4, 4, 5, 5, 5, 5, 5, 5],
      [(.pairLower 24 25, 1, 105), (.pairUpper 27 25, 1, 36),
       (.pairUpper 26 27, 1, 50), (.pairUpper 449 14, 1, 39),
       (.agreementEdge 25 390 5, 1, 107), (.agreementEdge 26 449 2, 1, 77),
       (.agreementEdge 448 30 0, 1, 71), (.pairUpper 449 56, 1, 13),
       (.shellLower 30, 1, 18), (.shellLower 57, 1, 13),
       (.size, 1, 26), (.parity, 1, 7),
       (.degree 0, 1, 3), (.degree 1, 1, 3),
       (.degree 6, 1, 3), (.degree 7, 1, 3),
       (.degree 10, 1, 34), (.degree 11, 1, 54),
       (.degree 14, 1, 16), (.degree 24, 1, 58),
       (.degree 25, 1, 48), (.degree 30, 1, 1),
       (.half 0, -1, 2), (.half 1, -1, 14),
       (.half 3, -1, 64), (.direction 1, -1, 5),
       (.direction 3, -1, 17), (.degree 27, -1, 50),
       (.degree 56, -1, 21), (.degree 57, -1, 43)]⟩,
   ⟨![0, 2, 2, 5, 5, 5, 5, 5, 5],
      [(.pairLower 14 15, 1, 278), (.pairLower 24 25, 1, 732),
       (.pairUpper 26 27, 1, 95), (.pairUpper 27 26, 1, 95),
       (.pairUpper 449 14, 1, 152), (.agreementEdge 14 449 4, 1, 390),
       (.pairUpper 448 15, 1, 152), (.agreementEdge 15 448 4, 1, 390),
       (.agreementEdge 26 449 2, 1, 1084), (.agreementEdge 27 448 2, 1, 1084),
       (.pairUpper 448 30, 1, 542), (.pairUpper 449 31, 1, 542),
       (.pairUpper 56 449, 1, 181), (.pairUpper 449 56, 1, 181),
       (.shellLower 56, 1, 181), (.shellLower 57, 1, 181),
       (.size, 1, 236), (.degree 0, 1, 36),
       (.degree 1, 1, 36), (.degree 6, 1, 33),
       (.degree 7, 1, 33), (.degree 10, 1, 472),
       (.degree 11, 1, 472), (.degree 14, 1, 139),
       (.degree 15, 1, 139), (.degree 24, 1, 542),
       (.degree 25, 1, 542), (.half 1, -1, 60),
       (.half 3, -1, 529), (.direction 1, -1, 66),
       (.direction 3, -1, 217), (.degree 26, -1, 95),
       (.degree 27, -1, 95)]⟩,
   ⟨![3, 3, 3, 4, 5, 5, 5, 5, 5],
      [(.agreementEdge 19 396 5, 1, 82), (.agreementEdge 25 390 5, 1, 82),
       (.agreementEdge 49 396 1, 1, 163), (.agreementEdge 49 390 3, 1, 82),
       (.pairUpper 51 448, 1, 27), (.agreementEdge 392 51 2, 1, 82),
       (.pairUpper 57 448, 1, 27), (.shellLower 51, 1, 27),
       (.shellLower 57, 1, 27), (.size, 1, 36),
       (.parity, 1, 3), (.degree 0, 1, 3),
       (.degree 1, 1, 1), (.degree 3, 1, 3),
       (.degree 7, 1, 3), (.degree 9, 1, 4),
       (.degree 11, 1, 9), (.degree 17, 1, 59),
       (.degree 19, 1, 27), (.degree 24, 1, 21),
       (.degree 25, 1, 23), (.degree 48, 1, 32),
       (.half 0, -1, 22), (.half 3, -1, 8),
       (.half 4, -1, 67), (.direction 0, -1, 4),
       (.direction 3, -1, 2), (.direction 4, -1, 14),
       (.degree 27, -1, 2), (.degree 49, -1, 32),
       (.degree 51, -1, 9), (.degree 56, -1, 14),
       (.degree 112, -1, 3)]⟩,
   ⟨![2, 2, 4, 5, 5, 5, 5, 5, 5],
      [(.pairUpper 15 13, 1, 434), (.pairUpper 27 25, 1, 1084),
       (.pairUpper 450 13, 1, 162), (.agreementEdge 13 450 4, 1, 687),
       (.pairUpper 450 25, 1, 404), (.agreementEdge 25 450 2, 1, 343),
       (.agreementEdge 25 450 5, 1, 101), (.agreementEdge 25 390 5, 1, 1273),
       (.agreementEdge 28 450 0, 1, 848), (.agreementEdge 448 29 1, 1, 848),
       (.agreementEdge 56 450 0, 1, 283), (.shellLower 29, 1, 212),
       (.shellLower 57, 1, 283), (.size, 1, 247),
       (.parity, 1, 16), (.degree 0, 1, 13),
       (.degree 3, 1, 13), (.degree 4, 1, 2),
       (.degree 5, 1, 23), (.degree 7, 1, 34),
       (.degree 8, 1, 11), (.degree 9, 1, 137),
       (.degree 11, 1, 206), (.degree 12, 1, 159),
       (.degree 24, 1, 398), (.half 0, -1, 76),
       (.half 2, -1, 84), (.half 3, -1, 504),
       (.direction 0, -1, 26), (.direction 2, -1, 11),
       (.direction 3, -1, 69), (.degree 15, -1, 138),
       (.degree 27, -1, 344), (.degree 28, -1, 226),
       (.degree 56, -1, 301)]⟩]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
-- Reduce each sparse certificate on its own finite coordinate profile.
private theorem residualOrbitCertificates2_valid :
    ∀ c ∈ residualOrbitCertificates2, c.Valid := by
  simp only [residualOrbitCertificates2, List.forall_mem_cons]
  repeat' apply And.intro
  all_goals first | exact List.forall_mem_nil _ | decide +kernel

end D5.S3.Combinatorics.Graph.HypercubeCritical
