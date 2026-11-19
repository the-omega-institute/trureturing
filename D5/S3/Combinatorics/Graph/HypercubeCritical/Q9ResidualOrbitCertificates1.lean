import D5.S3.Combinatorics.Graph.HypercubeCritical.Q9ResidualOrbitCertificateData

/-! Checked orbit certificates for 4 remaining deficit profiles. -/

namespace D5.S3.Combinatorics.Graph.HypercubeCritical


private def residualOrbitCertificates1 : List ResidualOrbitCertificate :=
  [⟨![4, 4, 4, 4, 4, 4, 4, 5, 5],
      [(.pairUpper 3 131, 1, 1465), (.pairUpper 129 385, 1, 316),
       (.pairUpper 385 129, 1, 57), (.agreementEdge 7 368 7, 1, 2011),
       (.agreementEdge 131 368 2, 1, 3017), (.shellLower 135, 1, 503),
       (.size, 1, 232), (.parity, 1, 25),
       (.degree 0, 1, 8), (.degree 1, 1, 134),
       (.degree 3, 1, 273), (.degree 7, 1, 168),
       (.degree 128, 1, 52), (.degree 129, 1, 201),
       (.degree 384, 1, 8), (.half 0, -1, 431),
       (.half 7, -1, 209), (.direction 7, -1, 67),
       (.degree 15, -1, 168), (.degree 131, -1, 603),
       (.degree 385, -1, 53)]⟩,
   ⟨![3, 4, 4, 4, 4, 4, 4, 4, 5],
      [(.pairUpper 0 256, 1, 4), (.pairUpper 1 257, 1, 4),
       (.pairUpper 2 258, 1, 15), (.pairUpper 3 259, 1, 18),
       (.pairUpper 6 262, 1, 164), (.pairLower 258 259, 1, 27),
       (.agreementEdge 7 240 8, 1, 139), (.agreementEdge 14 240 0, 1, 46),
       (.agreementEdge 448 30 0, 1, 139), (.pairUpper 30 385, 1, 108),
       (.shellLower 30, 1, 46), (.shellUpper 259, 1, 2),
       (.size, 1, 27), (.degree 1, 1, 1),
       (.degree 3, 1, 7), (.degree 6, 1, 12),
       (.degree 7, 1, 8), (.degree 256, 1, 1),
       (.degree 258, 1, 22), (.degree 259, 1, 12),
       (.half 0, -1, 2), (.half 1, -1, 60),
       (.half 8, -1, 13), (.direction 0, -1, 1),
       (.direction 8, -1, 5), (.degree 15, -1, 13),
       (.degree 262, -1, 66), (.degree 263, -1, 36)]⟩,
   ⟨![0, 3, 3, 5, 5, 5, 5, 5, 5],
      [(.pairLower 14 15, 1, 311), (.pairLower 24 25, 1, 822),
       (.pairUpper 26 30, 1, 513), (.agreementEdge 24 391 5, 1, 1086),
       (.agreementEdge 25 390 5, 1, 1086), (.agreementEdge 27 448 2, 1, 513),
       (.agreementEdge 448 30 0, 1, 724), (.pairUpper 449 31, 1, 724),
       (.shellLower 30, 1, 181), (.shellLower 31, 1, 181),
       (.size, 1, 252), (.direction 0, 1, 21),
       (.degree 0, 1, 16), (.degree 1, 1, 16),
       (.degree 6, 1, 7), (.degree 7, 1, 7),
       (.degree 10, 1, 311), (.degree 11, 1, 311),
       (.degree 14, 1, 93), (.degree 15, 1, 93),
       (.degree 24, 1, 256), (.degree 25, 1, 256),
       (.half 1, -1, 165), (.half 3, -1, 549),
       (.direction 1, -1, 14), (.direction 3, -1, 93),
       (.degree 26, -1, 309), (.degree 27, -1, 309),
       (.degree 56, -1, 392), (.degree 57, -1, 392)]⟩,
   ⟨![1, 2, 5, 5, 5, 5, 5, 5, 5],
      [(.pairUpper 0 1, 1, 9), (.pairUpper 2 3, 1, 11),
       (.pairUpper 4 5, 1, 65), (.pairUpper 15 13, 1, 703),
       (.pairUpper 15 14, 1, 938), (.agreementEdge 13 450 4, 1, 1954),
       (.agreementEdge 14 449 4, 1, 781), (.agreementEdge 28 450 0, 1, 1302),
       (.agreementEdge 28 449 1, 1, 521), (.shellLower 29, 1, 130),
       (.shellLower 30, 1, 326), (.size, 1, 244),
       (.parity, 1, 43), (.degree 0, 1, 14),
       (.degree 2, 1, 6), (.degree 3, 1, 6),
       (.degree 5, 1, 96), (.degree 6, 1, 52),
       (.degree 7, 1, 291), (.degree 12, 1, 482),
       (.degree 14, 1, 130), (.half 0, -1, 19),
       (.half 1, -1, 56), (.half 2, -1, 612),
       (.direction 0, -1, 23), (.direction 1, -1, 6),
       (.direction 2, -1, 96), (.degree 15, -1, 586),
       (.degree 28, -1, 326), (.degree 29, -1, 174)]⟩]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
-- Reduce each sparse certificate on its own finite coordinate profile.
private theorem residualOrbitCertificates1_valid :
    ∀ c ∈ residualOrbitCertificates1, c.Valid := by
  simp only [residualOrbitCertificates1, List.forall_mem_cons]
  repeat' apply And.intro
  all_goals first | exact List.forall_mem_nil _ | decide +kernel

end D5.S3.Combinatorics.Graph.HypercubeCritical
