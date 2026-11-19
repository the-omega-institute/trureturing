import D5.S3.Combinatorics.Graph.HypercubeCritical.Q9ResidualOrbitCertificateData

/-! Checked orbit certificates for 4 remaining deficit profiles. -/

namespace D5.S3.Combinatorics.Graph.HypercubeCritical


private def residualOrbitCertificates3 : List ResidualOrbitCertificate :=
  [⟨![2, 2, 2, 3, 5, 5, 5, 5, 5],
      [(.pairUpper 48 56, 1, 2), (.agreementEdge 19 396 5, 1, 70),
       (.agreementEdge 25 390 5, 1, 70), (.agreementEdge 384 31 5, 1, 81),
       (.agreementEdge 49 396 1, 1, 139), (.agreementEdge 49 390 3, 1, 70),
       (.agreementEdge 392 51 2, 1, 70), (.shellLower 31, 1, 13),
       (.shellLower 51, 1, 23), (.shellLower 57, 1, 23),
       (.shellUpper 112, 1, 8), (.size, 1, 47),
       (.degree 0, 1, 2), (.degree 3, 1, 3),
       (.degree 7, 1, 2), (.degree 9, 1, 3),
       (.degree 11, 1, 8), (.degree 15, 1, 1),
       (.degree 17, 1, 52), (.degree 19, 1, 22),
       (.degree 24, 1, 19), (.degree 25, 1, 18),
       (.degree 31, 1, 6), (.degree 48, 1, 23),
       (.parity, -1, 1), (.half 0, -1, 31),
       (.half 3, -1, 11), (.half 4, -1, 79),
       (.direction 0, -1, 3), (.direction 3, -1, 1),
       (.direction 4, -1, 12), (.degree 27, -1, 4),
       (.degree 49, -1, 34), (.degree 51, -1, 8),
       (.degree 56, -1, 14), (.degree 112, -1, 27)]⟩,
   ⟨![3, 3, 4, 5, 5, 5, 5, 5, 5],
      [(.pairUpper 15 13, 1, 43360), (.pairUpper 27 25, 1, 108399),
       (.pairUpper 450 13, 1, 16159), (.agreementEdge 13 450 4, 1, 68675),
       (.pairUpper 450 25, 1, 40397), (.agreementEdge 25 450 2, 1, 34338),
       (.agreementEdge 25 450 5, 1, 10099), (.agreementEdge 25 390 5, 1, 127251),
       (.agreementEdge 28 450 0, 1, 84834), (.agreementEdge 448 29 1, 1, 84834),
       (.agreementEdge 56 450 0, 1, 28278), (.shellLower 29, 1, 21208),
       (.shellLower 57, 1, 28278), (.size, 1, 24743),
       (.parity, 1, 1571), (.degree 0, 1, 969),
       (.degree 1, 1, 703), (.degree 3, 1, 969),
       (.degree 4, 1, 176), (.degree 5, 1, 2289),
       (.degree 7, 1, 3437), (.degree 8, 1, 1055),
       (.degree 9, 1, 13735), (.degree 11, 1, 20625),
       (.degree 12, 1, 15912), (.degree 24, 1, 39780),
       (.half 0, -1, 7608), (.half 2, -1, 8394),
       (.half 3, -1, 50362), (.direction 0, -1, 2641),
       (.direction 2, -1, 1145), (.direction 3, -1, 6868),
       (.degree 15, -1, 13757), (.degree 27, -1, 34394),
       (.degree 28, -1, 22611), (.degree 56, -1, 30148)]⟩,
   ⟨![0, 2, 4, 5, 5, 5, 5, 5, 5],
      [(.pairLower 14 15, 1, 311), (.pairLower 24 25, 1, 822),
       (.pairUpper 28 30, 1, 256), (.pairUpper 29 31, 1, 256),
       (.agreementEdge 24 391 5, 1, 1086), (.agreementEdge 25 390 5, 1, 1086),
       (.agreementEdge 26 449 2, 1, 256), (.agreementEdge 27 448 2, 1, 256),
       (.agreementEdge 448 30 0, 1, 724), (.pairUpper 449 31, 1, 724),
       (.shellLower 30, 1, 181), (.shellLower 31, 1, 181),
       (.size, 1, 252), (.direction 0, 1, 21),
       (.degree 0, 1, 16), (.degree 1, 1, 16),
       (.degree 6, 1, 7), (.degree 7, 1, 7),
       (.degree 10, 1, 155), (.degree 11, 1, 155),
       (.degree 12, 1, 155), (.degree 13, 1, 155),
       (.degree 14, 1, 93), (.degree 15, 1, 93),
       (.degree 24, 1, 256), (.degree 25, 1, 256),
       (.half 1, -1, 83), (.half 2, -1, 83),
       (.half 3, -1, 549), (.direction 1, -1, 7),
       (.direction 2, -1, 7), (.direction 3, -1, 93),
       (.degree 26, -1, 155), (.degree 27, -1, 155),
       (.degree 28, -1, 155), (.degree 29, -1, 155),
       (.degree 56, -1, 392), (.degree 57, -1, 392)]⟩,
   ⟨![2, 2, 4, 4, 4, 5, 5, 5, 5],
      [(.pairUpper 13 29, 1, 5), (.pairUpper 100 96, 1, 29),
       (.pairUpper 97 99, 1, 23), (.agreementEdge 13 402 5, 1, 48),
       (.agreementEdge 384 31 5, 1, 6), (.pairUpper 402 37, 1, 10),
       (.agreementEdge 37 402 3, 1, 137), (.agreementEdge 37 402 6, 1, 44),
       (.agreementEdge 44 402 0, 1, 96), (.agreementEdge 97 402 2, 1, 48),
       (.agreementEdge 100 402 0, 1, 96), (.shellLower 31, 1, 1),
       (.shellLower 101, 1, 48), (.size, 1, 38),
       (.parity, 1, 3), (.direction 0, 1, 1),
       (.degree 0, 1, 1), (.degree 5, 1, 4),
       (.degree 7, 1, 3), (.degree 12, 1, 8),
       (.degree 13, 1, 5), (.degree 28, 1, 1),
       (.degree 31, 1, 1), (.degree 33, 1, 10),
       (.degree 35, 1, 9), (.degree 36, 1, 43),
       (.degree 96, 1, 12), (.half 0, -1, 12),
       (.half 2, -1, 35), (.half 5, -1, 61),
       (.direction 2, -1, 2), (.direction 5, -1, 2),
       (.degree 29, -1, 2), (.degree 39, -1, 3),
       (.degree 44, -1, 25), (.degree 45, -1, 53),
       (.degree 97, -1, 8), (.degree 99, -1, 9),
       (.degree 100, -1, 53), (.degree 224, -1, 8)]⟩]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
-- Reduce each sparse certificate on its own finite coordinate profile.
private theorem residualOrbitCertificates3_valid :
    ∀ c ∈ residualOrbitCertificates3, c.Valid := by
  simp only [residualOrbitCertificates3, List.forall_mem_cons]
  repeat' apply And.intro
  all_goals first | exact List.forall_mem_nil _ | decide +kernel

end D5.S3.Combinatorics.Graph.HypercubeCritical
