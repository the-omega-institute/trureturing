/- GID: D5/S3/Combinatorics/Graph/StarForming/HeawoodIncidence
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/StarForming/HeawoodIncidence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [lake/module/Init]
   utility: none
   digest: Binary incidence pairing for Heawood graphs. -/

import Init

/-! The binary incidence pairing from subquorum-colorings
48728b42d39ab3de5de251c61da5a404ec418a69, Apache-2.0. -/

namespace D5.S3.Combinatorics.Graph.StarForming.HeawoodCertificates

def dot (first second : Nat) : Nat :=
  ((first % 2) * (second % 2) + (first / 2 % 2) * (second / 2 % 2) +
    (first / 4) * (second / 4)) % 2

end D5.S3.Combinatorics.Graph.StarForming.HeawoodCertificates
