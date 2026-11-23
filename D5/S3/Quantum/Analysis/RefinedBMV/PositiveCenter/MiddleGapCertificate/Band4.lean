/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveCenter/MiddleGapCertificate/Band4
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact kernel checks for one quarter of the compact right-strip interval certificate. -/

import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.MiddleGapCertificate
import Batteries.Tactic.OpenPrivate

/-! Exact checks for a quarter of the right-strip interval certificate. -/

namespace RefinedBMV.PositiveCenter.MiddleGapReplay

open private Box.split rectangle verify verify_children from
  D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.MiddleGapCertificate

section
set_option maxRecDepth 8192
set_option maxHeartbeats 0

private theorem check_1100 : verify ((Box.split (Box.split (Box.split (Box.split rectangle).2).2).1).1) 7 = true :=
  by decide +kernel

private theorem check_1101 : verify ((Box.split (Box.split (Box.split (Box.split rectangle).2).2).1).2) 7 = true :=
  by decide +kernel

private theorem check_1110 : verify ((Box.split (Box.split (Box.split (Box.split rectangle).2).2).2).1) 7 = true :=
  by decide +kernel

private theorem check_1111 : verify ((Box.split (Box.split (Box.split (Box.split rectangle).2).2).2).2) 7 = true :=
  by decide +kernel

end

theorem band4_checked : verify ((Box.split (Box.split rectangle).2).2) 9 = true :=
  verify_children (b := ((Box.split (Box.split rectangle).2).2)) (n := 8)
    (verify_children (b := ((Box.split (Box.split (Box.split rectangle).2).2).1)) (n := 7) check_1100 check_1101)
    (verify_children (b := ((Box.split (Box.split (Box.split rectangle).2).2).2)) (n := 7) check_1110 check_1111)

end RefinedBMV.PositiveCenter.MiddleGapReplay
