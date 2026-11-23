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

open private Box.split rectangle verify verify_children verify_of_cover from
  D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.MiddleGapCertificate

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem check_1100 :
    verify ((Box.split (Box.split (Box.split (Box.split rectangle).2).2).1).1) 7 = true :=
  verify_of_cover
    (.split
      (.split (.split .leaf .leaf) (.split .leaf .leaf))
      (.split (.split .leaf .leaf) (.split .leaf .leaf)))
    (by decide +kernel)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem check_1101 :
    verify ((Box.split (Box.split (Box.split (Box.split rectangle).2).2).1).2) 7 = true :=
  verify_of_cover
    (.split (.split (.split .leaf .leaf) (.split .leaf .leaf)) (.split .leaf .leaf))
    (by decide +kernel)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem check_1110 :
    verify ((Box.split (Box.split (Box.split (Box.split rectangle).2).2).2).1) 7 = true :=
  verify_of_cover
    (.split (.split (.split .leaf .leaf) .leaf) (.split .leaf .leaf))
    (by decide +kernel)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem check_1111 :
    verify ((Box.split (Box.split (Box.split (Box.split rectangle).2).2).2).2) 7 = true :=
  verify_of_cover
    (.split (.split .leaf .leaf) (.split .leaf .leaf))
    (by decide +kernel)

theorem band4_checked : verify ((Box.split (Box.split rectangle).2).2) 9 = true :=
  verify_children (b := ((Box.split (Box.split rectangle).2).2)) (n := 8)
    (verify_children (b := ((Box.split (Box.split (Box.split rectangle).2).2).1)) (n := 7)
      check_1100 check_1101)
    (verify_children (b := ((Box.split (Box.split (Box.split rectangle).2).2).2)) (n := 7)
      check_1110 check_1111)

end RefinedBMV.PositiveCenter.MiddleGapReplay
