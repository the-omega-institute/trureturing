/- GID: D5/S3/Combinatorics/SubtractionGames/AdmissibleAngle
   generality: I
   mirror-B: D5/B/S3/Combinatorics/SubtractionGames/AdmissibleAngle
   mirror-E: none(waiver:manabe-conjecture-fifty-seven)
   anchors: []
   utility: none
   digest: Admissible-angle necessity for purely periodic three-move subtraction games. -/

import D5.S3.Combinatorics.SubtractionGames.AdmissibleAngleCA
import D5.S3.Combinatorics.SubtractionGames.AdmissibleAngleCB

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.SubtractionGames.AdmissibleAngle

open AdmissibleAngleDefs

/-- Manabe's Conjecture 57: each candidate least pure period forces its admissible angle. -/
theorem result : AdmissibleAngleDefs.claim := by
  intro a b c p ha hab hbc _ primitive hp
  constructor
  · intro hpa
    apply ca_necessity a b c (by omega) hab hbc
    intro n
    rw [← hpa, hp.2.1 n]
  · intro hpb
    apply cb_necessity a b c ha hab hbc primitive
    intro n
    rw [← hpb, hp.2.1 n]

#print axioms result

end D5.S3.Combinatorics.SubtractionGames.AdmissibleAngle
