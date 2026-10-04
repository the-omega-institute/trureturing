/- GID: D5/S3/Combinatorics/RegularInduced/DysonMcKay
   generality: G
   mirror-B: D5/B/S3/Combinatorics/RegularInduced/DysonMcKay
   mirror-E: none(waiver:dyson-mckay-prime-optimality-resolution)
   anchors: []
   utility: none
   digest: The literal cycle-clique unions have the Dyson and McKay prime optimum. -/

import D5.S3.Combinatorics.RegularInduced.DysonMcKayLower
import D5.S3.Combinatorics.RegularInduced.DysonMcKayUpper

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.RegularInduced.DysonMcKay

/-- Dyson and McKay's prime optimality assertion in the fixed literal graph class. -/
theorem result : DysonMcKayDefs.claim := by
  intro p hp hp13
  exact ⟨fun comps hadm havoid => upper_bound hp hp13 comps hadm havoid,
    attainment hp hp13⟩

end D5.S3.Combinatorics.RegularInduced.DysonMcKay
