/- GID: D5/S3/Combinatorics/PackingDomatic/PackingDomaticPath
   generality: G
   mirror-B: D5/B/S3/Combinatorics/PackingDomatic/PackingDomaticPath
   mirror-E: none(waiver:general-counting-refutation)
   anchors: []
   utility: none
   digest: The general path counting bound gives a negative answer to Brešar-Ferme-Hu Problem 2. -/

import D5.S3.Combinatorics.PackingDomatic.PackingDomaticPathCounting

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.PackingDomatic.PackingDomaticPath

/-- Brešar-Ferme-Hu Problem 2 fails at k = 28 and n = 56. -/
theorem result : ¬ PackingDomaticPathDefs.claim := by
  intro h
  obtain ⟨f, hf⟩ := h 28 56 (by omega) (by omega)
  have hc := PackingDomaticPathCounting.local_counting hf (by omega)
  omega

end D5.S3.Combinatorics.PackingDomatic.PackingDomaticPath
