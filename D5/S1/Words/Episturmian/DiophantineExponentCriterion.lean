/- GID: D5/S1/Words/Episturmian/DiophantineExponentCriterion
   generality: G
   mirror-B: D5/B/S1/Words/Episturmian/DiophantineExponentCriterion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Peltomäki Conjecture 8.4 -/

/- escape_witness: D5.S1.Words.Episturmian.BoundedPowers.extendedMu_period_lift
   admission_basis: open-problem-resolution (#15858; Proved)
   Declarations:
   proof_shape: result: content; escape_witness: D5.S1.Words.Episturmian.BoundedPowers.extendedMu_period_lift; consumer: none
   Direct frozen dependencies (pre-existing): none (pinned Mathlib and same-delivery declarations)
   Finite prefixes use the existing factor operator at start zero.
   Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/16158
-/

import D5.S1.Words.Episturmian.BoundedPowers

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.Episturmian.DiophantineExponentCriterion
open D5.S1.Words.Episturmian.MorphicDecomposition
open D5.S1.Words.Episturmian.BoundedPowers

 theorem result : claim := by
  intro d Delta t hlang _haper
  constructor
  · exact dio_finite_implies_boundedPQ Delta t hlang
  · intro hb
    exact dio_finite_of_bounded_powers t
      (boundedPowers_of_language_eq t (cDelta Delta) hlang (boundedPQ_boundedPowers Delta hb))

end D5.S1.Words.Episturmian.DiophantineExponentCriterion
