/- GID: D5/S1/Words/OriginalGenerationBoundary
   generality: G
   mirror-B: D5/B/S1/Words/OriginalGenerationBoundary
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The explicit finite-word boundary conjugacy for the original generation morphisms. -/

import D5.S1.Words.FibonacciIncidence

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.OriginalGenerationBoundary

/-- The two finite block images, with false representing 0 and true representing 1. -/
def tau : Bool → List Bool
  | false => [false, false, true, false, true]
  | true => [false, false, true]

/-- Complementing both alphabets transports the canonical Fibonacci iterate
    to the convention sigma(0) = 01 and sigma(1) = 0. -/
def sigmaThree (w : List Bool) : List Bool :=
  (FibonacciIncidence.iterate 3 (w.map Bool.not)).map Bool.not

/-- Letterwise concatenation of the two block images. -/
def tauWord (w : List Bool) : List Bool :=
  w.flatMap tau

/-- Abstract finite-word conjugacy. No source, acquisition or cursor is assumed. -/
theorem original_generation_boundary (w : List Bool) :
    sigmaThree w ++ [false, true] = [false, true] ++ tauWord w := by
  induction w with
  | nil => rfl
  | cons b w ih =>
      cases b <;>
        simpa [sigmaThree, tauWord, FibonacciIncidence.iterate,
          FibonacciIncidence.substitute, D5.S0.Tower.GoldenGapWord.subst,
          tau, List.flatMap_append, List.map_append, List.append_assoc] using ih

end D5.S1.Words.OriginalGenerationBoundary
