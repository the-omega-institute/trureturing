/- GID: D5/S1/Words/OriginalGenerationBoundary
   generality: G
   mirror-B: D5/B/S1/Words/OriginalGenerationBoundary
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The explicit finite-word boundary conjugacy for the original generation morphisms. -/

import Mathlib.Data.Bool.Basic
import Mathlib.Data.List.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.OriginalGenerationBoundary

/- The source uses `0` and `1`; the formal alphabet is Bool with false and true
   representing those two letters. -/
def sigma : Bool → List Bool
  | false => [false, true]
  | true => [false]

def tau : Bool → List Bool
  | false => [false, false, true, false, true]
  | true => [false, false, true]

def apply (morphism : Bool → List Bool) (w : List Bool) : List Bool :=
  w.flatMap morphism

def sigmaThree (w : List Bool) : List Bool :=
  apply sigma (apply sigma (apply sigma w))

def tauWord (w : List Bool) : List Bool :=
  apply tau w

def finitePrefix (uK w : List Bool) : List Bool :=
  uK ++ tauWord w ++ [false, false]

theorem original_generation_boundary (uK w : List Bool) :
    sigmaThree w ++ [false, true] = [false, true] ++ tauWord w ∧
      finitePrefix uK w = uK ++ tauWord w ++ [false, false] := by
  constructor
  · induction w with
    | nil => rfl
    | cons b w ih =>
        cases b <;>
          simpa [sigmaThree, tauWord, apply, sigma, tau, List.flatMap_append,
            List.append_assoc] using ih
  · rfl

end D5.S1.Words.OriginalGenerationBoundary
