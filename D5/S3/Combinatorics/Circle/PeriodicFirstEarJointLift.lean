/- GID: D5/S3/Combinatorics/Circle/PeriodicFirstEarJointLift
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Circle/PeriodicFirstEarJointLift
   mirror-E: none(waiver:no-escape-mirror-specified)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Physical repeated one-bit periods admit a literal first-ear joint order.
-/
import D5.S3.Combinatorics.Circle.RunFirstEarTransport
import D5.S3.Combinatorics.Circle.PeriodicShorteningArithmetic
import D5.S3.Combinatorics.Circle.ThreeRowSource
import D5.S3.Combinatorics.Circle.ZeroSumSubsets

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Circle.PeriodicFirstEarJointLift
open SourceWidth PeriodicShortening PeriodicShorteningArithmetic RunFirstEarTransport
open ThreeRowSource ZeroSumSubsets
open scoped BigOperators

example (k : ℕ) (hk : 0 < k) (l : List (Fin k)) :
    (l.take 0).map (actualSource k 1) = [] := by simp

example (k : ℕ) (hk : 0 < k) (n : ℕ) :
    ((List.finRange k).take (n+1)).map (actualSource k 1) =
      (List.finRange k).take (n+1) |>.map (actualSource k 1) := by rfl

example (k : ℕ) : List.finRange (k+1) = 0 :: (List.finRange k).map Fin.succ := by
  simp [List.finRange_succ]

end D5.S3.Combinatorics.Circle.PeriodicFirstEarJointLift
