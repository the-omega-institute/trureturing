/- GID: D5/S3/Arith/FiniteField/DyadicTraceCirculant
   generality: G
   mirror-B: D5/B/S3/Arith/FiniteField/DyadicTraceCirculant
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Unit dyadic trace-circulant consecutive sections over the binary field. -/

import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.Finite.Trace
import D5.S3.Analytic.GoldenTomography.FinitePronyMatrixPencil

namespace D5.S3.Arith.FiniteField.DyadicTraceCirculant

open scoped BigOperators

/-- Directed cyclic displacement; the endpoint casts precede subtraction. -/
def dyadicTraceCirculant (k t : ℕ) :
    Matrix (Fin (2 ^ (k - 1))) (Fin (2 ^ (k - 1))) (ZMod 2) :=
  fun x y => ∑ i : Fin k,
    if ((y.val : ZMod (2 ^ k - 1)) - (x.val : ZMod (2 ^ k - 1))) =
        (t : ZMod (2 ^ k - 1)) * (2 : ZMod (2 ^ k - 1)) ^ i.val
    then 1 else 0

end D5.S3.Arith.FiniteField.DyadicTraceCirculant
