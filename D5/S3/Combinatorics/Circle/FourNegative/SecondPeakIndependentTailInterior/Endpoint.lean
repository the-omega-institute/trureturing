/- GID: D5/S3/Combinatorics/Circle/FourNegative/SecondPeakIndependentTailInterior/Endpoint
   generality: I
   mirror-B: none(waiver:owning-blueprint-scribe)
   mirror-E: none(waiver:literal-first-ear-endpoint)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Independent-gap UXWV actual source order and the same word's literal first ear. -/
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakIndependentTailInterior.FirstEar
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.SecondPeakIndependentTailInterior.Endpoint
open SourceWidth PeriodicShortening RunFirstEarTransport
open private Parameters Parameters.mk from
  D5.S3.Combinatorics.Circle.FourNegative.SecondPeakIndependentTailInterior.Parameters
open private physical_first_ear from
  D5.S3.Combinatorics.Circle.FourNegative.SecondPeakIndependentTailInterior.FirstEar

/-- The four gaps are independent and unbounded above. The witness is one
physical source permutation, used unchanged after the literal first ear. -/
theorem actualSource_independent_tail_interior_first_ear
    (a b c d : ℕ) (hc : 2≤c) (hd : c+2≤d)
    (ha : c+d+3≤a) (hb : a+1≤b) :
    ∃ sigma : List (Fin (a+b+c+d)),
      OriginalOrder (a+b+c+d) (1+2^a+2^(a+b)+2^(a+b+c)) sigma ∧
      OriginalOrder (a+b+c+d+1) (2*(1+2^a+2^(a+b)+2^(a+b+c)))
        (earWord (a+b+c+d) sigma 0) := by
  exact physical_first_ear (Parameters.mk a b c d hc hd ha hb)

end D5.S3.Combinatorics.Circle.FourNegative.SecondPeakIndependentTailInterior.Endpoint
