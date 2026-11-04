# IntegerCover

## Abstract

Second peak SecondPeakA2: IntegerCover

The eight translated integer intervals overlap under 16e<=D and 13D<=A. Euclidean division by 8A transports their chain to every integer X, without a cutoff on X, A or the quotient. The resulting j is between 0 and 15.

**Theorem 1.1 (sixteen_step_cover).**

Lean statement: `D5/S3/Combinatorics/Circle/FourNegative/SecondPeakA2/IntegerCover.sixteen_step_cover`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/FourNegative/SecondPeakA2/IntegerCover.sixteen_step_cover` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem sixteen_step_cover (A D e X : ℤ)     (hD : 0 < D) (he : 0 ≤ e) (heD : 16*e ≤ D) (hDA : 13*D ≤ A) :     ∃ j v : ℤ, 0 ≤ j ∧ j ≤ 15 ∧       ((e ≤ X+j*(5*A-D)+8*v*A ∧ X+j*(5*A-D)+8*v*A ≤ A-e) ∨        (3*A+e ≤ X+j*(5*A-D)+8*v*A ∧ X+j*(5*A-D)+8*v*A ≤ 4*A-e))

## References

- Truth anchor: `D5/S3/Combinatorics/Circle/FourNegative/SecondPeakA2/IntegerCover.sixteen_step_cover`
