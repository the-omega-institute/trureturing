# A Rising Comparison for Actual Separable Records

## Abstract

The actual irreducible right-maximum distribution rises from two to three records.

**Theorem 1.1 (Every length at least four).**

$$n\ge4 \Rightarrow \operatorname{j}\left(n, 2\right)\le\operatorname{j}\left(n, 3\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Patterns/Separable/RecordPeak.actual_record_rising` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The quantity j(n,k) is the cardinality of the actual permutations of Fin n avoiding 2413 and 3142, with no proper direct cut and exactly k strict right maxima. A position is a right maximum when its value exceeds every later value. The theorem has no generating-function or cardinality-correspondence hypothesis.

Positive record series omit the empty permutation. The scalar series q and I0 are defined directly from actual avoidance and direct-indecomposable cardinalities. Minimum-cut reconstruction gives finite record-fiber convolutions. The pointwise opposite-sign cut law restricts to each record fiber for n>=2, and the singleton contributes ty to both no-cut classes. These actual partitions give U=(1+q)J and J=ty+ty(1+q)J+q(1+q)J^2. The scalar supplier identifies q=t*largeSchroderSeries.

The quadratic gives J1=t, J2=t^2(1+q)^2 and J3=t^3(1+q)^3(1+2q). The scalar equation q=t+tq+q^2 then gives J3-J2=t^2 P(q), where P(x)=-1-x+2x^2+x^3-3x^4-2x^5. Differentiation uses K(q)q'=(1+q)^2, with K(x)=1-2x-x^2.

For N(x)=9x^2-2x^3-31x^4-32x^5-10x^6, the derivative of P(q)+1+t equals (N/K)(q). An exact series V satisfies K*V=N. Its first eight coefficients are 0,0,9,16,10,4,8,20, and every later coefficient is twice the preceding one plus the coefficient two places earlier. Thus all coefficients are nonnegative. Finite coefficientwise composition with the positive actual series q preserves this property. The derivative identity gives nonnegativity at every positive degree; the correction 1+t affects only degrees zero and one. Multiplication by t^2 therefore proves the actual comparison for every n>=4.

This proves the adjacent comparison between records two and three for irreducible right maxima. The full peak-three conjecture also requires the remaining rising comparisons, all decreasing comparisons and the other three actual record/class transports; they are outside this theorem.

## References

- Truth anchor: `D5/S1/Words/Patterns/Separable/RecordPeak.actual_record_rising`
- Dependency: [D5/S1/Words/Patterns/Separable/ActualCardinality](ActualCardinality.md)
