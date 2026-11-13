# All natural parameters and finite repetitions

## Abstract

The complete physical second-peak equal-outer face

**Theorem 1.1 (Whole-face endpoint).**

Lean statement: `D5/S3/Combinatorics/Circle/FourNegative/SecondPeakEqualOuter/Endpoint.actualSource_second_peak_equal_outer_joint_lift`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/FourNegative/SecondPeakEqualOuter/Endpoint.actualSource_second_peak_equal_outer_joint_lift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every independent natural a,b,c with 2<=a,2<=c,max(a,c)<=b, put k=a+b+c+a and A=1+2^a+2^(a+b)+2^(a+b+c). There is one permutation sigma of every original Fin(k) occurrence and one natural literal cut j<=k with both OriginalOrder(k,A,sigma) and OriginalOrder(k+1,2A,earWord(k,sigma,j)). For every natural m,n the take(n) of m finite copies of each actual scalar word stays in its exact strip. For every natural m both complete repeated scalar totals are zero, including empty, full and overlong takes. The partition first reuses EqualFirstTwoLast at b=a and EqualOuterThree at c=a, then uses the lower, palindromic and strict physical constructions. The palindromic b=a+1 overlap directly reuses BalancedGaps. Only arithmetic length and exponent equalities are normalized on these overlaps. Full unrestricted J/C3.1 and Circle remain OPEN.

## References

- Truth anchor: `D5/S3/Combinatorics/Circle/FourNegative/SecondPeakEqualOuter/Endpoint.actualSource_second_peak_equal_outer_joint_lift`
- Dependency: [D5/S3/Combinatorics/Circle/FourNegative/SecondPeakEqualOuter/Lower](Lower.md)
- Dependency: [D5/S3/Combinatorics/Circle/FourNegative/SecondPeakEqualOuter/Palindromic](Palindromic.md)
- Dependency: [D5/S3/Combinatorics/Circle/FourNegative/SecondPeakEqualOuter/Strict](Strict.md)
