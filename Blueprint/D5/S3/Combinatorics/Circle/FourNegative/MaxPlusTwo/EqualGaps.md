# One actual reserved label over the entire fourth-gap ray

## Abstract

A physical first-ear order for equal first-three gaps

**Theorem 1.1 (The unbounded equal-gap branch).**

Lean statement: `D5/S3/Combinatorics/Circle/FourNegative/MaxPlusTwo/EqualGaps.actualSource_equal_gaps_first_ear`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/FourNegative/MaxPlusTwo/EqualGaps.actualSource_equal_gaps_first_ear` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For all a>=2 and d>=a+2, put k=3a+d and A=1+2^a+2^(2a)+2^(3a). The theorem constructs one permutation sigma of every physical Fin(k) occurrence such that OriginalOrder(k,A,sigma) and OriginalOrder(k+1,2A,earWord(k,sigma,0)). Both totals are exactly zero. Both strip predicates quantify over every natural take-prefix, including empty and saturated takes. No primitivity, coprimality or injectivity of numerical source values is assumed.

Set s=d-a-1. The natural-label word first uses every positive U label except s, then U-minus; it uses every positive V label then V-minus, every positive W label then W-minus, and finally the reserved U label s together with every positive X label before X-minus. Within each positive interval labels retain increasing order. The reserve_inventory proof partitions the complete physical label range and reorders its actual occurrences; it does not quotient equal numerical values.

Write R=2^a, l=2^s and p=2^(a-1), so R=2p and 2^d=2Rl, with p,l>=2. SourceTable supplies the actual old and enlarged centered rows without the eventual d>=3a+3 hypothesis. The withheld old value is lA and the withheld enlarged value is 2lA. The old troughs are B-(l+1)A,V-(l+1)A,W-(l+1)A, and the enlarged troughs are (2B-1)-(2l+1)A,(2V-1-R)-(2l+1)A,(2W-1-R-R^2)-(2l+1)A. EqualGapsArithmetic proves all four peaks, the three troughs and the final zero for both sources by polynomials in the independent nonnegative integers p-2 and l-2. Existing positive-block and inStrip_append arguments extend these endpoint bounds to every prefix. Existing source_zero, lift_order and marked_word supply the exact Fin-label predicates and literal cut zero.

The arithmetic connects to the group action through physical powers of two. In PeriodicShorteningArithmetic.digit_data, the same physical occurrence carries f and its charge q, and the enlarged value is g=2f-q. With remaining charge Q=A-consumed(q), the old height h=consumed(f) and shadow r=h+Q obey A+consumed(g)=h+r. Keeping the physical label rather than only its numerical value preserves charge and occurrence multiplicity under this lift.

This is the equal-first-three-gap branch of the proposed complete max-plus-two cone. Independent unequal first-three gaps, including the monotone and strict middle-extremum mask constructions, remain formalization obligations. The unrestricted physical J and Circle C3.1 remain OPEN, including parameters below d=max(a,b,c)+2. The result concerns the circle problem of Damasdi, Frankl, Pach and Palvolgyi, arXiv:2504.10687v2.

## References

- Truth anchor: `D5/S3/Combinatorics/Circle/FourNegative/MaxPlusTwo/EqualGaps.actualSource_equal_gaps_first_ear`
- Dependency: [D5/S3/Combinatorics/Circle/FourNegative/FourNegativeEventualJointLift](../FourNegativeEventualJointLift.md)
- Dependency: [D5/S3/Combinatorics/Circle/FourNegative/MaxPlusTwo/EqualGapsArithmetic](EqualGapsArithmetic.md)
- Dependency: [D5/S3/Combinatorics/Circle/FourNegative/MaxPlusTwo/SourceTable](SourceTable.md)
