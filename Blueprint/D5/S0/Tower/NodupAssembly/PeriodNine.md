# Period Nine Assembly

## Abstract

No state code is shared by two of the twenty-six period-nine representatives.

This assembly was deferred three times, at periods nine, ten and eleven, each time on the ground that the shape after the append lemma does not match a flat tuple. That was true and not an obstacle: the append lemma wants a pairwise inequality where the components give disjointness, and the gap is a three-line adapter. The fold over six groups is then mechanical.

**Theorem 1.1 (Period nine codes have no duplicates).**

$$\operatorname{Nodup}\left(\mathit{nineAllCodes}\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/NodupAssembly/PeriodNine.nine_all_codes_nodup` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The components were already proved: six within-group statements and fifteen across-group statements. Only their combination was missing.

## References

- Truth anchor: `D5/S0/Tower/NodupAssembly/PeriodNine.nine_all_codes_nodup`
- Dependency: [D5/S0/Tower/TribonacciPeriodicNine/EnumerationNineDistinct](../TribonacciPeriodicNine/EnumerationNineDistinct.md)
