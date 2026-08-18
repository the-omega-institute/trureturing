# Period Eleven Assembly

## Abstract

No state code is shared by two of the seventy-four period-eleven representatives.

The fold is the same shape as at the two shorter levels, only longer: nineteen groups rather than nine, because this level is grouped by four. The concatenation is right associated because that is the shape the append and disjointness lemmas expect, and the eighteen tails are named so that no line carries the whole nesting.

Unlike the shorter levels this one calls the pinned library's append lemma directly instead of a local adapter. The adapter restated a lemma that the library already had with the same three hypotheses; that duplication is recorded and is not carried forward here.

**Theorem 1.1 (Period eleven codes have no duplicates).**

$$\operatorname{Nodup}\left(\mathit{seg0}\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/NodupAssembly/PeriodEleven.tribonacci_period_eleven_state_codes_nodup` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The components were already proved: nineteen within-group statements and one hundred and seventy-one across-group statements. Only their combination was missing. That the nineteen groups partition the seventy-four representatives exactly is a property of the group definitions rather than of this theorem, and was checked by reading them.

## References

- Truth anchor: `D5/S0/Tower/NodupAssembly/PeriodEleven.tribonacci_period_eleven_state_codes_nodup`
- Dependency: [D5/S0/Tower/TribonacciPeriodicElevenDistinct/PartA](../TribonacciPeriodicElevenDistinct/PartA.md)
- Dependency: [D5/S0/Tower/TribonacciPeriodicElevenDistinct/PartD](../TribonacciPeriodicElevenDistinct/PartD.md)
- Dependency: [D5/S0/Tower/TribonacciPeriodicElevenDistinct/PartE](../TribonacciPeriodicElevenDistinct/PartE.md)
- Dependency: [D5/S0/Tower/TribonacciPeriodicElevenDistinct/PartF](../TribonacciPeriodicElevenDistinct/PartF.md)
