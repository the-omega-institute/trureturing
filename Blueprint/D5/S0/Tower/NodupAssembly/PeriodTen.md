# Period Ten Assembly

## Abstract

No state code is shared by two of the forty-two period-ten representatives.

The adapter and the append lemma come from the period-nine assembly rather than being restated, so there is one definition of each. The concatenation is right associated because that is the shape the append and disjointness lemmas expect; the nine tails are named so that no line carries the whole nesting.

**Theorem 1.1 (Period ten codes have no duplicates).**

$$\operatorname{Nodup}\left(\mathit{seg0}\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/NodupAssembly/PeriodTen.ten_all_codes_nodup` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The components were already proved: nine within-group statements and thirty-six across-group statements. Only their combination was missing, and it was deferred once at each of three levels before being retried.

## References

- Truth anchor: `D5/S0/Tower/NodupAssembly/PeriodTen.ten_all_codes_nodup`
- Dependency: [D5/S0/Tower/NodupAssembly/PeriodNine](PeriodNine.md)
- Dependency: [D5/S0/Tower/TribonacciPeriodicTen/EnumerationTenDistinctB](../TribonacciPeriodicTen/EnumerationTenDistinctB.md)
