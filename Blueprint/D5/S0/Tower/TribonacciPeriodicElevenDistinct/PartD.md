# Period Eleven Distinct D

## Abstract

Period-eleven phase codes, part D.

Grouping is by four here, not by five as at the shorter levels. Five was tried first and every across-group statement hit the default heartbeat budget; a probe showed three and four both clear it, and four gives the fewest pairs among the workable sizes. The budget was not raised.

**Theorem 1.1 (Period Eleven Distinct D).**

$$\operatorname{Disjoint}\left(\operatorname{flatMap}\left(\mathit{orbitStates}, \mathit{elevenOrbitsG05}\right), \operatorname{flatMap}\left(\mathit{orbitStates}, \mathit{elevenOrbitsG10}\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/TribonacciPeriodicElevenDistinct/PartD.eleven_g05_g10_state_codes_disjoint` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assembling the components into one statement over the whole list is not done here, as at the shorter levels, and remains open.

## References

- Truth anchor: `D5/S0/Tower/TribonacciPeriodicElevenDistinct/PartD.eleven_g05_g10_state_codes_disjoint`
- Dependency: [D5/S0/Tower/TribonacciPeriodicEleven/EnumerationElevenData](../TribonacciPeriodicEleven/EnumerationElevenData.md)
- Dependency: [D5/S0/Tower/TribonacciPeriodicElevenDistinct/PartC](PartC.md)
