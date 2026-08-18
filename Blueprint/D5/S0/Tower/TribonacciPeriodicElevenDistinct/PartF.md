# Period Eleven Distinct F

## Abstract

Period-eleven phase codes, part F.

Grouping is by four here, not by five as at the shorter levels. Five was tried first and every across-group statement hit the default heartbeat budget; a probe showed three and four both clear it, and four gives the fewest pairs among the workable sizes. The budget was not raised.

**Theorem 1.1 (Period Eleven Distinct F).**

$$\operatorname{Disjoint}\left(\operatorname{flatMap}\left(\mathit{orbitStates}, \mathit{elevenOrbitsG11}\right), \operatorname{flatMap}\left(\mathit{orbitStates}, \mathit{elevenOrbitsG17}\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/TribonacciPeriodicElevenDistinct/PartF.eleven_g11_g17_state_codes_disjoint` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assembling the components into one statement over the whole list is not done here, as at the shorter levels, and remains open.

## References

- Truth anchor: `D5/S0/Tower/TribonacciPeriodicElevenDistinct/PartF.eleven_g11_g17_state_codes_disjoint`
- Dependency: [D5/S0/Tower/TribonacciPeriodicEleven/EnumerationElevenData](../TribonacciPeriodicEleven/EnumerationElevenData.md)
- Dependency: [D5/S0/Tower/TribonacciPeriodicElevenDistinct/PartA](PartA.md)
