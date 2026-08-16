# D-Bonacci Champion Boundary

## Abstract

The d-bonacci champion values converge to one third at the binary boundary.

**Theorem 1.1 (Champion values tend to one third).**

$$\operatorname{limitAtTop}\left(d, \operatorname{championValue}\left(\operatorname{beta}\left(d\right)\right)\right) = \frac{1}{3}$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/DBonacciGeneral/ChampionBoundary.championValue_dbonacciPerronRoot_tendsto_one_third` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The Perron roots beta(d) tend to two. The denominator of the corrected rational champion expression is three at two, so the expression is continuous there and the composed sequence tends to championValue(2)=1/3.

This is a filter-level limit as d tends to infinity. It is stronger than direct substitution at the endpoint.

## References

- Truth anchor: `D5/S0/Tower/DBonacciGeneral/ChampionBoundary.championValue_dbonacciPerronRoot_tendsto_one_third`
- Dependency: [D5/S0/Tower/DBonacciGeneral/ChampionValue](ChampionValue.md)
