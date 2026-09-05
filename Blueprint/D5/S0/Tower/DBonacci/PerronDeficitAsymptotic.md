# D-Bonacci Perron Deficit Asymptotic

## Abstract

The d-bonacci Perron-root deficit is sharply asymptotic to the negative d-th power of two.

**Theorem 1.1 (The normalized Perron deficit tends to one).**

$$\operatorname{limitAtTop}\left(d, \operatorname{div}\left(2 - \operatorname{dbonacciPerronRoot}\left(d\right), \operatorname{pow}\left(\operatorname{inv}\left(2\right), d\right)\right)\right) = 1$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/DBonacci/PerronDeficitAsymptotic.dbonacci_perron_deficit_asymptotic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every order d at least two, the frozen characteristic-equation identity rewrites the endpoint deficit as the negative d-th power of the Perron root. Dividing by 2 to the negative d then gives the d-th power of 2 divided by that root.

The logarithm of this normalized ratio is nonnegative. Its scaled value is bounded above by the golden-ratio reciprocal times d times the d-th power of that reciprocal. Mathlib's polynomial-times-geometric limit sends this majorant to zero, and continuity of the real exponential sends the normalized deficit to one.

The denominator is nonzero for every natural order. The totalized values below order two do not affect the at-top limit, and no numerical approximation is used.

## References

- Truth anchor: `D5/S0/Tower/DBonacci/PerronDeficitAsymptotic.dbonacci_perron_deficit_asymptotic`
- Dependency: [D5/S0/Tower/DBonacci/PerronRoot](PerronRoot.md)
