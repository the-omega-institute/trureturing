# Exact seed budgets for coloured parity profiles

## Abstract

Exact uniform seed budgets for two coloured parity laws are multiples of four times a parity class.

**Theorem 1.1 (Exactly which seed counts realize the two uniform parity laws).**

$$\forall n \in Nat,\; \forall N \in Nat,\; \operatorname{Implements}\left(n, N\right) \Leftrightarrow 2^{n + 3} \mid N$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Attribution/ParitySeedBudget.exact_seed_budget` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The cube has n+2 coordinates for a natural number n. The group consists of binary acting vectors under coordinatewise addition. The two output sets are the even and odd profiles with one binary colour, respectively. The action preserves the profile and adds the acting vector over its zero coordinates to the colour. Implements(n,N) means there is a finite group set S of cardinality N and an equivariant map from S to the product of the two output sets, such that a common natural count k is the number of seeds above every output of either projection. For positive N these counts give the uniform laws. The empty seed set realizes N=0.

The pushforward counts are invariant. For a pair with neither profile all ones, the four colour counts in that cell are equal. The profile obtained from the all-ones vector by clearing two coordinates is in the same parity class and supplies a row or column entirely divisible by four. The common marginal then forces the remaining cells to be divisible by four as well. Summing the cells gives the necessary modulus.

For sufficiency, match even and odd profiles with identical tails. Use all four pairs of colours over each matched pair, repeated as many times as the budget multiplier. The copy construction gives a finite group set, with the prescribed cardinality and equal counts above every output in each parity class.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Attribution/ParitySeedBudget.exact_seed_budget`
- Dependency: [D5/S3/ConceptDynamics/Attribution/CoordinateColourOrbit](CoordinateColourOrbit.md)
- Dependency: [D5/S3/ConceptDynamics/Attribution/UniformTableCalibration](UniformTableCalibration.md)
