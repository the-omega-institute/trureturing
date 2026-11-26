# Topological entropy of the bilateral Parry shift

## Abstract

Topological entropy of the native bilateral forbidden-run shift.

**Theorem 1.1 (The Perron root gives the topological entropy).**

Lean statement: `D5/S3/TotalVariation/ParryTopologicalEntropy.bilateral_entropy`

*Proof.* Machine-checked in Lean as `D5/S3/TotalVariation/ParryTopologicalEntropy.bilateral_entropy` (`✓ std3`). ∎

*Citation.* Dawoud Ahmadi Dastjerdi and Somaye Jangjoo (2013). *Computations on Sofic S-gap Shifts*. DOI: [10.1007/s12346-013-0096-2](https://doi.org/10.1007/s12346-013-0096-2). URL: <https://arxiv.org/abs/1108.3414>.

*Commentary.*

For k at least two, take all Boolean paths on the integers for which every block of length k contains a false bit. With the product uniform structure, the one-step left shift restricted to this set has cover entropy log(beta_k), where beta_k is the order-k d-bonacci Perron root.

Every finite admissible word extends to a one-sided path by appending false bits. The number of words and the powers of beta_k satisfy the same recurrence. The initial values bound the counts between beta_k^n and 2^k times beta_k^n. Taking logarithms per step supplies the one-sided entropy through the symbolic prefix-growth theorem.

For each nonpositive integer endpoint, reading the forward tail from that endpoint maps the bilateral space onto the same one-sided subshift and intertwines the shifts. These pullback uniformities decrease as the endpoint moves to the left. Every product entourage belongs to one of them, which yields the bilateral entropy from the one-sided law.

## References

- Truth anchor: `D5/S3/TotalVariation/ParryTopologicalEntropy.bilateral_entropy`
- Dependency: [D5/S0/Tower/DBonacci/PerronRoot](../../S0/Tower/DBonacci/PerronRoot.md)
- Dependency: [D5/S1/Dynamics/Symbolic/PrefixGrowthEntropy](../../S1/Dynamics/Symbolic/PrefixGrowthEntropy.md)
- Dependency: [D5/S1/Words/AdmissibleWords/KBonacciIntegerInterval](../../S1/Words/AdmissibleWords/KBonacciIntegerInterval.md)
- Dependency: [D5/S3/TotalVariation/ParryBilateralLaw](ParryBilateralLaw.md)
