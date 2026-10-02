# Recursive Enumeration of First-Endpoint Parameters

## Abstract

A three-step recursion enumerates the eligible first-maximum parameters.

**Theorem 1.1 (The family decomposition and count).**

Lean statement: `D5/S3/Combinatorics/FundamentalBijection/ThetaIterateParametrization.first_endpoint_parametrization`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/FundamentalBijection/ThetaIterateParametrization.first_endpoint_parametrization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kassie Archer, Robert P. Laudone (2024). *Pattern avoidance and the fundamental bijection*. DOI: [10.48550/arXiv.2407.06338](https://doi.org/10.48550/arXiv.2407.06338). URL: <https://arxiv.org/abs/2407.06338v1>.

*Commentary.*

Let A(h) consist of first-maximum permutations r of size h for which P(r) avoids 132 through depth two. For h at least six, A(h) is the union of U(h), the decreasing word, W(h), and I applied to the members of A(h minus three) whose cycle from their maximum equals their fundamental image. Its cardinality is the latter count plus three and is the cardinality of A(h minus three) plus two. For every h at least two, the cardinality of A(h) is the integer part of (2h plus one) divided by three.

## References

- Truth anchor: `D5/S3/Combinatorics/FundamentalBijection/ThetaIterateParametrization.first_endpoint_parametrization`
- Dependency: [D5/S3/Combinatorics/FundamentalBijection/ThetaBasicInverseBlocks](ThetaBasicInverseBlocks.md)
- Dependency: [D5/S3/Combinatorics/FundamentalBijection/ThetaBasicInverseGeneral](ThetaBasicInverseGeneral.md)
- Dependency: [D5/S3/Combinatorics/FundamentalBijection/ThetaIterateVFamilies](ThetaIterateVFamilies.md)
- Dependency: [D5/S3/Combinatorics/FundamentalBijection/ThetaIterateWTests](ThetaIterateWTests.md)
