# Counting Parameters with a Final Maximum

## Abstract

Parameters ending at their maximum are counted by a smaller family beginning at its maximum.

**Theorem 1.1 (The final-maximum parameter count).**

Lean statement: `D5/S3/Combinatorics/FundamentalBijection/ThetaIterateEndpointCount.last_endpoint_count`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/FundamentalBijection/ThetaIterateEndpointCount.last_endpoint_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kassie Archer, Robert P. Laudone (2024). *Pattern avoidance and the fundamental bijection*. DOI: [10.48550/arXiv.2407.06338](https://doi.org/10.48550/arXiv.2407.06338). URL: <https://arxiv.org/abs/2407.06338v1>.

*Commentary.*

For n at least two, the number of parameter permutations of size n plus one ending with n plus one whose P images avoid 132 through depth two equals one plus the number of depth-two avoiders of size n beginning with n.

## References

- Truth anchor: `D5/S3/Combinatorics/FundamentalBijection/ThetaIterateEndpointCount.last_endpoint_count`
- Dependency: [D5/S3/Combinatorics/FundamentalBijection/ThetaBasicInverseTail](ThetaBasicInverseTail.md)
- Dependency: [D5/S3/Combinatorics/FundamentalBijection/ThetaIterateEndpointShape](ThetaIterateEndpointShape.md)
- Dependency: [D5/S3/Combinatorics/FundamentalBijection/ThetaIterateEndpoints](ThetaIterateEndpoints.md)
