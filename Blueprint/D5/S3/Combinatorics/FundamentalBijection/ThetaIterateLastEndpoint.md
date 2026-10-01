# Cycle Reduction at a Final Maximum

## Abstract

A final-maximum parameter reduces to the inverse image of its stem.

**Theorem 1.1 (The stem and its inverse image).**

Lean statement: `D5/S3/Combinatorics/FundamentalBijection/ThetaIterateLastEndpoint.last_endpoint_cycle`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/FundamentalBijection/ThetaIterateLastEndpoint.last_endpoint_cycle` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kassie Archer, Robert P. Laudone (2024). *Pattern avoidance and the fundamental bijection*. DOI: [10.48550/arXiv.2407.06338](https://doi.org/10.48550/arXiv.2407.06338). URL: <https://arxiv.org/abs/2407.06338v1>.

*Commentary.*

For a stem r of size h at least two beginning with h, depth-two avoidance of P of r followed by h plus one forces r to end with one. If r ends with one, its inverse fundamental image begins with h and has fundamental image r, and the P construction avoids through depth two exactly when that inverse image does.

## References

- Truth anchor: `D5/S3/Combinatorics/FundamentalBijection/ThetaIterateLastEndpoint.last_endpoint_cycle`
- Dependency: [D5/S3/Combinatorics/FundamentalBijection/ThetaIterateInsertion](ThetaIterateInsertion.md)
- Dependency: [D5/S3/Combinatorics/FundamentalBijection/ThetaIterateTail](ThetaIterateTail.md)
