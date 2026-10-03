# Explicit Exceptional Orbits

## Abstract

Three explicit orbit words leave the avoidance layers at successive depths.

**Theorem 1.1 (The exceptional orbit chain).**

Lean statement: `D5/S3/Combinatorics/FundamentalBijection/ThetaIterateExceptional.cyclic_last_endpoint`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/FundamentalBijection/ThetaIterateExceptional.cyclic_last_endpoint` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kassie Archer, Robert P. Laudone (2024). *Pattern avoidance and the fundamental bijection*. DOI: [10.48550/arXiv.2407.06338](https://doi.org/10.48550/arXiv.2407.06338). URL: <https://arxiv.org/abs/2407.06338v1>.

*Commentary.*

For size n at least three, let C be two through n followed by one and D be n followed by two through n minus one and then one. The fundamental images of C and D are respectively n followed by one through n minus one and C; D avoids 132 through depth two, and P of C followed by n plus one does so as well. For n at least four, let E be P of the increasing word of size n minus two. Its image is D; E lies at depth five but not six, D at depth four but not five, and C at depth three but not four.

## References

- Truth anchor: `D5/S3/Combinatorics/FundamentalBijection/ThetaIterateExceptional.cyclic_last_endpoint`
- Dependency: [D5/S3/Combinatorics/FundamentalBijection/ThetaIterateCycleReduction](ThetaIterateCycleReduction.md)
- Dependency: [D5/S3/Combinatorics/FundamentalBijection/ThetaIterateTail](ThetaIterateTail.md)
- Dependency: [D5/S3/Combinatorics/FundamentalBijection/ThetaIterateVFamilies](ThetaIterateVFamilies.md)
