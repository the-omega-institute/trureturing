# The corrected physical current seed

## Abstract

The corrected physical current seed

**Theorem 1.1 (The physical minus-one seed).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockCurrentSeedConstruction.actual_current_seed`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockCurrentSeedConstruction.actual_current_seed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

For every original lattice state and actual tensor target, the field of its minus-one current product plus the half-binomial correction sum equals the physical normal insertion. The source-current upper truncation makes the correction sum genuinely finite. No target vacuum, energy bound or module law is assumed.

The singleton at weight one contributes the negative charge pairing divided by two. Each pair of weights one and s has coefficient minus s times choose(1/2,s+1), including the positive one-eighth coefficient when both weights are one. Source partial derivatives retain repeated-colour multiplicities. Finite charge decomposition extends the polynomial identity to the whole original carrier.

The native field exponents use the physical even shifts. The normal insertion retains the negative-current split and the jet exponent plus three.

## References

- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockCurrentSeedConstruction.actual_current_seed`
- Dependency: [D5/S3/VertexAlgebra/LatticeHalfFockCurrentSeed](LatticeHalfFockCurrentSeed.md)
