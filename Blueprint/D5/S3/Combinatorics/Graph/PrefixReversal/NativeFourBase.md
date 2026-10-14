# Actual Big-3 Hamilton Cycle at Size Four

## Abstract

The three actual prefix reversals of lengths four, three and two admit a Hamilton cycle on every permutation of four labels.

**Theorem 1.1 (Close the Actual Zero-Star Complement).**

$$\exists base \in \mathrm{Configuration}\left(3\right),\; \exists w \in \mathrm{Walk}\left(\mathrm{mulCayley}\left(\mathrm{generatorTriple}\left(3\right)\right), base, base\right),\; \mathrm{IsHamiltonianCycle}\left(w\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PrefixReversal/NativeFourBase.native_four_hamiltonian_cycle` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Apply the existing zeroStar_b_complement_hamiltonian theorem at m=3 to the identity permutation, marked label zero and its deletion residual. The literal complementary word gives a Hamilton path of length 23 from the identity to its actual three-prefix reversal.

A Hamilton path has as many support vertices as its finite domain. Thus this independently specified deletion star has 24 elements. The full group on four labels also has 4!=24 elements, so its injective subtype inclusion is bijective. Mapping the actual path therefore visits every permutation exactly once.

The removed edge is an actual Cayley edge labeled by the three-prefix reversal. Add it in front of the mapped path to obtain a closed walk whose tail is Hamiltonian and whose length is 24. The standard cycle criterion then proves Hamiltonicity of this concrete closed walk.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeFourBase.native_four_hamiltonian_cycle`
- Dependency: [D5/S3/Combinatorics/Graph/PrefixReversalZeroStarComplement](../PrefixReversalZeroStarComplement.md)
