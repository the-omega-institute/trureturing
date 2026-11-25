# Symmetric unitary bases from parallel classes

## Abstract

Symmetric unitary bases from parallel classes.

**Theorem 1.1 (Hilbert–Schmidt pairing within one class).**

$$\operatorname{hs}\left(U_{\alpha}, U_{\psi}\right) = \frac{1}{4} \operatorname{card}\left(G\right) \delta_{\alpha,\psi}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/WernerHolevo/AffineNineAssembly.hollow_hs` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume the block unitary is symmetric, hollow, and has squared entry magnitude one eighth away from the diagonal. Use a bijection from all unordered block edges onto a finite additive group G. For each pair of complex additive characters of G, diagonal character congruence multiplies each entry by the character applied to the sum of its endpoint labels. The Kronecker delta in the formula is one for equal characters and zero otherwise. Summing over both orientations of each edge gives one fourth of the group character pairing.

## References

- Truth anchor: `D5/S3/Quantum/QuantumChannels/WernerHolevo/AffineNineAssembly.hollow_hs`
