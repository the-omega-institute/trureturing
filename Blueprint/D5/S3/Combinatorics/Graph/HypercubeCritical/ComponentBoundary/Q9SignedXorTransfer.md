# Parity coupling across opposite cells

## Abstract

Signed XOR transfer for overlapping nine-cube masks

**Theorem 1.1 (Exact transfer for overlapping four-axis eigenvectors).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SignedXorTransfer.overlapping_mask_signed_xor`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SignedXorTransfer.overlapping_mask_signed_xor` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let B be the sum of the signed flips on the three common axes of two masks. Write A and D for their respective exclusive signed flips. Take ambient eigenvectors f and g for B + A and B + D at eigenvalue 2. The two exclusive bits specify the common-cell traces f₀ and g₀, and changing the respective exclusive bit gives f₁ and g₁.

Projecting the eigenvector equations to the common cell gives f₁ = A(2I − B)f₀ and g₁ = D(2I − B)g₀. The two involutions cancel against the ordered signed action AD in the pairing. Self-adjointness and B² = 3I then give the total pairing ⟨f₁, AD g₁⟩ = ⟨f₀, (7I − 4B)g₀⟩.

Let Sₜ be the pairing of the common-cell traces on parity t, Dₜ the signed XOR pairing of the opposite traces on that parity, and L = ⟨f₀, B g₀⟩. Each signed flip reverses parity, yielding D₀ = 3S₀ + 4S₁ − 2L and D₁ = 4S₀ + 3S₁ − 2L. In particular D₀ − D₁ = S₁ − S₀.

For Hong, Wu and Xia's Problem 2, a four-axis face witness with the stated ambient eigenvector equation can be used as the corresponding input. https://arxiv.org/html/2610.09483v1#Thmproblem2

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SignedXorTransfer.overlapping_mask_signed_xor`
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9MaskedSpectrum](Q9MaskedSpectrum.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SignedContactCells](Q9SignedContactCells.md)
