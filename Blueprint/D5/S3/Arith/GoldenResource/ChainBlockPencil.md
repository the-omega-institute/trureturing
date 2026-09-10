# Chain Block Pencil

## Abstract

Unit endpoint couplings preserve positive lower bounds independent of chain length.

Let n be any natural number and put m=n+1. Each hidden chain has m vertices and matrix H(m), with diagonal four and adjacent entries minus one. The hidden space is the direct sum of two identical chains, ordered first chain then second chain. Two visible coordinates precede the hidden coordinates. B has first row the first unit vector of the first chain and second row the first unit vector of the second chain. K(n) has blocks I, B, B transpose, and H(m) direct sum H(m). For real k and b, G(n,k,b) is diagonal: every diagonal entry is k except the last vertex of the first hidden chain, whose entry is k-b. Write V(x) for the sum of coordinate squares and Q(A,x) for x transpose A x. PosSemidef and PosDef denote positive semidefiniteness and positive definiteness. Every statement involving G assumes k at least two and b at most one; in particular it applies to both b=0 and b=1. For the coefficient and combined statements, k and b are integers, and b is also nonnegative. Coeff(n,k,b,i,j) means there exist integers a and c equal to the corresponding entries K(n)(i,j) and G(n,k,b)(i,j), with both absolute values at most max(k,4). Uniform(n,k,b) means K(n) minus one third of the identity is positive semidefinite, G(n,k,b) minus the identity is positive semidefinite, and Coeff(n,k,b,i,j) holds for every pair of coordinates i and j.

**Theorem 1.1 (Uniform mass energy).**

$$\frac{1}{3}\cdot V\left(x\right) \le Q\left(K\left(n\right), x\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GoldenResource/ChainBlockPencil.mass_coercive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each visible scalar a and its chain h, (2a+3h(0)) squared is nonnegative. Thus the cross term is bounded below by minus two thirds of a squared minus three halves of h(0) squared. The first coordinate square is at most the sum of all chain squares. The chain energy is at least twice that sum. Adding the two chains gives the uniform factor one third.

**Theorem 1.2 (The mass matrix inequality).**

$$PosSemidef\left(K\left(n\right)-\frac{1}{3}\cdot I\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GoldenResource/ChainBlockPencil.mass_lower_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The blocks form a real symmetric matrix. Subtracting one third of the identity turns the energy bound into nonnegativity.

**Theorem 1.3 (Positive mass).**

$$PosDef\left(K\left(n\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GoldenResource/ChainBlockPencil.mass_posDef` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A nonzero vector has a positive sum of squares. Its mass energy is therefore strictly positive.

**Theorem 1.4 (The spatial matrix inequality).**

$$PosSemidef\left(G\left(n, k, b\right)-I\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GoldenResource/ChainBlockPencil.spatial_lower_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every unperturbed diagonal entry is at least two. The perturbed entry k-b is at least one. Hence subtracting the identity leaves a nonnegative diagonal matrix.

**Theorem 1.5 (Uniform spatial energy).**

$$V\left(x\right) \le Q\left(G\left(n, k, b\right), x\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GoldenResource/ChainBlockPencil.spatial_coercive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Evaluate the spatial matrix inequality on x.

**Theorem 1.6 (Positive spatial principal part).**

$$PosDef\left(G\left(n, k, b\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GoldenResource/ChainBlockPencil.spatial_posDef` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every diagonal entry is at least one, hence positive.

**Theorem 1.7 (Bounded integer coefficients).**

$$Coeff\left(n, k, b, i, j\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GoldenResource/ChainBlockPencil.coefficient_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Mass entries belong to minus one, zero, one, and four. Spatial entries belong to zero, k, and k-b. With integer k at least two and integer b between zero and one, all these entries are integers of absolute value at most max(k,4).

**Theorem 1.8 (The uniform integer family).**

$$Uniform\left(n, k, b\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GoldenResource/ChainBlockPencil.uniform_pencil_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Combine the mass, spatial, and coefficient estimates. The constants one third, one, and max(k,4) do not depend on n. The visible-to-hidden endpoint coefficients are exactly one and the coefficients between adjacent hidden vertices are minus one.

## References

- Truth anchor: `D5/S3/Arith/GoldenResource/ChainBlockPencil.coefficient_bounds`
- Truth anchor: `D5/S3/Arith/GoldenResource/ChainBlockPencil.mass_coercive`
- Truth anchor: `D5/S3/Arith/GoldenResource/ChainBlockPencil.mass_lower_bound`
- Truth anchor: `D5/S3/Arith/GoldenResource/ChainBlockPencil.mass_posDef`
- Truth anchor: `D5/S3/Arith/GoldenResource/ChainBlockPencil.spatial_coercive`
- Truth anchor: `D5/S3/Arith/GoldenResource/ChainBlockPencil.spatial_lower_bound`
- Truth anchor: `D5/S3/Arith/GoldenResource/ChainBlockPencil.spatial_posDef`
- Truth anchor: `D5/S3/Arith/GoldenResource/ChainBlockPencil.uniform_pencil_bounds`
- Dependency: [D5/S3/Arith/GoldenResource/TridiagonalChainInverse](TridiagonalChainInverse.md)
