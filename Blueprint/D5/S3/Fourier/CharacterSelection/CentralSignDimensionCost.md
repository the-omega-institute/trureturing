# Dimension cost of separating central signs

## Abstract

Joint separation of a binary cube places a sharp lower bound on the sum of squares of channel dimensions.

**Theorem 1.1 (The cost bound and its equality case).**

$$\begin{aligned}&k \le m, 1+r+\sum_j d_j^2 \ge 4k+1\\&1+r+\sum_j d_j^2=4k+1 \Leftrightarrow m=k,r=0, \forall j,d_j=2, \sigma \text{bijective}\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/CharacterSelection/CentralSignDimensionCost.central_sign_dimension_cost` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The complete binary profile of each k-bit string consists of r constant readings of dimension one and m further readings of integer dimensions at least two. Include one distinguished trivial channel of dimension one. If the complete profile separates all strings, the remaining profile σ alone is injective. Hence its codomain of size 2ᵐ contains at least 2ᵏ values. Each squared dimension costs at least four, and a dimension above two contributes strictly more. At equality there are no additional one-dimensional channels, every remaining dimension is two, and σ is a bijection of equally large cubes. In the compact-group application, the commutator condition is what makes the one-dimensional central restrictions constant.

## References

- Truth anchor: `D5/S3/Fourier/CharacterSelection/CentralSignDimensionCost.central_sign_dimension_cost`
