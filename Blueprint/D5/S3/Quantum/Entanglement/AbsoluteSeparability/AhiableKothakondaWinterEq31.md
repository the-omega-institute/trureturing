# Ahiable--Kothakonda--Winter Eq. (31) and absolute separability

## Abstract

The linear spectral condition in Eq. (31) implies absolute separability.

**Definition 1.1 (The spectral condition).**

$$\forall (m:\mathbb{N}), \forall (n:\mathbb{N}), ((2\leq m)\land (m\leq n))\Rightarrow \forall (rho:Matrix\left(Fin\left(m\right)\times Fin\left(n\right), Fin\left(m\right)\times Fin\left(n\right), \mathbb{C}\right)), ((PosSemidef\left(rho\right))\land (trace\left(rho\right)=1))\Rightarrow (\sum_{k:Fin\left(m-1\right)} lambda\left(k\right)\leq 2\cdot lambda\left(m\cdot n-1\right)+\sum_{k:Fin\left(m-1\right)} lambda\left(m\cdot n-k-2\right))\Rightarrow \forall (U:Matrix\left(Fin\left(m\right)\times Fin\left(n\right), Fin\left(m\right)\times Fin\left(n\right), \mathbb{C}\right)), (U\in unitaryGroup\left(Fin\left(m\right)\times Fin\left(n\right), \mathbb{C}\right))\Rightarrow separableCone\left(U\cdot rho\cdot star\left(U\right)\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/AbsoluteSeparability/AhiableKothakondaWinterEq31.claim` (`✓ std3`).

*Citation.* Jennifer Ahiable; Naga Bhavya Teja Kothakonda; Andreas Winter (2026). *The geometry of absolute separability and other convex matrix properties from spectrum*. DOI: [10.48550/arXiv.2608.03390](https://doi.org/10.48550/arXiv.2608.03390). URL: <https://arxiv.org/abs/2608.03390v2>.

*Commentary.*

Theorem 6.2, Eq. (31), assumes a decreasingly ordered spectrum λ₁ ≥ ⋯ ≥ λ_mn ≥ 0 and requires 2λ_mn + Σ_{k=1}^{m−1} λ_{mn−k} ≥ Σ_{k=1}^{m−1} λ_k. Section 7 asks whether this condition implies absolute separability. The definition in Section 1 requires every global unitary conjugate UρU† to remain separable. The statement quantifies all 2 ≤ m ≤ n, every positive semidefinite trace-one state, and every global unitary, using separableCone, the cone of finite sums of Kronecker products of positive semidefinite factors. In the displayed formula lambda(i) is the decreasing eigenvalues₀ of rho at zero-based index i; lambda(0) ≥ ⋯ ≥ lambda(mn−1) ≥ 0.

**Theorem 1.2 (Absolute separability follows).**

$$claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsoluteSeparability/AhiableKothakondaWinterEq31.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jennifer Ahiable; Naga Bhavya Teja Kothakonda; Andreas Winter (2026). *The geometry of absolute separability and other convex matrix properties from spectrum*. DOI: [10.48550/arXiv.2608.03390](https://doi.org/10.48550/arXiv.2608.03390). URL: <https://arxiv.org/abs/2608.03390v2>.

*Commentary.*

The spectral theorem orders an eigenbasis and telescopes the spectrum into the identity, the codimension-one projection ray, and the rays a_k I + 2P_k with a_k = min(k,m−1,mn−k−1). The three existing ray constructions prove separability of each summand; Eq. (31) makes the identity coefficient nonnegative. Finite sums and nonnegative scalings preserve separability.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/AbsoluteSeparability/AhiableKothakondaWinterEq31.claim`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsoluteSeparability/AhiableKothakondaWinterEq31.result`
- Dependency: [D5/S3/Quantum/Entanglement/AbsoluteSeparability/ContractionBlocks](ContractionBlocks.md)
- Dependency: [D5/S3/Quantum/Entanglement/AbsoluteSeparability/GurvitsBarnumBall](GurvitsBarnumBall.md)
- Dependency: [D5/S3/Quantum/Entanglement/AbsoluteSeparability/LowRankRays](LowRankRays.md)
