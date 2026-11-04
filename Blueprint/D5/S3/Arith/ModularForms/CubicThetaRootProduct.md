# Cubic root specialization of the actual Jacobi product

## Abstract

Cubic root specialization of the actual Jacobi product

For any commutative topological ring and ring homomorphism out of the rational Laurent polynomial ring satisfying w^2+w+1=0 at its Laurent generator, the actual Jacobi series specializes to (1-w) times E(X^3). The root condition factors finite products and is not an assumed theta identity.

**Theorem 1.1 (finite_cubic_root_product).**

Lean statement: `D5/S3/Arith/ModularForms/CubicThetaRootProduct.finite_cubic_root_product`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/ModularForms/CubicThetaRootProduct.finite_cubic_root_product` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Zeyu Huang, Timothy Huber, James McLaughlin, Pengjun Wang, Yan Xu and Dongxi Ye (2025). *Sign-patterns of Certain Infinite Products*. DOI: [10.48550/arXiv.2507.16644](https://doi.org/10.48550/arXiv.2507.16644). URL: <https://arxiv.org/abs/2507.16644v1>.

*Commentary.*

An exact finite factorization, before any limit or division is taken.

**Theorem 1.2 (jacobi_cubic_root_product).**

Lean statement: `D5/S3/Arith/ModularForms/CubicThetaRootProduct.jacobi_cubic_root_product`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/ModularForms/CubicThetaRootProduct.jacobi_cubic_root_product` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Zeyu Huang, Timothy Huber, James McLaughlin, Pengjun Wang, Yan Xu and Dongxi Ye (2025). *Sign-patterns of Certain Infinite Products*. DOI: [10.48550/arXiv.2507.16644](https://doi.org/10.48550/arXiv.2507.16644). URL: <https://arxiv.org/abs/2507.16644v1>.

*Commentary.*

Jacobi's actual formal product at a cubic root is (1-w)E(X^3). The algebraic root condition is used only to factor finite products.

**Theorem 1.3 (cubic_factor).**

Lean statement: `D5/S3/Arith/ModularForms/CubicThetaRootProduct.cubic_factor`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/ModularForms/CubicThetaRootProduct.cubic_factor` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Zeyu Huang, Timothy Huber, James McLaughlin, Pengjun Wang, Yan Xu and Dongxi Ye (2025). *Sign-patterns of Certain Infinite Products*. DOI: [10.48550/arXiv.2507.16644](https://doi.org/10.48550/arXiv.2507.16644). URL: <https://arxiv.org/abs/2507.16644v1>.

*Commentary.*

Three cubic-root polynomial factors multiply to one minus the cube, over any commutative ring.

**Theorem 1.4 (map_tendsto).**

Lean statement: `D5/S3/Arith/ModularForms/CubicThetaRootProduct.map_tendsto`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/ModularForms/CubicThetaRootProduct.map_tendsto` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Zeyu Huang, Timothy Huber, James McLaughlin, Pengjun Wang, Yan Xu and Dongxi Ye (2025). *Sign-patterns of Certain Infinite Products*. DOI: [10.48550/arXiv.2507.16644](https://doi.org/10.48550/arXiv.2507.16644). URL: <https://arxiv.org/abs/2507.16644v1>.

*Commentary.*

Discrete coefficient ring maps preserve coefficientwise power-series convergence.

**Theorem 1.5 (tendsto_expand_three).**

Lean statement: `D5/S3/Arith/ModularForms/CubicThetaRootProduct.tendsto_expand_three`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/ModularForms/CubicThetaRootProduct.tendsto_expand_three` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Zeyu Huang, Timothy Huber, James McLaughlin, Pengjun Wang, Yan Xu and Dongxi Ye (2025). *Sign-patterns of Certain Infinite Products*. DOI: [10.48550/arXiv.2507.16644](https://doi.org/10.48550/arXiv.2507.16644). URL: <https://arxiv.org/abs/2507.16644v1>.

*Commentary.*

Expansion by three preserves coefficientwise convergence.

This is classical intermediate mathematics. CubicThetaCoreProduct supplies the downstream product-to-core lattice identity and EtaSignK6 supplies the exact all-index sign theorem. Independent formal acceptance and publication remain separate; no literature priority or novelty credit is asserted.

## References

- Truth anchor: `D5/S3/Arith/ModularForms/CubicThetaRootProduct.cubic_factor`
- Truth anchor: `D5/S3/Arith/ModularForms/CubicThetaRootProduct.finite_cubic_root_product`
- Truth anchor: `D5/S3/Arith/ModularForms/CubicThetaRootProduct.jacobi_cubic_root_product`
- Truth anchor: `D5/S3/Arith/ModularForms/CubicThetaRootProduct.map_tendsto`
- Truth anchor: `D5/S3/Arith/ModularForms/CubicThetaRootProduct.tendsto_expand_three`
- Dependency: [D5/S3/Arith/ModularForms/CubicThetaJacobi](CubicThetaJacobi.md)
