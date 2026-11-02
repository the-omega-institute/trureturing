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

The three finite Jacobi factors collapse exactly to (1-w) times the finite Euler product at X cubed. No division or limiting argument occurs in this theorem.

**Theorem 1.2 (jacobi_cubic_root_product).**

Lean statement: `D5/S3/Arith/ModularForms/CubicThetaRootProduct.jacobi_cubic_root_product`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/ModularForms/CubicThetaRootProduct.jacobi_cubic_root_product` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Zeyu Huang, Timothy Huber, James McLaughlin, Pengjun Wang, Yan Xu and Dongxi Ye (2025). *Sign-patterns of Certain Infinite Products*. DOI: [10.48550/arXiv.2507.16644](https://doi.org/10.48550/arXiv.2507.16644). URL: <https://arxiv.org/abs/2507.16644v1>.

*Commentary.*

Coefficientwise convergence of those finite factorizations proves the actual all-index formal product specialization.

This is classical intermediate mathematics. The product-to-core lattice identity and the complete original k6 sign theorem are separate remaining obligations; no original-problem completion or novelty credit is asserted.

## References

- Truth anchor: `D5/S3/Arith/ModularForms/CubicThetaRootProduct.finite_cubic_root_product`
- Truth anchor: `D5/S3/Arith/ModularForms/CubicThetaRootProduct.jacobi_cubic_root_product`
- Dependency: [D5/S3/Arith/ModularForms/CubicThetaJacobi](CubicThetaJacobi.md)
