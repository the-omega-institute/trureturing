# The Shifted Hankel Desnanot-Jacobi Identity

## Abstract

Shifted Hankel determinants of any integral formal power series satisfy the Desnanot-Jacobi identity, including at vanishing determinants.

**Theorem 1.1 (Adjacent shifts and determinant sizes).**

Lean statement: `D5/S3/Combinatorics/MetallicHankel/MetallicHankelUnboundedJacobi.hankel_jacobi`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/MetallicHankel/MetallicHankelUnboundedJacobi.hankel_jacobi` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Guo-Niu Han, Emmanuel Pedon (2025). *Hankel continued fractions and Hankel determinants for q-deformed metallic numbers*. DOI: [10.48550/arXiv.2502.05993](https://doi.org/10.48550/arXiv.2502.05993). URL: <https://arxiv.org/abs/2502.05993v2>.

*Commentary.*

For every integral formal power series Phi and all nonnegative integers ell and j, write Delta_r^{(s)} for the determinant with entries [q^{s+a+b}]Phi and size r. Then (Delta_{j+1}^{(ell+1)})^2 = Delta_{j+1}^{(ell)} Delta_{j+1}^{(ell+2)} - Delta_{j+2}^{(ell)} Delta_j^{(ell+2)}. The empty determinant is one. No determinant is assumed nonzero, and the identity holds also for j equal to zero.

## References

- Truth anchor: `D5/S3/Combinatorics/MetallicHankel/MetallicHankelUnboundedJacobi.hankel_jacobi`
- Dependency: [D5/S3/Combinatorics/MetallicHankel/MetallicHankelDefs](MetallicHankelDefs.md)
