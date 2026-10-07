# A Cofactor Identity at Normal Hankel Indices

## Abstract

Two orthogonal moment relations determine the shifted cofactor of a unit Hankel determinant.

**Theorem 1.1 (The shifted cofactor from moment relations).**

Lean statement: `D5/S3/Combinatorics/MetallicHankel/MetallicHankelUnboundedCofactor.normal_cofactor`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/MetallicHankel/MetallicHankelUnboundedCofactor.normal_cofactor` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Guo-Niu Han, Emmanuel Pedon (2025). *Hankel continued fractions and Hankel determinants for q-deformed metallic numbers*. DOI: [10.48550/arXiv.2502.05993](https://doi.org/10.48550/arXiv.2502.05993). URL: <https://arxiv.org/abs/2502.05993v2>.

*Commentary.*

Let Phi be an integral formal power series, ell a nonnegative integer and m a positive integer. Let c and b be integer sequences and h an integer. Suppose c_m = 1, and b_1 = 0 when m = 1. For each t from zero through m-1, suppose the sum of c_r [q^{ell+r+t}]Phi over r from zero through m is zero. For each t from zero through m-2, suppose the sum of b_r [q^{ell+r+t}]Phi over r from zero through m-1 is zero, and suppose that the latter sum at t = m-1 equals h. If Delta_m^{(ell)} is an integer unit, then h Delta_{m-1}^{(ell+2)} = Delta_m^{(ell)}(c_1 b_0 - c_0 b_1). The unit condition means that Delta_m^{(ell)} is either one or minus one; no nonvanishing condition is imposed on the smaller determinant.

## References

- Truth anchor: `D5/S3/Combinatorics/MetallicHankel/MetallicHankelUnboundedCofactor.normal_cofactor`
- Dependency: [D5/S3/Combinatorics/MetallicHankel/MetallicHankelDeterminants](MetallicHankelDeterminants.md)
