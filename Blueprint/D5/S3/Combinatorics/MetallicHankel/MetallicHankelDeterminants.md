# Integral Hankel Zero Runs and Shift Relations

## Abstract

A monic moment relation determines a Hankel zero interval, its endpoint and the determinant at the next shift without division.

**Theorem 1.1 (The determinant formula from a zero run of moments).**

Lean statement: `D5/S3/Combinatorics/MetallicHankel/MetallicHankelDeterminants.zero_run`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/MetallicHankel/MetallicHankelDeterminants.zero_run` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Guo-Niu Han, Emmanuel Pedon (2025). *Hankel continued fractions and Hankel determinants for q-deformed metallic numbers*. DOI: [10.48550/arXiv.2502.05993](https://doi.org/10.48550/arXiv.2502.05993). URL: <https://arxiv.org/abs/2502.05993v2>.

*Commentary.*

Let Phi(q) = sum_{r >= 0} f_r q^r be an integral formal power series, let ell and s be nonnegative integers and let m be positive. Suppose c_s = 1, sum_{r=0}^s c_r f_{ell+r+t} = 0 for every nonnegative t less than s+m-1, and sum_{r=0}^s c_r f_{ell+r+s+m-1} = h. Then Delta_{s+m}^{(ell)} = (-1)^{m(m-1)/2} h^m Delta_s^{(ell)}; Delta_j^{(ell)} = 0 whenever s < j < s+m; and Delta_s^{(ell+1)} = (-1)^s Delta_s^{(ell)} c_0. These equalities hold over the integers even when h or Delta_s^{(ell)} vanishes.

## References

- Truth anchor: `D5/S3/Combinatorics/MetallicHankel/MetallicHankelDeterminants.zero_run`
- Dependency: [D5/S3/Combinatorics/MetallicHankel/MetallicHankelDefs](MetallicHankelDefs.md)
