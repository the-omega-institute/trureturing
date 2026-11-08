# A strict depth bound for the transfer remainder

## Abstract

The unit spectral branch controls transfer powers below the exact determinant-order depth.

**Theorem 1.1 (One fixed unit branch for every admissible block and depth).**

Lean statement: `D5/S3/Combinatorics/MetallicHankel/MetallicHankelEndpointSpectral.transfer_spectral_remainder`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/MetallicHankel/MetallicHankelEndpointSpectral.transfer_spectral_remainder` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Guo-Niu Han, Emmanuel Pedon (2025). *Hankel continued fractions and Hankel determinants for q-deformed metallic numbers*. DOI: [10.48550/arXiv.2502.05993](https://doi.org/10.48550/arXiv.2502.05993). URL: <https://arxiv.org/abs/2502.05993v2>.

*Commentary.*

Let U be a two-by-two matrix over rational formal power series. Suppose its trace has constant coefficient one and its determinant is q^D for a positive integer D. There are a fixed power series a with a(0)=1 and a fixed matrix E such that the coefficient of degree h in every entry of U^K equals that in a^K E whenever h<D*K. The same a and E work for every natural K and every admissible depth. The condition is evaluated at the actual K.

Hensel lifting gives the characteristic root a with constant coefficient one. Its inverse defines b=q^D/a, and the characteristic equation gives trace(U)=a+b. The difference a-b is a unit. Define E=(U-bI)/(a-b) and F=I-E. The existing two-by-two Cayley-Hamilton power recurrence gives U^K=a^K E+b^K F by induction, including powers zero and one. Since b^K=q^(D*K)/a^K, the second summand has zero coefficients at every degree below D*K.

For the ordinary denominator block in the metallic construction, D=2*rho gives exactly h<2*K*rho. MetallicHankelBlocks.ordinary_blocks supplies this trace constant coefficient and determinant for the actual continuants. MetallicHankelEndpointJets combines the branch with polynomial unit-power coefficients, and MetallicHankelResiduePolynomials consumes those jets in the exact complementary boundary. The theorem does not replace them by eventual equality.

## References

- Truth anchor: `D5/S3/Combinatorics/MetallicHankel/MetallicHankelEndpointSpectral.transfer_spectral_remainder`
- Dependency: [D5/S0/Observation/MatrixTracePowerSum](../../../S0/Observation/MatrixTracePowerSum.md)
