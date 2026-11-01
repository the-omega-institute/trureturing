# Unequal block dilation spectra

## Abstract

Positive second eigenvalues of unequal Hermitian block dilations.

**Theorem 1.1 (The complex unequal-block identity).**

Lean statement: `D5/S3/SpectralTopology/RectangularDilation.unequal_dilation_second`

*Proof.* Machine-checked in Lean as `D5/S3/SpectralTopology/RectangularDilation.unequal_dilation_second` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Rad Sarar Anando (2026). *Second adjacency eigenvalue of Apollonian networks: is theta_2(G_m)/2^(m/2) -> sqrt(2)?*. URL: <https://mathoverflow.net/questions/516405>.

*Commentary.*

For arbitrary finite types I and J with decidable equality, let B be a complex I by J matrix and let P=[[0,B],[B*,0]] be Hermitian. Suppose I has at least two elements and the second decreasing eigenvalue of BB* is strictly positive. The second decreasing real eigenvalue of P equals the positive square root of the second decreasing eigenvalue of BB*. Both lists count algebraic multiplicity. The two block sizes may differ or the second block may be empty; strict positivity rules out insufficient positive rank. Zero padding preserves the positive ordered prefix. A permutation identifies the square padded dilation with P plus a zero block; roots of characteristic polynomials retain signs and multiplicities.

**Theorem 1.2 (Real inclusion preserves the ordered spectrum).**

Lean statement: `D5/S3/SpectralTopology/RectangularDilation.eigenvalues_ofReal`

*Proof.* Machine-checked in Lean as `D5/S3/SpectralTopology/RectangularDilation.eigenvalues_ofReal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Rad Sarar Anando (2026). *Second adjacency eigenvalue of Apollonian networks: is theta_2(G_m)/2^(m/2) -> sqrt(2)?*. URL: <https://mathoverflow.net/questions/516405>.

*Commentary.*

For any finite index type with decidable equality, a Hermitian real matrix and its entrywise inclusion in the complex field have identical decreasing real eigenvalue lists. The equality preserves characteristic-polynomial multiplicities and all indices.

**Theorem 1.3 (The real unequal-block identity).**

Lean statement: `D5/S3/SpectralTopology/RectangularDilation.unequal_real_dilation_second`

*Proof.* Machine-checked in Lean as `D5/S3/SpectralTopology/RectangularDilation.unequal_real_dilation_second` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Rad Sarar Anando (2026). *Second adjacency eigenvalue of Apollonian networks: is theta_2(G_m)/2^(m/2) -> sqrt(2)?*. URL: <https://mathoverflow.net/questions/516405>.

*Commentary.*

For arbitrary finite types I and J with decidable equality, let B be a real I by J matrix and let P=[[0,B],[transpose B,0]] be Hermitian. If I has at least two elements and the second decreasing eigenvalue of BB* is strictly positive, the second decreasing real eigenvalue of P equals its positive square root. For real matrices B*=transpose B. The proof embeds entries in the complex field, transports the full characteristic-root multiset and its decreasing order, and applies the complex unequal-block identity.

## References

- Truth anchor: `D5/S3/SpectralTopology/RectangularDilation.eigenvalues_ofReal`
- Truth anchor: `D5/S3/SpectralTopology/RectangularDilation.unequal_dilation_second`
- Truth anchor: `D5/S3/SpectralTopology/RectangularDilation.unequal_real_dilation_second`
- Dependency: [D5/S3/Quantum/Matrix/LinGProperty/ArithmeticBound](../Quantum/Matrix/LinGProperty/ArithmeticBound.md)
