# Pure replacement in a real complementary plane

## Abstract

A density supported in the complement of a conjugate pair has a unit vector with the same diagonal.

**Theorem 1.1 (A diagonal-preserving unit vector).**

Lean statement: `D5/S3/Quantum/Measurements/ThreeDistinguishabilityRealCompression.pure_replacement_for_conjugate_pair`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurements/ThreeDistinguishabilityRealCompression.pure_replacement_for_conjugate_pair` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Chi-Kwong Li and Yiu-Tung Poon (2000). *Convexity of the Joint Numerical Range*. DOI: [10.1137/s0895479898343516](https://doi.org/10.1137/s0895479898343516). URL: <https://doi.org/10.1137/s0895479898343516>.

*Commentary.*

For an orthogonal unit pair z and its conjugate, √2 Re z and √2 Im z form a real orthonormal pair. Let C be a real orthonormal basis matrix for their complement. A positive density B annihilating the pair is supported on the complexification of this plane, so B = C(CᵀBC)Cᵀ.

Taking the entrywise real part of the compression gives a real symmetric positive matrix T because its quadratic forms on real vectors agree with those of the positive compression. The same operation preserves trace one and the diagonal after lifting through the real matrix C. Diagonalize T with eigenvalues λ, μ ≥ 0 and λ+μ = 1, and lift the unit real eigenvectors to c,e. The complex unit vector √λ c + i√μ e lies in the same plane. The cross term vanishes in each squared modulus, giving λcᵢ²+μeᵢ² = Bᵢᵢ.

Li and Poon’s Theorem 3.1 gives convexity of the first joint numerical range for measurements in a real symmetric 2 × 2 span. Each effect CᵀEᵢᵢC belongs to that span. Their Theorem 1.2 then gives a rank-one projection with the same four expectations. The Lean construction produces the vector directly from the two real eigenvectors.

## References

- Truth anchor: `D5/S3/Quantum/Measurements/ThreeDistinguishabilityRealCompression.pure_replacement_for_conjugate_pair`
- Dependency: [D5/S3/Quantum/Measurements/ThreeDistinguishabilityCubic](ThreeDistinguishabilityCubic.md)
