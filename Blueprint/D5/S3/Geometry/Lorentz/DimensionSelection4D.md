# Four-dimensional selection by curvature and angular summability

## Abstract

A nonzero trace-free null screen, angular trace summability, and even dimension select four dimensions.

**Theorem 1.1 (Dimension of algebraic curvature).**

Lean statement: `D5/S3/Geometry/Lorentz/DimensionSelection4D.finrank_algebraicCurvature`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/DimensionSelection4D.finrank_algebraicCurvature` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* A. Z. Petrov (2000). *The Classification of Spaces Defining Gravitational Fields*. DOI: [10.1023/A:1001910908054](https://doi.org/10.1023/A:1001910908054). URL: <https://link.springer.com/article/10.1023/A:1001910908054>.

*Commentary.*

For D ≥ 3 the real dimension is D²(D² − 1)/12. Pair skew symmetry and exchange symmetry reduce the tensor to a symmetric array on increasing pairs. The Bianchi expression is alternating, so its increasing quadruple coordinates suffice. The Bianchi map splits by assigning each quadruple to the pairing of its first two and last two indices. Rank–nullity subtracts the number of quadruples from the symmetric pair-array dimension.

**Theorem 1.2 (A section of Ricci contraction).**

Lean statement: `D5/S3/Geometry/Lorentz/DimensionSelection4D.ricci_right_inverse`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/DimensionSelection4D.ricci_right_inverse` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In D ≥ 3, contracting the Kulkarni–Nomizu product of the metric with a symmetric form P gives (D − 2)P + tr_g(P)g. For a prescribed Ricci form T, take P = (T − tr_g(T)g/(2(D − 1)))/(D − 2). Its contraction is T.

**Theorem 1.3 (Dimension of Weyl curvature).**

Lean statement: `D5/S3/Geometry/Lorentz/DimensionSelection4D.finrank_weyl`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/DimensionSelection4D.finrank_weyl` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* A. Z. Petrov (2000). *The Classification of Spaces Defining Gravitational Fields*. DOI: [10.1023/A:1001910908054](https://doi.org/10.1023/A:1001910908054). URL: <https://link.springer.com/article/10.1023/A:1001910908054>.

*Commentary.*

For D ≥ 3 the Ricci kernel has real dimension D(D + 1)(D + 2)(D − 3)/12. The right inverse of Ricci contraction subtracts precisely D(D + 1)/2 symmetric coordinates.

**Theorem 1.4 (Dimension of the trace-free screen).**

Lean statement: `D5/S3/Geometry/Lorentz/DimensionSelection4D.finrank_screenSTF`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/DimensionSelection4D.finrank_screenSTF` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The screen has D − 2 coordinates for D ≥ 3. Trace on its symmetric forms is onto by taking a scalar multiple of the screen metric. The trace kernel has real dimension D(D − 3)/2, positive precisely from D = 4.

**Theorem 1.5 (The trace-free tide is the Weyl tide).**

Lean statement: `D5/S3/Geometry/Lorentz/DimensionSelection4D.screen_tide_weyl_invariance`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/DimensionSelection4D.screen_tide_weyl_invariance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In the standard Lorentz null frame, contract on the generator e₀ + e₁ and the transverse coordinate screen. The Ricci lift shifts the tide by a scalar multiple of the screen metric. The Weyl tide has zero trace, so subtracting the average trace leaves exactly that tide.

**Theorem 1.6 (Ricci agrees in the four-dimensional oriented basis).**

Lean statement: `D5/S3/Geometry/Lorentz/DimensionSelection4D.curvature4_ricci`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/DimensionSelection4D.curvature4_ricci` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* A. Z. Petrov (2000). *The Classification of Spaces Defining Gravitational Fields*. DOI: [10.1023/A:1001910908054](https://doi.org/10.1023/A:1001910908054). URL: <https://link.springer.com/article/10.1023/A:1001910908054>.

*Commentary.*

Evaluate the general curvature form in pair order (01, 02, 03, 23, 31, 12). The sign of the reversed pair 31 gives the Bianchi trace condition and the Ricci contraction agrees entrywise.

**Theorem 1.7 (Four-dimensional curvature, Weyl, and screen ranks).**

Lean statement: `D5/S3/Geometry/Lorentz/DimensionSelection4D.four_dimensional_compatibility`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/DimensionSelection4D.four_dimensional_compatibility` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The general curvature and Weyl dimensions agree with the four-dimensional oriented spaces, with ranks 20 and 10. The real trace-free screen rank is 2.

**Theorem 1.8 (Summability of the angular model).**

Lean statement: `D5/S3/Geometry/Lorentz/DimensionSelection4D.summable_angularMode_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/DimensionSelection4D.summable_angularMode_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

The sum of (ℓ + 1)^(D − 7) over nonnegative integers ℓ converges exactly for D ≤ 5. The shift removes the index zero, and the real power-series criterion requires exponent strictly below −1.

**Theorem 1.9 (Two-sided comparison).**

Lean statement: `D5/S3/Geometry/Lorentz/DimensionSelection4D.angular_trace_summable_iff_of_eventually_comparable`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/DimensionSelection4D.angular_trace_summable_iff_of_eventually_comparable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

If a nonnegative angular contribution is eventually bounded above and below by positive multiples of the model term, the same summability threshold holds. The comparison is a hypothesis on the physical contributions.

**Theorem 1.10 (Selection by even dimension).**

Lean statement: `D5/S3/Geometry/Lorentz/DimensionSelection4D.unique_dimension_four_of_weyl_modular_chiral`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/DimensionSelection4D.unique_dimension_four_of_weyl_modular_chiral` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

A positive screen dimension gives D ≥ 4. Summability gives D ≤ 5. Of these dimensions only four is even, and dimension four satisfies all three conditions.

**Theorem 1.11 (Selection by Hodge degree).**

Lean statement: `D5/S3/Geometry/Lorentz/DimensionSelection4D.unique_dimension_four_of_weyl_modular_hodge`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/DimensionSelection4D.unique_dimension_four_of_weyl_modular_hodge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The complementary degree of a two-form is D − 2. Requiring this degree to equal two gives D = 4, where the screen is positive and the angular model is summable.

## References

- Truth anchor: `D5/S3/Geometry/Lorentz/DimensionSelection4D.angular_trace_summable_iff_of_eventually_comparable`
- Truth anchor: `D5/S3/Geometry/Lorentz/DimensionSelection4D.curvature4_ricci`
- Truth anchor: `D5/S3/Geometry/Lorentz/DimensionSelection4D.finrank_algebraicCurvature`
- Truth anchor: `D5/S3/Geometry/Lorentz/DimensionSelection4D.finrank_screenSTF`
- Truth anchor: `D5/S3/Geometry/Lorentz/DimensionSelection4D.finrank_weyl`
- Truth anchor: `D5/S3/Geometry/Lorentz/DimensionSelection4D.four_dimensional_compatibility`
- Truth anchor: `D5/S3/Geometry/Lorentz/DimensionSelection4D.ricci_right_inverse`
- Truth anchor: `D5/S3/Geometry/Lorentz/DimensionSelection4D.screen_tide_weyl_invariance`
- Truth anchor: `D5/S3/Geometry/Lorentz/DimensionSelection4D.summable_angularMode_iff`
- Truth anchor: `D5/S3/Geometry/Lorentz/DimensionSelection4D.unique_dimension_four_of_weyl_modular_chiral`
- Truth anchor: `D5/S3/Geometry/Lorentz/DimensionSelection4D.unique_dimension_four_of_weyl_modular_hodge`
- Dependency: [D5/S3/Geometry/Lorentz/WeylNullScreen](WeylNullScreen.md)
