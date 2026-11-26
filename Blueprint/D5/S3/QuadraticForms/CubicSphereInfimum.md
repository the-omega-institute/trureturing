# Sharp sphere bound for an increasing odd cubic

## Abstract

For h(t) = (3t − t³)/2 the infimum of R_h(x)² over unit vectors is 16(17 − 9√3)/23, never attained.

**Definition 1.1 (The cubic).**

Lean statement: `D5/S3/QuadraticForms/CubicSphereInfimum.cubic`

*Formalization.* `D5/S3/QuadraticForms/CubicSphereInfimum.cubic` (`✓ std3`).

*Citation.* Haobo Ma; Wenlin Zhang (2026). *MathOverflow 513954, revision 2: singular signed downdates, fixed coordinates, and a sharp polynomial sphere bound (version 2)*. DOI: [10.5281/zenodo.23920598](https://doi.org/10.5281/zenodo.23920598). URL: <https://zenodo.org/records/23920598>.

*Commentary.*

h(t) = (3t − t³)/2.

**Definition 1.2 (The ratio R_h).**

Lean statement: `D5/S3/QuadraticForms/CubicSphereInfimum.rayleigh`

*Formalization.* `D5/S3/QuadraticForms/CubicSphereInfimum.rayleigh` (`✓ std3`).

*Citation.* Haobo Ma; Wenlin Zhang (2026). *MathOverflow 513954, revision 2: singular signed downdates, fixed coordinates, and a sharp polynomial sphere bound (version 2)*. DOI: [10.5281/zenodo.23920598](https://doi.org/10.5281/zenodo.23920598). URL: <https://zenodo.org/records/23920598>.

*Commentary.*

For x ∈ ℝᵈ, R_h(x) = Σᵢ xᵢ h(xᵢ) / (Σᵢ h(xᵢ)²)^{1/2}. Since h(0) = 0, summing over all coordinates agrees with the source's active-coordinate convention.

**Definition 1.3 (The infimum value).**

Lean statement: `D5/S3/QuadraticForms/CubicSphereInfimum.infimumValue`

*Formalization.* `D5/S3/QuadraticForms/CubicSphereInfimum.infimumValue` (`✓ std3`).

*Citation.* Haobo Ma; Wenlin Zhang (2026). *MathOverflow 513954, revision 2: singular signed downdates, fixed coordinates, and a sharp polynomial sphere bound (version 2)*. DOI: [10.5281/zenodo.23920598](https://doi.org/10.5281/zenodo.23920598). URL: <https://zenodo.org/records/23920598>.

*Commentary.*

c = 16(17 − 9√3)/23.

**Definition 1.4 (The large squared coordinate).**

Lean statement: `D5/S3/QuadraticForms/CubicSphereInfimum.largeMass`

*Formalization.* `D5/S3/QuadraticForms/CubicSphereInfimum.largeMass` (`✓ std3`).

*Citation.* Haobo Ma; Wenlin Zhang (2026). *MathOverflow 513954, revision 2: singular signed downdates, fixed coordinates, and a sharp polynomial sphere bound (version 2)*. DOI: [10.5281/zenodo.23920598](https://doi.org/10.5281/zenodo.23920598). URL: <https://zenodo.org/records/23920598>.

*Commentary.*

a* = 6 − 3√3, a number in (0, 1).

**Definition 1.5 (The minimizing sequence).**

Lean statement: `D5/S3/QuadraticForms/CubicSphereInfimum.approach`

*Formalization.* `D5/S3/QuadraticForms/CubicSphereInfimum.approach` (`✓ std3`).

*Citation.* Haobo Ma; Wenlin Zhang (2026). *MathOverflow 513954, revision 2: singular signed downdates, fixed coordinates, and a sharp polynomial sphere bound (version 2)*. DOI: [10.5281/zenodo.23920598](https://doi.org/10.5281/zenodo.23920598). URL: <https://zenodo.org/records/23920598>.

*Commentary.*

The vector in ℝ^{m+1} with first coordinate √a* and m coordinates √((1 − a*)/m): one squared coordinate a* and m equal squared tail coordinates.

**Theorem 1.6 (The moment identity).**

Lean statement: `D5/S3/QuadraticForms/CubicSphereInfimum.moment`

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/CubicSphereInfimum.moment` (`✓ std3`). ∎

*Citation.* Haobo Ma; Wenlin Zhang (2026). *MathOverflow 513954, revision 2: singular signed downdates, fixed coordinates, and a sharp polynomial sphere bound (version 2)*. DOI: [10.5281/zenodo.23920598](https://doi.org/10.5281/zenodo.23920598). URL: <https://zenodo.org/records/23920598>.

*Commentary.*

For every unit vector x, with pᵢ = xᵢ² and sₖ = Σᵢ pᵢᵏ, R_h(x)² = (3 − s₂)²/(9 − 6s₂ + s₃).

Expand xᵢ h(xᵢ) = (3pᵢ − pᵢ²)/2 and h(xᵢ)² = (9pᵢ − 6pᵢ² + pᵢ³)/4 and use Σᵢ pᵢ = 1. This is equation (5) of H. Ma and W. Zhang (DOI 10.5281/zenodo.23920598).

**Theorem 1.7 (Infimum, non-attainment and the two-coordinate minimum).**

Lean statement: `D5/S3/QuadraticForms/CubicSphereInfimum.result`

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/CubicSphereInfimum.result` (`✓ std3`). ∎

*Citation.* Haobo Ma; Wenlin Zhang (2026). *MathOverflow 513954, revision 2: singular signed downdates, fixed coordinates, and a sharp polynomial sphere bound (version 2)*. DOI: [10.5281/zenodo.23920598](https://doi.org/10.5281/zenodo.23920598). URL: <https://zenodo.org/records/23920598>.

*Commentary.*

h is strictly increasing on [−1, 1], h(1) = 1, and h(t)/t is strictly decreasing for t > 0. Every unit vector x of every finite dimension, of any signs, satisfies c < R_h(x)², and c is the greatest lower bound of R_h(x)² over nonnegative unit vectors, so the infimum c = 16(17 − 9√3)/23 is never attained. The sequence with one squared coordinate a* = 6 − 3√3 and m equal squared tail coordinates consists of nonnegative unit vectors whose values R_h² tend to c. Every unit vector with at most two nonzero coordinates satisfies 80/81 ≤ R_h(x)², with equality exactly when 9s₂ = 7, and equality holds for a nonnegative vector in dimension two. The vector with squared coordinates (4/5, 1/10, 1/10) has R_h(x)² = 13689/13885 < 80/81.

Put a = √s₂ ∈ (0, 1]. Each pᵢ ≤ a, so s₃ ≤ a s₂ = a³ and the moment identity gives R_h(x)² ≥ (3 − a²)²/(9 − 6a² + a³). The factorization 23(3 − a²)² − 16(17 − 9√3)(9 − 6a² + a³) = (a − a*)²(23a² + (4 + 6√3)a + 12√3 − 15), with a positive second factor for a ≥ 0, gives R_h(x)² ≥ c. Equality would need s₃ = a s₂, which forces every positive pᵢ to equal a; then s₂ = a and s₂ = a², so a = 1 ≠ a*, a contradiction. Along the sequence s₂ → a*² and s₃ → a*³, so R_h² → c. On a support of at most two points 2s₃ = 3s₂ − 1, and then R_h(x)² − 80/81 = (9s₂ − 7)²/(81(9 − 6s₂ + s₃)); squared coordinates (3 ± √5)/6 give s₂ = 7/9. This is Theorem 11 of H. Ma and W. Zhang (DOI 10.5281/zenodo.23920598), answering Lucid's sphere question (Mathematics Stack Exchange 5146381) linked from MathOverflow 513954, revision 2.

## References

- Truth anchor: `D5/S3/QuadraticForms/CubicSphereInfimum.approach`
- Truth anchor: `D5/S3/QuadraticForms/CubicSphereInfimum.cubic`
- Truth anchor: `D5/S3/QuadraticForms/CubicSphereInfimum.infimumValue`
- Truth anchor: `D5/S3/QuadraticForms/CubicSphereInfimum.largeMass`
- Truth anchor: `D5/S3/QuadraticForms/CubicSphereInfimum.moment`
- Truth anchor: `D5/S3/QuadraticForms/CubicSphereInfimum.rayleigh`
- Truth anchor: `D5/S3/QuadraticForms/CubicSphereInfimum.result`
