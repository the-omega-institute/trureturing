# Heat on a triangle with one vanishing mass

## Abstract

Positive triangles with a common massless Schur reduction have distinct collocated heat at the hidden-mass time scale.

The triangle and heat expansion come from the heat calculation in An exact zero-mass heat and control separation on a positive triangle (triangle-exact-control.txt, 2026-11-24). Its vertices 1, 2 and 3 are numbered 0, 1 and 2 here.

**Theorem 1.1 (Common massless heat and distinct finite-mass heat).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/ZeroMassTriangleHeat.same_schur_distinct_heat_at_mass_time`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/ZeroMassTriangleHeat.same_schur_distinct_heat_at_mass_time` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Florian Dörfler; Francesco Bullo (2013). *Kron Reduction of Graphs With Applications to Electrical Networks*. DOI: [10.1109/TCSI.2012.2215780](https://doi.org/10.1109/TCSI.2012.2215780). URL: <https://arxiv.org/abs/1102.2950>.

*Commentary.*

The two retained vertices have unit mass. The two edges to vertex 2 have conductance c, and the retained edge has conductance k − c/2. For each c strictly between zero and 2k, all three conductances are positive. With zero mass and no injection at vertex 2, its temperature is the average of the two retained temperatures. The eliminated diagonal is 2c and both couplings are −c, so Schur elimination subtracts c/2 from each entry of the retained block. This leaves a single edge of conductance k. The entire two-vertex heat operator is therefore independent of c at every time.

For positive hidden mass ε, the finite-mass collocated heat is the temperature at vertex 0 per unit impulse at vertex 0. At time εs with s positive, the zero and antisymmetric mode terms cancel in the difference between any two c values. The positive symmetric mode has decay rate c(1+2/ε) and collocated weight ε/[2(2+ε)]. The remaining difference divided by ε is the difference of the exponentials with arguments −c₁(ε+2)s and −c₂(ε+2)s, divided by 2(2+ε). Injectivity of the exponential makes that difference nonzero for distinct conductances.

**Theorem 1.2 (Orthogonal mode projections).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/ZeroMassTriangleHeat.spectral_projectors`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/ZeroMassTriangleHeat.spectral_projectors` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For ε positive, the zero, antisymmetric and symmetric modes give symmetric, pairwise orthogonal projections summing to the identity. The normalized stiffness acts on them with rates 0, 2k and c(1+2/ε).

**Theorem 1.3 (Projection at the repeated rate).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/ZeroMassTriangleHeat.coincident_positive_projector`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/ZeroMassTriangleHeat.coincident_positive_projector` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

When the two rates agree at positive ε, the sum of their mode projections is symmetric and idempotent. The normalized stiffness equals 2k times this projection. For the positive triangle the common rate is positive.

**Theorem 1.4 (Nonzero right-hand limit of the scaled difference).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/ZeroMassTriangleHeat.collocated_difference_limit`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/ZeroMassTriangleHeat.collocated_difference_limit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive s and distinct c₁ and c₂, as ε tends to zero from above the scaled difference tends to one quarter of the difference of the exponentials with arguments −2c₁s and −2c₂s. That limit is nonzero.

## References

- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/ZeroMassTriangleHeat.coincident_positive_projector`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/ZeroMassTriangleHeat.collocated_difference_limit`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/ZeroMassTriangleHeat.same_schur_distinct_heat_at_mass_time`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/ZeroMassTriangleHeat.spectral_projectors`
- Dependency: [D5/S3/Combinatorics/SpectralGraph/UnequalMassPortHeatResistance](UnequalMassPortHeatResistance.md)
