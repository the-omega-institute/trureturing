# SixRowAttainment

## Abstract

Actual central APPT attainment and the strict obstruction at n=22

The contraction theorem supplies a central APPT density at each dimension n >= 23. The normalized ray supplies the APPT density used to rule out n = 22.

**Definition 1.1 (centralProjector).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowAttainment.centralProjector`

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowAttainment.centralProjector` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Diagonal projection onto the first centralIndex(n) coordinates under the canonical finProdFinEquiv.

**Definition 1.2 (normalization).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowAttainment.normalization`

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowAttainment.normalization` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The real trace denominator 30*n+2*centralIndex(n).

**Definition 1.3 (centralDensity).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowAttainment.centralDensity`

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowAttainment.centralDensity` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The actual complex matrix (5I+2P)/(30*n+2*centralIndex(n)).

**Theorem 1.4 (projector square).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowAttainment.projector_square`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowAttainment.projector_square` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural n, P squared equals P.

**Theorem 1.5 (projector positive).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowAttainment.projector_positive`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowAttainment.projector_positive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural n, P and I-P are positive semidefinite.

**Theorem 1.6 (projector trace).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowAttainment.projector_trace`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowAttainment.projector_trace` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural n, the actual complex trace of P is the integer centralIndex(n).

**Theorem 1.7 (projector rank).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowAttainment.projector_rank`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowAttainment.projector_rank` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural n, the matrix rank of P is centralIndex(n), using the idempotent linear-map trace identity.

**Theorem 1.8 (central density physical).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowAttainment.central_density_physical`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowAttainment.central_density_physical` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For n>=23 the actual density is PSD, has trace exactly one, and is literal APPT. This invokes dimension-general contraction_appt with A=Fin 6 and positive scalar normalization.

**Theorem 1.9 (central density square trace).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowAttainment.central_density_square_trace`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowAttainment.central_density_square_trace` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For n>=23 the complex square trace is the real scalar (25*(6*n)+24*centralIndex(n))/(30*n+2*centralIndex(n))^2, embedded in C.

**Theorem 1.10 (central density purity).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowAttainment.central_density_purity`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowAttainment.central_density_purity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For n>=23 the actual purity is theta(n). Even n uses 2*j=5*n; odd n uses 2*j=5*n+1, with j=(5*n+1)/2 in Nat.

**Theorem 1.11 (central density diagonal).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowAttainment.central_density_diagonal`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowAttainment.central_density_diagonal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural n the actual density is the canonical diagonal with its first centralIndex(n) entries 7/(30*n+2*j) and its remaining entries 5/(30*n+2*j). This is the existing SixRowConcentration.centralSpectrum formula after unfolding; its proof closure is not imported solely for a definition.

**Theorem 1.12 (central spectrum data).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowAttainment.central_spectrum_data`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowAttainment.central_spectrum_data` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For n>=23 the entire displayed diagonal vector is antitone, nonnegative, has sum one and square sum theta(n). Trace is transported by finProdFinEquiv; no eigenvalue spectral theorem is reproved.

**Theorem 1.13 (central attainment).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowAttainment.central_attainment`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowAttainment.central_attainment` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For n>=23 a rank-centralIndex(n) projection produces an actual PSD trace-one literal APPT density of purity theta(n), for later consumption by the full original threshold theorem.

**Definition 1.14 (ray22Vector).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowAttainment.ray22Vector`

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowAttainment.ray22Vector` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The concrete vector Pi.single (0,0) 1 on Fin 6 times Fin 22.

**Definition 1.15 (ray22Density).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowAttainment.ray22Density`

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowAttainment.ray22Density` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The existing dimension-general normalizedRay of the concrete ray22Vector.

**Theorem 1.16 (ray22 unit).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowAttainment.ray22_unit`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowAttainment.ray22_unit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual complex dot product star(v) dot v is one.

**Theorem 1.17 (n22 obstruction).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowAttainment.n22_obstruction`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowAttainment.n22_obstruction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The concrete six-by-twenty-two ray density is PSD, trace one and literal APPT, with purity 35/4489. The central theta(22)=3/385 is strictly smaller, by exactly 8/1728265. This does not determine the maximum below 23 or establish the full threshold.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowAttainment.centralDensity`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowAttainment.centralProjector`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowAttainment.central_attainment`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowAttainment.central_density_diagonal`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowAttainment.central_density_physical`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowAttainment.central_density_purity`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowAttainment.central_density_square_trace`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowAttainment.central_spectrum_data`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowAttainment.n22_obstruction`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowAttainment.normalization`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowAttainment.projector_positive`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowAttainment.projector_rank`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowAttainment.projector_square`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowAttainment.projector_trace`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowAttainment.ray22Density`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowAttainment.ray22Vector`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowAttainment.ray22_unit`
- Dependency: [D5/S3/Quantum/Entanglement/AbsolutePPT/ContractionAttainment](../ContractionAttainment.md)
- Dependency: [D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitQuintitMaximumPurity](../QuadbitQuintitMaximumPurity.md)
- Dependency: [D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowScalarData](SixRowScalarData.md)
