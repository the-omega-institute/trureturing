# Saturation with a support that is not a dimension multiple

## Abstract

An actual complex noisy Strange qutrit has eight nonzero Gross-Wigner coordinates and saturates the fixed-purity natural-log entropy bound.

**Definition 1.1 (Source displacement operators).**

Lean statement: `D5/S3/Quantum/Magic/ThioSaturationRefutation.grossDisplacement`

*Formalization.* `D5/S3/Quantum/Magic/ThioSaturationRefutation.grossDisplacement` (`✓ std3`).

*Citation.* Jonathan J. Thio, Stephan De Bièvre, Crispin H. W. Barnes, and David R. M. Arvidsson-Shukur (2026). *Tight Quasiprobabilistic Entropic Uncertainty Relations for Discrete Quantum Systems*. URL: <https://arxiv.org/abs/2611.04009v1>.

*Commentary.*

For local dimension q the root is exp(2*pi*i/q). The shift sends |j> to |j+1>, the clock multiplies |j> by the jth root power, and the phase exponent is ab(q+1)/2 in ZMod q. Thus this is the source's phase-adjusted X^a Z^b, with residue labels including zero.

**Definition 1.2 (The source origin operator).**

Lean statement: `D5/S3/Quantum/Magic/ThioSaturationRefutation.grossOrigin`

*Formalization.* `D5/S3/Quantum/Magic/ThioSaturationRefutation.grossOrigin` (`✓ std3`).

*Citation.* Jonathan J. Thio, Stephan De Bièvre, Crispin H. W. Barnes, and David R. M. Arvidsson-Shukur (2026). *Tight Quasiprobabilistic Entropic Uncertainty Relations for Discrete Quantum Systems*. URL: <https://arxiv.org/abs/2611.04009v1>.

*Commentary.*

Eq. (19) averages all q squared displacement operators with factor 1/q squared. This definition retains that sum and its normalization.

**Definition 1.3 (Local Gross operators).**

Lean statement: `D5/S3/Quantum/Magic/ThioSaturationRefutation.grossLocal`

*Formalization.* `D5/S3/Quantum/Magic/ThioSaturationRefutation.grossLocal` (`✓ std3`).

*Citation.* Jonathan J. Thio, Stephan De Bièvre, Crispin H. W. Barnes, and David R. M. Arvidsson-Shukur (2026). *Tight Quasiprobabilistic Entropic Uncertainty Relations for Discrete Quantum Systems*. URL: <https://arxiv.org/abs/2611.04009v1>.

*Commentary.*

Conjugating the origin operator by the source displacement gives S_ab. The dagger is the complex conjugate transpose. The dual operator is q*S_ab, as in Eq. (20).

**Definition 1.4 (Odd-local tensor frames).**

Lean statement: `D5/S3/Quantum/Magic/ThioSaturationRefutation.grossTensor`

*Formalization.* `D5/S3/Quantum/Magic/ThioSaturationRefutation.grossTensor` (`✓ std3`).

*Citation.* Jonathan J. Thio, Stephan De Bièvre, Crispin H. W. Barnes, and David R. M. Arvidsson-Shukur (2026). *Tight Quasiprobabilistic Entropic Uncertainty Relations for Discrete Quantum Systems*. URL: <https://arxiv.org/abs/2611.04009v1>.

*Commentary.*

The matrix entries are products of the local S entries for a family of local dimensions. IsGross specializes this construction to n factors of a common odd dimension q. The Hilbert basis is the dependent product of the residue bases and the coordinate labels are a pair of such products.

**Definition 1.5 (Basis projectors).**

Lean statement: `D5/S3/Quantum/Magic/ThioSaturationRefutation.columnProjector`

*Formalization.* `D5/S3/Quantum/Magic/ThioSaturationRefutation.columnProjector` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Jonathan J. Thio, Stephan De Bièvre, Crispin H. W. Barnes, and David R. M. Arvidsson-Shukur (2026). *Tight Quasiprobabilistic Entropic Uncertainty Relations for Discrete Quantum Systems*. URL: <https://arxiv.org/abs/2611.04009v1>.

*Commentary.*

A column vector of an orthonormal basis gives its complex rank-one projector by the outer product with its conjugate.

**Definition 1.6 (The complete MUB-KD source class).**

Lean statement: `D5/S3/Quantum/Magic/ThioSaturationRefutation.IsMUBKD`

*Formalization.* `D5/S3/Quantum/Magic/ThioSaturationRefutation.IsMUBKD` (`✓ std3`).

*Citation.* Jonathan J. Thio, Stephan De Bièvre, Crispin H. W. Barnes, and David R. M. Arvidsson-Shukur (2026). *Tight Quasiprobabilistic Entropic Uncertainty Relations for Discrete Quantum Systems*. URL: <https://arxiv.org/abs/2611.04009v1>.

*Commentary.*

The two square basis matrices have orthonormal columns and every squared overlap is the inverse Hilbert dimension. The KD frame is the ordered product of the first and second projectors, Eq. (17), with an arbitrary bijection of coordinate labels. No convex-hull hypothesis from Lemma 2 is imposed.

**Definition 1.7 (The complete odd-local Gross source class).**

Lean statement: `D5/S3/Quantum/Magic/ThioSaturationRefutation.IsGross`

*Formalization.* `D5/S3/Quantum/Magic/ThioSaturationRefutation.IsGross` (`✓ std3`).

*Citation.* Jonathan J. Thio, Stephan De Bièvre, Crispin H. W. Barnes, and David R. M. Arvidsson-Shukur (2026). *Tight Quasiprobabilistic Entropic Uncertainty Relations for Discrete Quantum Systems*. URL: <https://arxiv.org/abs/2611.04009v1>.

*Commentary.*

There is at least one local factor. The common local dimension q is positive and odd; the total dimension is q to the power n. The Hilbert basis and coordinate labels are bijectively identified with the tensor residue carriers. A unitary basis matrix permits every orthonormal computational basis. The frame equals the exact tensor product conjugated by this unitary, rather than an arbitrary operator frame.

**Definition 1.8 (The union of source classes).**

Lean statement: `D5/S3/Quantum/Magic/ThioSaturationRefutation.IsSourceFrame`

*Formalization.* `D5/S3/Quantum/Magic/ThioSaturationRefutation.IsSourceFrame` (`✓ std3`).

*Citation.* Jonathan J. Thio, Stephan De Bièvre, Crispin H. W. Barnes, and David R. M. Arvidsson-Shukur (2026). *Tight Quasiprobabilistic Entropic Uncertainty Relations for Discrete Quantum Systems*. URL: <https://arxiv.org/abs/2611.04009v1>.

*Commentary.*

The allowed frame belongs either to the complete MUB-KD class or to the exact odd-local Gross tensor class.

**Definition 1.9 (Complex coordinates).**

Lean statement: `D5/S3/Quantum/Magic/ThioSaturationRefutation.coordinate`

*Formalization.* `D5/S3/Quantum/Magic/ThioSaturationRefutation.coordinate` (`✓ std3`).

*Citation.* Jonathan J. Thio, Stephan De Bièvre, Crispin H. W. Barnes, and David R. M. Arvidsson-Shukur (2026). *Tight Quasiprobabilistic Entropic Uncertainty Relations for Discrete Quantum Systems*. URL: <https://arxiv.org/abs/2611.04009v1>.

*Commentary.*

Eq. (9) is Tr(rho*S dagger). Realness is asserted separately in the positivity hypotheses; taking the real part alone does not define membership in the allowed probability domain.

**Definition 1.10 (Coordinate support).**

Lean statement: `D5/S3/Quantum/Magic/ThioSaturationRefutation.coordinateSupport`

*Formalization.* `D5/S3/Quantum/Magic/ThioSaturationRefutation.coordinateSupport` (`✓ std3`).

*Citation.* Jonathan J. Thio, Stephan De Bièvre, Crispin H. W. Barnes, and David R. M. Arvidsson-Shukur (2026). *Tight Quasiprobabilistic Entropic Uncertainty Relations for Discrete Quantum Systems*. URL: <https://arxiv.org/abs/2611.04009v1>.

*Commentary.*

The finite set contains every label with nonzero complex coordinate. Its cardinality is D. This is not the rank of the density matrix.

**Definition 1.11 (Entropy including zero entries).**

Lean statement: `D5/S3/Quantum/Magic/ThioSaturationRefutation.coordinateEntropy`

*Formalization.* `D5/S3/Quantum/Magic/ThioSaturationRefutation.coordinateEntropy` (`✓ std3`).

*Citation.* Jonathan J. Thio, Stephan De Bièvre, Crispin H. W. Barnes, and David R. M. Arvidsson-Shukur (2026). *Tight Quasiprobabilistic Entropic Uncertainty Relations for Discrete Quantum Systems*. URL: <https://arxiv.org/abs/2611.04009v1>.

*Commentary.*

The Shannon sum uses Real.negMulLog at every coordinate's real part. This uses the natural logarithm and its zero term is exactly zero. Positivity and realness are separate hypotheses in the assertion.

**Definition 1.12 (Only dimension-multiple supports at saturation).**

Lean statement: `D5/S3/Quantum/Magic/ThioSaturationRefutation.claim`

*Formalization.* `D5/S3/Quantum/Magic/ThioSaturationRefutation.claim` (`✓ std3`).

*Citation.* Jonathan J. Thio, Stephan De Bièvre, Crispin H. W. Barnes, and David R. M. Arvidsson-Shukur (2026). *Tight Quasiprobabilistic Entropic Uncertainty Relations for Discrete Quantum Systems*. URL: <https://arxiv.org/abs/2611.04009v1>.

*Commentary.*

Appendix A A1.p8.1 asks: Whether these are the only possible D-values for which saturation occurs is not clear in general. The preceding values are D=delta*d, 1<=delta<=d. The assertion quantifies over every finite complex Hilbert basis of positive dimension, every finite coordinate carrier, both source classes, and every complex positive-semidefinite trace-one state. Every coordinate must be real and nonnegative, including zero. Source coordinates obey Eq. (10); no extra normalization premise is imposed on the assertion. Purity lies in the closed interval [1/d,1], so both endpoints are retained. Equality refers to H(Q)=-ln(Tr(rho squared))+ln(d). The conclusion requires an integer delta between one and d whose dimension multiple is the coordinate support.

**Definition 1.13 (The known noisy Strange state).**

Lean statement: `D5/S3/Quantum/Magic/ThioSaturationRefutation.rho`

*Formalization.* `D5/S3/Quantum/Magic/ThioSaturationRefutation.rho` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Jonathan J. Thio, Stephan De Bièvre, Crispin H. W. Barnes, and David R. M. Arvidsson-Shukur (2026). *Tight Quasiprobabilistic Entropic Uncertainty Relations for Discrete Quantum Systems*. URL: <https://arxiv.org/abs/2611.04009v1>.

*Commentary.*

The matrix is [[1/4,0,0],[0,3/8,-1/8],[0,-1/8,3/8]] on ZMod 3. With v=(0,1,-1) it equals I/4+v*v dagger/8=(3I-P)/8, where P|j>=|-j>. This is a known depolarized antisymmetric qutrit ingredient, credited to Gross and the noisy Strange literature in the source note. No new-state or priority claim is made.

**Theorem 1.14 (The universal assertion is false).**

$$\neg \mathrm{claim}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Magic/ThioSaturationRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/thio-2026-saturation-support-multiples` (refuted) by `D5/S3/Quantum/Magic/ThioSaturationRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"thio-2026-saturation-support-multiples","declaration_gid":"D5/S3/Quantum/Magic/ThioSaturationRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Jonathan J. Thio, Stephan De Bièvre, Crispin H. W. Barnes, and David R. M. Arvidsson-Shukur (2026). *Tight Quasiprobabilistic Entropic Uncertainty Relations for Discrete Quantum Systems*. URL: <https://arxiv.org/abs/2611.04009v1>.

*Commentary.*

Take q=d=3 and one tensor factor. The source operator sum equals P/3. The source coordinates of rho are zero at (0,0) and 1/8 at all other eight labels. The Gram decomposition establishes positivity on all complex vectors, and trace is one. The purity is 3/8, strictly between 1/3 and 1. The full entropy sum, including its zero term, is ln(8)=-ln(3/8)+ln(3). Coordinate support is eight, which is not three times an integer. This allowed instance contradicts the universally quantified assertion over both source classes. It saturates the purity-dependent middle bound, while its entropy exceeds ln(3). No classification of every fixed-purity minimizer or of every other attaining support follows.

## References

- Truth anchor: `D5/S3/Quantum/Magic/ThioSaturationRefutation.IsGross`
- Truth anchor: `D5/S3/Quantum/Magic/ThioSaturationRefutation.IsMUBKD`
- Truth anchor: `D5/S3/Quantum/Magic/ThioSaturationRefutation.IsSourceFrame`
- Truth anchor: `D5/S3/Quantum/Magic/ThioSaturationRefutation.claim`
- Truth anchor: `D5/S3/Quantum/Magic/ThioSaturationRefutation.columnProjector`
- Truth anchor: `D5/S3/Quantum/Magic/ThioSaturationRefutation.coordinate`
- Truth anchor: `D5/S3/Quantum/Magic/ThioSaturationRefutation.coordinateEntropy`
- Truth anchor: `D5/S3/Quantum/Magic/ThioSaturationRefutation.coordinateSupport`
- Truth anchor: `D5/S3/Quantum/Magic/ThioSaturationRefutation.grossDisplacement`
- Truth anchor: `D5/S3/Quantum/Magic/ThioSaturationRefutation.grossLocal`
- Truth anchor: `D5/S3/Quantum/Magic/ThioSaturationRefutation.grossOrigin`
- Truth anchor: `D5/S3/Quantum/Magic/ThioSaturationRefutation.grossTensor`
- Truth anchor: `D5/S3/Quantum/Magic/ThioSaturationRefutation.result`
- Truth anchor: `D5/S3/Quantum/Magic/ThioSaturationRefutation.rho`
- Dependency: [D5/S3/Entropy/EntropyEquality](../../Entropy/EntropyEquality.md)
- Dependency: [D5/S3/Quantum/Algebra/WeylDisplacementTrace](../Algebra/WeylDisplacementTrace.md)
- Dependency: [D5/S3/Quantum/Algebra/WeylPhaseArithmetic](../Algebra/WeylPhaseArithmetic.md)
