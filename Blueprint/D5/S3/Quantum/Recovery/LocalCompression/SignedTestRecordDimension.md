# Signed tests and record dimension

## Abstract

A static reconstruction-error obstruction for a finite experiment with a bounded encoder environment.

**Definition 1.1 (Sign leakage).**

Lean statement: `D5/S3/Quantum/Recovery/LocalCompression/SignedTestRecordDimension.signLeakage`

*Formalization.* `D5/S3/Quantum/Recovery/LocalCompression/SignedTestRecordDimension.signLeakage` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a Hermitian test H and its strictly positive spectral projection P, the form L on a square matrix X sums the real traces of (I − P) X H⁺ X† and P X H⁻ X†. H⁺ and H⁻ are the positive and negative parts of H, respectively. These pairings give the squared Frobenius leakages with the full spectral weights.

**Theorem 1.2 (Exact Kraus sign leakage).**

Lean statement: `D5/S3/Quantum/Recovery/LocalCompression/SignedTestRecordDimension.sum_signLeakage_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/LocalCompression/SignedTestRecordDimension.sum_signLeakage_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kohdai Kuroiwa (2021). *Quantum Blind Data Compression and Structure of Quantum Operations Approximately Preserving Quantum States*. URL: <https://hdl.handle.net/10012/17174>.

*Commentary.*

For a finite trace-preserving square Kraus map T with matrices Kₐ and a Hermitian test H, the sum of L(Kₐ) is the real trace of P(H − T(H)). The identity holds for singular tests and follows by applying trace preservation to H⁺. Kuroiwa's Chapter 4, Lemma 4.6, equations (4.23)–(4.24), supplies the sign-leakage terms.

**Definition 1.3 (Auxiliary label projections).**

Lean statement: `D5/S3/Quantum/Recovery/LocalCompression/SignedTestRecordDimension.labelProjection`

*Formalization.* `D5/S3/Quantum/Recovery/LocalCompression/SignedTestRecordDimension.labelProjection` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a label map g on a finite basis, Qⱼ is diagonal with entry one at b when g(b) = j and zero otherwise.

**Definition 1.4 (Auxiliary label densities).**

Lean statement: `D5/S3/Quantum/Recovery/LocalCompression/SignedTestRecordDimension.labelDensity`

*Formalization.* `D5/S3/Quantum/Recovery/LocalCompression/SignedTestRecordDimension.labelDensity` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

With coordinate masses m(b), the diagonal matrix Ωⱼ has entry m(b) on coordinates b of label j and zero on the others.

**Definition 1.5 (Density-weighted label loss).**

Lean statement: `D5/S3/Quantum/Recovery/LocalCompression/SignedTestRecordDimension.labelLeakage`

*Formalization.* `D5/S3/Quantum/Recovery/LocalCompression/SignedTestRecordDimension.labelLeakage` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The form F on X is the sum over j of the real trace of (I − Qⱼ)XΩⱼX†.

**Definition 1.6 (Encoder environment slices).**

Lean statement: `D5/S3/Quantum/Recovery/LocalCompression/SignedTestRecordDimension.encoderSlice`

*Formalization.* `D5/S3/Quantum/Recovery/LocalCompression/SignedTestRecordDimension.encoderSlice` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For V mapping the input basis into memory times environment, the slice Aₜ has entry V((a,t),b) at memory row a and input column b.

**Definition 1.7 (Composite Kraus matrices).**

Lean statement: `D5/S3/Quantum/Recovery/LocalCompression/SignedTestRecordDimension.recordKraus`

*Formalization.* `D5/S3/Quantum/Recovery/LocalCompression/SignedTestRecordDimension.recordKraus` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a CPTP decoder D and encoder slices Aₜ, the composite Kraus family has entries BₛAₜ for the canonical Kraus family Bₛ of D.

**Definition 1.8 (Induced memory effects).**

Lean statement: `D5/S3/Quantum/Recovery/LocalCompression/SignedTestRecordDimension.decoderEffect`

*Formalization.* `D5/S3/Quantum/Recovery/LocalCompression/SignedTestRecordDimension.decoderEffect` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The memory effect Mⱼ is the trace adjoint of the decoder applied to Qⱼ.

**Theorem 1.9 (Actual label loss and the memory score).**

Lean statement: `D5/S3/Quantum/Recovery/LocalCompression/SignedTestRecordDimension.label_deficit_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/LocalCompression/SignedTestRecordDimension.label_deficit_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a nonempty finite label set of cardinality r whose coordinate masses sum to one within each label, let V be an isometry on the whole input basis and D a CPTP decoder. Then the sum of F(BₛAₜ) over both Kraus indices equals r times one minus the average success of the effects Mⱼ on the environment-reduced columns of V, with coordinate prior p(b) = m(b)/r. Trace preservation gives the total input weight and the Kraus trace-adjoint pairing gives the success.

**Theorem 1.10 (Label count and memory dimension).**

Lean statement: `D5/S3/Quantum/Recovery/LocalCompression/SignedTestRecordDimension.label_count_sub_memory_le_deficit`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/LocalCompression/SignedTestRecordDimension.label_count_sub_memory_le_deficit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For nonnegative coordinate masses of total one per label, the loss of a full-input isometry and common CPTP decoder is at least r − d. Each encoded auxiliary density is at most the identity, so the sum of the correct-label pairings is at most the sum of the decoder effect traces, which is d by POVM completeness. With the same signed tests and quadratic dominance, r − d is bounded by the same reconstruction-error budget.

**Definition 1.11 (Preparation matrices).**

Lean statement: `D5/S3/Quantum/Recovery/LocalCompression/SignedTestRecordDimension.preparation`

*Formalization.* `D5/S3/Quantum/Recovery/LocalCompression/SignedTestRecordDimension.preparation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The plain complex matrix underlying an input density state.

**Definition 1.12 (Finite signed tests).**

Lean statement: `D5/S3/Quantum/Recovery/LocalCompression/SignedTestRecordDimension.signedTest`

*Formalization.* `D5/S3/Quantum/Recovery/LocalCompression/SignedTestRecordDimension.signedTest` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A sum of the preparation matrices with the specified real coefficients.

**Definition 1.13 (Sign loss of a signed test).**

Lean statement: `D5/S3/Quantum/Recovery/LocalCompression/SignedTestRecordDimension.signedTestLeakage`

*Formalization.* `D5/S3/Quantum/Recovery/LocalCompression/SignedTestRecordDimension.signedTestLeakage` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The full Jordan-part leakage form of the Hermitian test with the specified coefficients.

**Theorem 1.14 (Weighted signed-test dimension obstruction).**

$$r (1 - O\left(g, p, d, e\right)) \leq \delta \sum_{l} w_{l} \frac{\sum_{i} \lvert c_{li} \rvert}{2}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/LocalCompression/SignedTestRecordDimension.signed_test_record_dimension` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kohdai Kuroiwa (2021). *Quantum Blind Data Compression and Structure of Quantum Operations Approximately Preserving Quantum States*. URL: <https://hdl.handle.net/10012/17174>.

*Acknowledgement.* Noam Elron and Yonina C. Eldar (2007). *Optimal encoding of classical information in a quantum medium*. DOI: [10.1109/TIT.2006.894686](https://doi.org/10.1109/TIT.2006.894686). URL: <https://arxiv.org/abs/quant-ph/0601010v2>.

*Acknowledgement.* Péter E. Frenkel (2022). *Classical simulations of communication channels*. DOI: [10.22331/q-2022-06-29-751](https://doi.org/10.22331/q-2022-06-29-751). URL: <https://arxiv.org/abs/2101.10985v4>.

*Acknowledgement.* Fabien Clivaz, Ralph Silva, Géraldine Haack, Jonatan Bohr Brask, Nicolas Brunner and Marcus Huber (2019). *Unifying paradigms of quantum refrigeration: A universal and attainable bound on cooling*. DOI: [10.1103/PhysRevLett.123.170605](https://doi.org/10.1103/PhysRevLett.123.170605). URL: <https://arxiv.org/abs/1903.04970v2>.

*Acknowledgement.* Kohtaro Kato (2025). *Exact and Local Compression of Quantum Bipartite States*. DOI: [10.1109/TIT.2025.3562884](https://doi.org/10.1109/TIT.2025.3562884). URL: <https://arxiv.org/abs/2309.07434>.

*Commentary.*

Let B be the whole finite input basis, and let the auxiliary labels form a nonempty finite set of size r. Each coordinate has a label g(b) and a nonnegative mass m(b), with mass one per label. The basis includes the zero-mass coordinates. Let V be an isometry from this basis into memory of dimension d and a pure environment of dimension e > 0, so |B| ≤ de. Let D be one CPTP decoder from memory to input.

For a finite family of input states ρᵢ and finitely many real signed coefficient rows cₗ, form Hₗ = ∑ᵢ cₗᵢρᵢ. The bound assumes wₗ ≥ 0 and F(X) ≤ ∑ₗ wₗ Lₗ(X) for every square complex matrix X. Here Lₗ is the full sign-leakage form for Hₗ. The parameter δ bounds each full trace-norm error after applying V, discarding its environment and applying D.

O(g,p,d,e) is the exact weighted label optimum with p(b) = m(b)/r. It sums the d largest masses among consecutive e-entry blocks of the separately sorted and zero-padded prior lists of the labels. The decoder effects form a POVM and the actual score is at most O by WeightedLabelRecordDilation.weightedLabelRecord_optimum. Its spectral packing uses the sources documented with that theorem. Applying the quadratic dominance to each composite Kraus operator and the trace-zero effect bound to each test gives the displayed error budget, using the finite signed-sum trace-norm triangle inequality.

Kato §VII motivates the approximate local-compression question. The estimate concerns the full trace-norm errors of a fixed finite experiment under one encoder and decoder in one use, with the pure environment bound imposed on the encoder.

## References

- Truth anchor: `D5/S3/Quantum/Recovery/LocalCompression/SignedTestRecordDimension.decoderEffect`
- Truth anchor: `D5/S3/Quantum/Recovery/LocalCompression/SignedTestRecordDimension.encoderSlice`
- Truth anchor: `D5/S3/Quantum/Recovery/LocalCompression/SignedTestRecordDimension.labelDensity`
- Truth anchor: `D5/S3/Quantum/Recovery/LocalCompression/SignedTestRecordDimension.labelLeakage`
- Truth anchor: `D5/S3/Quantum/Recovery/LocalCompression/SignedTestRecordDimension.labelProjection`
- Truth anchor: `D5/S3/Quantum/Recovery/LocalCompression/SignedTestRecordDimension.label_count_sub_memory_le_deficit`
- Truth anchor: `D5/S3/Quantum/Recovery/LocalCompression/SignedTestRecordDimension.label_deficit_eq`
- Truth anchor: `D5/S3/Quantum/Recovery/LocalCompression/SignedTestRecordDimension.preparation`
- Truth anchor: `D5/S3/Quantum/Recovery/LocalCompression/SignedTestRecordDimension.recordKraus`
- Truth anchor: `D5/S3/Quantum/Recovery/LocalCompression/SignedTestRecordDimension.signLeakage`
- Truth anchor: `D5/S3/Quantum/Recovery/LocalCompression/SignedTestRecordDimension.signedTest`
- Truth anchor: `D5/S3/Quantum/Recovery/LocalCompression/SignedTestRecordDimension.signedTestLeakage`
- Truth anchor: `D5/S3/Quantum/Recovery/LocalCompression/SignedTestRecordDimension.signed_test_record_dimension`
- Truth anchor: `D5/S3/Quantum/Recovery/LocalCompression/SignedTestRecordDimension.sum_signLeakage_eq`
- Dependency: [D5/S3/Quantum/Divergence/CanonicalRelativeModularModel](../../Divergence/CanonicalRelativeModularModel.md)
- Dependency: [D5/S3/Quantum/Measurements/WeightedLabelRecordDilation](../../Measurements/WeightedLabelRecordDilation.md)
- Dependency: [D5/S3/Quantum/Recovery/LocalCompression/SpectralTestLeakage](SpectralTestLeakage.md)
