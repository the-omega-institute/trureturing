# Relative Unitary Spectrum

## Abstract

Spectral chords of a relative unitary and expectations on finite reference extensions.

**Lemma 1.1 (Doubled operator norm bounds every spectral chord).**

Lean statement: `D5/S3/Quantum/ProcessReconstruction/UnitarySpectrum.spectrum_chord_le`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/ProcessReconstruction/UnitarySpectrum.spectrum_chord_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Nathaniel Johnston, David W. Kribs and Vern I. Paulsen (2009). *Computing stabilized norms for quantum operations*. DOI: [10.26421/QIC9.1-2-2](https://doi.org/10.26421/QIC9.1-2-2). URL: <https://arxiv.org/abs/0711.3636v1>.

*Commentary.*

Choose any two spectral points of a finite unitary W. An eigenvector in the tensor product built from eigenvectors for the two points shows that their chord length is bounded by the operator norm of W† ⊗ W minus the identity.

**Lemma 1.2 (Reference amplification preserves spectral inclusion).**

Lean statement: `D5/S3/Quantum/ProcessReconstruction/UnitarySpectrum.reference_spectrum_subset`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/ProcessReconstruction/UnitarySpectrum.reference_spectrum_subset` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every spectral point of the finite reference amplification of a unitary lies in the original spectrum. Take a nonzero reference component of an eigenvector of the amplified unitary.

**Lemma 1.3 (A spectral half-plane bounds every unit-vector expectation).**

Lean statement: `D5/S3/Quantum/ProcessReconstruction/UnitarySpectrum.re_inner_ge_of_spectrum`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/ProcessReconstruction/UnitarySpectrum.re_inner_ge_of_spectrum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Nathaniel Johnston, David W. Kribs and Vern I. Paulsen (2009). *Computing stabilized norms for quantum operations*. DOI: [10.26421/QIC9.1-2-2](https://doi.org/10.26421/QIC9.1-2-2). URL: <https://arxiv.org/abs/0711.3636v1>.

*Commentary.*

A common lower bound for the real parts of the rotated spectral points of a unitary bounds the real part of each similarly rotated expectation in a unit vector. The proof uses positivity of the real part after subtracting the scalar threshold.

## References

- Truth anchor: `D5/S3/Quantum/ProcessReconstruction/UnitarySpectrum.re_inner_ge_of_spectrum`
- Truth anchor: `D5/S3/Quantum/ProcessReconstruction/UnitarySpectrum.reference_spectrum_subset`
- Truth anchor: `D5/S3/Quantum/ProcessReconstruction/UnitarySpectrum.spectrum_chord_le`
- Dependency: [D5/S3/Quantum/ProcessReconstruction/SwapReconstruction](SwapReconstruction.md)
