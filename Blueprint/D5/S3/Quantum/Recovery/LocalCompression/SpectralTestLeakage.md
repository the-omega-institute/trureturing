# Spectral test leakage

## Abstract

Two-sided leakage estimates for finite quantum channels and their signed tests.

**Definition 1.1 (Positive spectral projection).**

Lean statement: `D5/S3/Quantum/Recovery/LocalCompression/SpectralTestLeakage.positiveSpectralProjection`

*Formalization.* `D5/S3/Quantum/Recovery/LocalCompression/SpectralTestLeakage.positiveSpectralProjection` (`✓ std3`).

*Citation.* Kohdai Kuroiwa (2021). *Quantum Blind Data Compression and Structure of Quantum Operations Approximately Preserving Quantum States*. URL: <https://hdl.handle.net/10012/17174>.

*Commentary.*

For a Hermitian complex matrix H on a finite index set, the projection P is the spectral function of H that is one on strictly positive eigenvalues and zero elsewhere.

**Theorem 1.2 (Separate spectral floors for the two leakage directions).**

Lean statement: `D5/S3/Quantum/Recovery/LocalCompression/SpectralTestLeakage.spectral_test_leakage_asymmetric`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/LocalCompression/SpectralTestLeakage.spectral_test_leakage_asymmetric` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kohdai Kuroiwa (2021). *Quantum Blind Data Compression and Structure of Quantum Operations Approximately Preserving Quantum States*. URL: <https://hdl.handle.net/10012/17174>.

*Commentary.*

Let T(X) = ∑ₐ Kₐ X Kₐ* be trace preserving for a finite family of square Kraus matrices. Let H be Hermitian and suppose every eigenvalue is at least g₊ or at most −g₋, with both floors strictly positive. Write P for the positive spectral projection and Q = I − P. Then twice the sum over a of g₊‖QKₐP‖²_F + g₋‖PKₐQ‖²_F is bounded by the full trace norm of H − T(H). Kuroiwa's Lemma 4.6, equations (4.23)–(4.24), gives the sign-leakage trace terms. The two spectral floors lower-bound them separately. The trace-zero effect inequality contributes the factor of two.

**Theorem 1.3 (Commutator bound for a common spectral floor).**

Lean statement: `D5/S3/Quantum/Recovery/LocalCompression/SpectralTestLeakage.spectral_test_leakage`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/LocalCompression/SpectralTestLeakage.spectral_test_leakage` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kohdai Kuroiwa (2021). *Quantum Blind Data Compression and Structure of Quantum Operations Approximately Preserving Quantum States*. URL: <https://hdl.handle.net/10012/17174>.

*Commentary.*

For a trace-preserving finite square Kraus action and a Hermitian H with all eigenvalues at least g or at most −g for g > 0, the positive spectral projection P satisfies 2g∑ₐ ‖PKₐ − KₐP‖²_F ≤ ‖H − T(H)‖₁. The two off-diagonal blocks are orthogonal in the unnormalized Hilbert–Schmidt pairing.

**Theorem 1.4 (Total commutator for finitely many signed tests).**

Lean statement: `D5/S3/Quantum/Recovery/LocalCompression/SpectralTestLeakage.finite_test_commutator_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/LocalCompression/SpectralTestLeakage.finite_test_commutator_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kohdai Kuroiwa (2021). *Quantum Blind Data Compression and Structure of Quantum Operations Approximately Preserving Quantum States*. URL: <https://hdl.handle.net/10012/17174>.

*Commentary.*

For a finite family of Hermitian tests Hⱼ = ρⱼ − tⱼσ, take tⱼ and wⱼ nonnegative and assume every eigenvalue of Hⱼ is at least gⱼ or at most −gⱼ for gⱼ > 0. Let Pⱼ be the positive spectral projection of Hⱼ. If δ bounds the full trace-norm reconstruction errors of every ρⱼ and of σ under the trace-preserving finite square Kraus action T, then ∑ⱼ wⱼ ∑ₐ ‖[Pⱼ,Kₐ]‖²_F ≤ δ∑ⱼ wⱼ(1+tⱼ)/(2gⱼ). Linearity and the triangle inequality give the factor 1+tⱼ. In the dimension converse, a Hilbert–Schmidt commutator gap γ bounds the squared distance of each Kₐ from the common commutant by its weighted commutator sum divided by γ. The finite-test estimate supplies the numerator of that distance bound. The memory dimension and environment packing argument belongs to the manuscript.

## References

- Truth anchor: `D5/S3/Quantum/Recovery/LocalCompression/SpectralTestLeakage.finite_test_commutator_bound`
- Truth anchor: `D5/S3/Quantum/Recovery/LocalCompression/SpectralTestLeakage.positiveSpectralProjection`
- Truth anchor: `D5/S3/Quantum/Recovery/LocalCompression/SpectralTestLeakage.spectral_test_leakage`
- Truth anchor: `D5/S3/Quantum/Recovery/LocalCompression/SpectralTestLeakage.spectral_test_leakage_asymmetric`
- Dependency: [D5/S3/Quantum/Entanglement/ConicalDesignConcurrenceComparability](../../Entanglement/ConicalDesignConcurrenceComparability.md)
- Dependency: [D5/S3/Quantum/Measurement/Auric/DiamondBounds](../../Measurement/Auric/DiamondBounds.md)
