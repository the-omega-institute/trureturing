# Finite rank-one APPT maximum

## Abstract

Actual four-by-n APPT maximum purity for every natural n from seven through thirteen.

**Definition 1.1 (Rank-one purity value).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitFiniteMaximumPurity.purityValue`

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitFiniteMaximumPurity.purityValue` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Jennifer Ahiable; Naga Bhavya Teja Kothakonda; Andreas Winter (2026). *The geometry of absolute separability and other convex matrix properties from spectrum*. DOI: [10.48550/arXiv.2608.03390](https://doi.org/10.48550/arXiv.2608.03390). URL: <https://arxiv.org/abs/2608.03390v2>.

*Commentary.*

For every natural n, purityValue(n)=(4n+8)/(4n+2)^2 in the real numbers. Natural multiplication is performed before coercion. The formula and attaining spectrum are due to Ahiable–Kothakonda–Winter, arXiv:2608.03390v2, Corollary 6.4 and equation (44).

**Definition 1.2 (Purities of actual density matrices).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitFiniteMaximumPurity.physicalPurities`

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitFiniteMaximumPurity.physicalPurities` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Jennifer Ahiable; Naga Bhavya Teja Kothakonda; Andreas Winter (2026). *The geometry of absolute separability and other convex matrix properties from spectrum*. DOI: [10.48550/arXiv.2608.03390](https://doi.org/10.48550/arXiv.2608.03390). URL: <https://arxiv.org/abs/2608.03390v2>.

*Commentary.*

For every natural n, physicalPurities(n) is the set of real p for which an actual complex matrix rho on Fin 4 times Fin n is positive semidefinite, has complex trace one, satisfies APPT, and has real part of trace(rho*rho) equal to p. APPT means that every global unitary conjugate has positive semidefinite second-factor partial transpose. No spectral relaxation replaces this physical domain.

**Definition 1.3 (Product basis origin).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitFiniteMaximumPurity.basisZero`

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitFiniteMaximumPurity.basisZero` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Jennifer Ahiable; Naga Bhavya Teja Kothakonda; Andreas Winter (2026). *The geometry of absolute separability and other convex matrix properties from spectrum*. DOI: [10.48550/arXiv.2608.03390](https://doi.org/10.48550/arXiv.2608.03390). URL: <https://arxiv.org/abs/2608.03390v2>.

*Commentary.*

For every natural n with 7<=n, basisZero(n) is the actual product index (0,0) in Fin 4 times Fin n. Its second coordinate is constructed from the positive dimension; its proof argument is suppressed here.

**Definition 1.4 (Density from a normalized rank-one ray).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitFiniteMaximumPurity.attainingDensity`

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitFiniteMaximumPurity.attainingDensity` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Jennifer Ahiable; Naga Bhavya Teja Kothakonda; Andreas Winter (2026). *The geometry of absolute separability and other convex matrix properties from spectrum*. DOI: [10.48550/arXiv.2608.03390](https://doi.org/10.48550/arXiv.2608.03390). URL: <https://arxiv.org/abs/2608.03390v2>.

*Commentary.*

For every natural n with 7<=n, attainingDensity(n) is normalizedRay(Pi.single(basisZero(n),1))=(I+2|00><00|)/(4n+2). The normalization is the existing physical ray construction. It is also the basis diagonal with entry 3/(4n+2) at the origin and 1/(4n+2) elsewhere.

**Theorem 1.5 (Unconditional physical upper bound).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitFiniteMaximumPurity.physical_purity_upper_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitFiniteMaximumPurity.physical_purity_upper_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jennifer Ahiable; Naga Bhavya Teja Kothakonda; Andreas Winter (2026). *The geometry of absolute separability and other convex matrix properties from spectrum*. DOI: [10.48550/arXiv.2608.03390](https://doi.org/10.48550/arXiv.2608.03390). URL: <https://arxiv.org/abs/2608.03390v2>.

*Commentary.*

For every natural n with 7<=n<=13 and every complex matrix rho indexed by Fin 4 times Fin n, positive semidefiniteness of rho, trace(rho)=1 and APPT(rho) imply re(trace(rho*rho))<=(4n+8)/(4n+2)^2. One actual sorted spectrum l:Fin(4n) to Real is obtained by diagonal_spectral_reduction with finProdFinEquiv. Its nonnegative entries sum to one and its actual labelled diagonal remains APPT. That same l supplies both literal K1 and K2 through diagonal_necessary_both, the first-six/last-ten inequality through uniform_rank_four_necessary, and the trace-square identity. No independent spectral choices are combined. The length-52 endpoint actual_k1_l4_length52_purity_bound has value 5/243, needs no K2 assumption and applies to arbitrary ordered spectra. rank_four_endpoint_interval transports this endpoint down to length 24; substituting N=4n and k=N-16 covers every required dimension 28 through 52. The endpoint is proved internally, rather than left as a hypothesis.

**Theorem 1.6 (Actual attained maximum and real supremum).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitFiniteMaximumPurity.physical_finite7_maximum`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitFiniteMaximumPurity.physical_finite7_maximum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jennifer Ahiable; Naga Bhavya Teja Kothakonda; Andreas Winter (2026). *The geometry of absolute separability and other convex matrix properties from spectrum*. DOI: [10.48550/arXiv.2608.03390](https://doi.org/10.48550/arXiv.2608.03390). URL: <https://arxiv.org/abs/2608.03390v2>.

*Commentary.*

For every natural n with 7<=n<=13 the real denominator 4n+2 is positive. Every complex positive-semidefinite trace-one APPT rho on Fin 4 times Fin n has purity at most purityValue(n). There exists an actual rho equal both to normalizedRay(Pi.single(basisZero(n),1)) and to the diagonal with entry 3/(4n+2) at basisZero(n) and 1/(4n+2) elsewhere; it is positive semidefinite, trace one, APPT and has purity exactly purityValue(n). The physical purity set is nonempty, bounded above and has real supremum purityValue(n). The existing normalized_ray theorem proves the physical properties for the unit product vector, and normalized_basis_diagonal supplies the literal diagonal. Membership of its purity and the universal upper bound give the attained real supremum.

Ordering is non-strict: ties, zero eigenvalues and singular necessary matrices remain allowed. K1, K2 and L4 are used only as necessary conditions, with no PSD sufficiency assertion or extremal spectral ansatz. The formula and attainer are published prior work; the unrestricted upper bound is the additional inference supplied by the endpoint and dimension transfer. This finite theorem does not settle n>=14, the general-dimensional conjecture, uniqueness of maximizers or world priority.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitFiniteMaximumPurity.attainingDensity`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitFiniteMaximumPurity.basisZero`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitFiniteMaximumPurity.physicalPurities`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitFiniteMaximumPurity.physical_finite7_maximum`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitFiniteMaximumPurity.physical_purity_upper_bound`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitFiniteMaximumPurity.purityValue`
- Dependency: [D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitQuintitMaximumPurity](QuadbitQuintitMaximumPurity.md)
- Dependency: [D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniform/ContinuousSpectrumAssembly](QuadbitUniform/ContinuousSpectrumAssembly.md)
- Dependency: [D5/S3/Quantum/Entanglement/AbsolutePPT/SpectralBoundaryTransfer](SpectralBoundaryTransfer.md)
- Dependency: [D5/S3/Quantum/Entanglement/AbsolutePPT/UniformRankFourNecessary](UniformRankFourNecessary.md)
