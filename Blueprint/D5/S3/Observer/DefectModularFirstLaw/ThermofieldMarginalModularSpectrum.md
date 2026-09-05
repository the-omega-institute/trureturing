# Thermofield Marginal and Modular Spectrum

## Abstract

The countable thermofield state reduces to the geometric thermal law whose entropy derivative and relative modular level spacing coincide.

**Definition 1.1 (The countable thermofield amplitude).**

Lean statement: `D5/S3/Observer/DefectModularFirstLaw/ThermofieldMarginalModularSpectrum.thermofieldAmplitude`

*Formalization.* `D5/S3/Observer/DefectModularFirstLaw/ThermofieldMarginalModularSpectrum.thermofieldAmplitude` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The amplitude is supported on matching visible and hidden occupations, with Schmidt coefficient sqrt((1-q)q^n).

**Definition 1.2 (Partial trace over the hidden mode).**

Lean statement: `D5/S3/Observer/DefectModularFirstLaw/ThermofieldMarginalModularSpectrum.countablePartialTraceRight`

*Formalization.* `D5/S3/Observer/DefectModularFirstLaw/ThermofieldMarginalModularSpectrum.countablePartialTraceRight` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The hidden countable coordinate is traced out by summing the corresponding diagonal blocks.

**Definition 1.3 (The visible geometric density).**

Lean statement: `D5/S3/Observer/DefectModularFirstLaw/ThermofieldMarginalModularSpectrum.geometricDiagonalDensity`

*Formalization.* `D5/S3/Observer/DefectModularFirstLaw/ThermofieldMarginalModularSpectrum.geometricDiagonalDensity` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The visible occupation n has diagonal weight (1-q)q^n.

**Definition 1.4 (Entropy of a countable diagonal density).**

Lean statement: `D5/S3/Observer/DefectModularFirstLaw/ThermofieldMarginalModularSpectrum.diagonalEntropy`

*Formalization.* `D5/S3/Observer/DefectModularFirstLaw/ThermofieldMarginalModularSpectrum.diagonalEntropy` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The entropy is the infinite sum of -p log p over the real diagonal weights.

**Definition 1.5 (Relative modular energy levels).**

Lean statement: `D5/S3/Observer/DefectModularFirstLaw/ThermofieldMarginalModularSpectrum.relativeModularEnergy`

*Formalization.* `D5/S3/Observer/DefectModularFirstLaw/ThermofieldMarginalModularSpectrum.relativeModularEnergy` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The n-th modular energy is minus the logarithm of the n-th visible density eigenvalue.

**Theorem 1.6 (The local modular first law on the thermofield marginal).**

$$\forall delta \in \mathbb{R}, omega \in \mathbb{R},\; \left(0 < omega \land omega < delta\right) \Rightarrow \operatorname{let} q: \mathbb{R} = {\frac{omega}{delta}}^{2}, \operatorname{let} N: \mathbb{R} = \operatorname{rankOneThermalOccupation}\left(q\right), \operatorname{let} epsilon: \mathbb{R} = \operatorname{defectModularGap}\left(delta, omega\right), \operatorname{let} \rho_{vis}: \operatorname{Matrix}\left(\mathbb{N}, \mathbb{N}, \mathbb{C}\right) = \operatorname{countablePartialTraceRight}\left(\operatorname{rankOneDensity}\left(\operatorname{thermofieldAmplitude}\left(q\right)\right)\right), \left(\operatorname{HasDerivAt}\left(rankOneThermalEntropy, \log (\frac{N + 1}{N}), N\right) \land \left(\log (\frac{N + 1}{N}) = -\log (q) \land -\log (q) = epsilon\right)\right) \land \left(\left(\left(\forall dN \in \mathbb{R},\; \operatorname{fderiv}\left(\mathbb{R}, rankOneThermalEntropy, N\right)\left(dN\right) = epsilon dN\right) \land epsilon = 2 \log (\frac{delta}{omega})\right) \land \left(\rho_{vis} = \operatorname{geometricDiagonalDensity}\left(q\right) \land \left(\operatorname{tsum}\left((n: \mathbb{N} \mapsto \operatorname{re}\left(\left(\rho_{vis}\right)\left(n, n\right)\right))\right) = 1 \land \left(\operatorname{tsum}\left((n: \mathbb{N} \mapsto (n: \mathbb{R}) \operatorname{re}\left(\left(\rho_{vis}\right)\left(n, n\right)\right))\right) = N \land \left(\operatorname{diagonalEntropy}\left(\rho_{vis}\right) = \operatorname{rankOneThermalEntropy}\left(N\right) \land \left(\forall n \in \mathbb{N},\; \operatorname{relativeModularEnergy}\left(q, n + 1\right) - \operatorname{relativeModularEnergy}\left(q, n\right) = epsilon\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/DefectModularFirstLaw/ThermofieldMarginalModularSpectrum.local_modular_first_law_from_thermofield_marginal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For real scales 0 < omega < delta, q is (omega/delta)^2, N is the visible geometric occupation, and epsilon is the defect modular gap 2 log(delta/omega).

The frozen derivative theorem supplies the differential law. The new countable Schmidt construction proves that tracing out the hidden mode from the frozen generic rank-one density gives the normalized geometric density, whose first moment is N and whose diagonal entropy is exactly S(N).

The negative logarithms of successive visible eigenweights differ by epsilon, so epsilon is the adjacent level spacing of the relative modular Hamiltonian. This states only local rank-one modular thermodynamics, not a physical black-hole first law.

## References

- Truth anchor: `D5/S3/Observer/DefectModularFirstLaw/ThermofieldMarginalModularSpectrum.countablePartialTraceRight`
- Truth anchor: `D5/S3/Observer/DefectModularFirstLaw/ThermofieldMarginalModularSpectrum.diagonalEntropy`
- Truth anchor: `D5/S3/Observer/DefectModularFirstLaw/ThermofieldMarginalModularSpectrum.geometricDiagonalDensity`
- Truth anchor: `D5/S3/Observer/DefectModularFirstLaw/ThermofieldMarginalModularSpectrum.local_modular_first_law_from_thermofield_marginal`
- Truth anchor: `D5/S3/Observer/DefectModularFirstLaw/ThermofieldMarginalModularSpectrum.relativeModularEnergy`
- Truth anchor: `D5/S3/Observer/DefectModularFirstLaw/ThermofieldMarginalModularSpectrum.thermofieldAmplitude`
- Dependency: [D5/S3/Observer/DefectModularFirstLaw/EntropyDerivativeEqualsModularGap](EntropyDerivativeEqualsModularGap.md)
- Dependency: [D5/S3/Quantum/PureState/PureStateHandshake](../../Quantum/PureState/PureStateHandshake.md)
