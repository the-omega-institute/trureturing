# HS4Assembly

## Abstract

The literal marginal density states define the average entropy in bits.

**Definition 1.1 (Literal index tables).**

$$\forall (c : \operatorname{Fin}\left(3\right)), (\operatorname{cutIndex}\left(c\right) = ![!![0,1,2,3;4,5,6,7;8,9,10,11;12,13,14,15],!![0,1,4,5;2,3,6,7;8,9,12,13;10,11,14,15],!![0,2,4,6;1,3,5,7;8,10,12,14;9,11,13,15]]\left(c\right))$$

*Formalization.* `D5/S3/Quantum/Entanglement/HiguchiSudbery/HS4Assembly.cutIndex` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The matrix rows and columns are ordered as 00, 01, 10, 11. The three index tables retain AB, AC and AD, respectively, for the basis index 8a+4b+2c+d.

**Definition 1.2 (Flattening amplitudes).**

$$\forall (z : \operatorname{Fin}\left(16\right) \to \operatorname{Complex}), (\forall (c : \operatorname{Fin}\left(3\right)), (\operatorname{cutFlatten}\left(z, c\right) = (r : \operatorname{Fin}\left(4\right)) \mapsto ((b : \operatorname{Fin}\left(4\right)) \mapsto (z\left(\operatorname{cutIndex}\left(c, r, b\right)\right)))))$$

*Formalization.* `D5/S3/Quantum/Entanglement/HiguchiSudbery/HS4Assembly.cutFlatten` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each matrix entry is the amplitude at the literal cutIndex value; no basis relabeling is hidden in this definition.

**Definition 1.3 (Literal marginal matrix).**

$$\forall (z : \operatorname{Fin}\left(16\right) \to \operatorname{Complex}), (\forall (c : \operatorname{Fin}\left(3\right)), (\operatorname{cutMatrix}\left(z, c\right) = \operatorname{partialTraceRight}\left(\operatorname{rankOneDensity}\left((p : \operatorname{Fin}\left(4\right)\times\operatorname{Fin}\left(4\right)) \mapsto (\operatorname{cutFlatten}\left(z, c, p.1, p.2\right))\right)\right)))$$

*Formalization.* `D5/S3/Quantum/Entanglement/HiguchiSudbery/HS4Assembly.cutMatrix` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The repository’s partialTraceRight and rankOneDensity are reused directly. The carrier is Fin 4 × Fin 4, with the retained pair in the first component.

**Definition 1.4 (Normalized literal marginal).**

$$\forall (z : \operatorname{Fin}\left(16\right) \to \operatorname{Complex}), (\forall (hz : \sum_{i \in \operatorname{Fin}\left(16\right)} \operatorname{Complex.normSq}\left(z\left(i\right)\right) = 1), (\forall (c : \operatorname{Fin}\left(3\right)), (\forall (h : \operatorname{dotProduct}\left(\operatorname{star}\left((p : \operatorname{Fin}\left(4\right)\times\operatorname{Fin}\left(4\right)) \mapsto (\operatorname{cutFlatten}\left(z, c, p.1, p.2\right))\right), (p : \operatorname{Fin}\left(4\right)\times\operatorname{Fin}\left(4\right)) \mapsto (\operatorname{cutFlatten}\left(z, c, p.1, p.2\right))\right) = 1), (\operatorname{cutDensity}\left(z, hz, c\right) = \operatorname{marginalRight}\left(\operatorname{pureDensityState}\left((p : \operatorname{Fin}\left(4\right)\times\operatorname{Fin}\left(4\right)) \mapsto (\operatorname{cutFlatten}\left(z, c, p.1, p.2\right)), h\right)\right)))))$$

*Formalization.* `D5/S3/Quantum/Entanglement/HiguchiSudbery/HS4Assembly.cutDensity` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed h is any proof of the flattened-vector normalization; the amplitude normalization hz supplies it in Lean. Proof irrelevance makes the resulting density state independent of this proof term. Both pureDensityState and marginalRight are reused repository definitions.

**Definition 1.5 (Average two-qubit entropy).**

$$\forall (z : \operatorname{Fin}\left(16\right) \to \operatorname{Complex}), (\forall (h : \sum_{i \in \operatorname{Fin}\left(16\right)} \operatorname{Complex.normSq}\left(z\left(i\right)\right) = 1), (\operatorname{averageEntropy}\left(z, h\right) = \frac{\sum_{c \in \operatorname{Fin}\left(3\right)} \operatorname{vonNeumannEntropy}\left(\operatorname{cutDensity}\left(z, h, c\right)\right)}{3\cdot \operatorname{Real.log}\left(2\right)}))$$

*Formalization.* `D5/S3/Quantum/Entanglement/HiguchiSudbery/HS4Assembly.averageEntropy` (`✓ std3`).

*Citation.* A. Higuchi; A. Sudbery (2000). *How entangled can two couples get?*. DOI: [10.1016/S0375-9601(00)00506-4](https://doi.org/10.1016/S0375-9601(00)00506-4). URL: <https://arxiv.org/abs/quant-ph/0005013>.

*Commentary.*

Section 3, p. 5: “The second equality holds because complementary pairs have equal entropy.” The displayed average (E_AB+E_AC+E_AD)/3 uses the repository’s vonNeumannEntropy divided by log 2, so its units are bits. Index c ranges over Fin 3 in the order AB, AC, AD.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/HiguchiSudbery/HS4Assembly.averageEntropy`
- Truth anchor: `D5/S3/Quantum/Entanglement/HiguchiSudbery/HS4Assembly.cutDensity`
- Truth anchor: `D5/S3/Quantum/Entanglement/HiguchiSudbery/HS4Assembly.cutFlatten`
- Truth anchor: `D5/S3/Quantum/Entanglement/HiguchiSudbery/HS4Assembly.cutIndex`
- Truth anchor: `D5/S3/Quantum/Entanglement/HiguchiSudbery/HS4Assembly.cutMatrix`
- Dependency: [D5/S3/Quantum/Dynamics/EnergyEigenstateStationarity](../../Dynamics/EnergyEigenstateStationarity.md)
- Dependency: [D5/S3/Quantum/Entanglement/HiguchiSudbery/EntropyReduction](EntropyReduction.md)
- Dependency: [D5/S3/Quantum/Fibers/ProjectiveInteriorProbabilityFiber](../../Fibers/ProjectiveInteriorProbabilityFiber.md)
- Dependency: [D5/S3/Quantum/Information/InputInformationBalance](../../Information/InputInformationBalance.md)
