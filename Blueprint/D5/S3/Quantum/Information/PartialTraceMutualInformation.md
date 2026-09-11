# Partial Trace and Quantum Mutual Information

## Abstract

Partial traces give density-state marginals, and independent product states have zero quantum mutual information.

**Theorem 1.1 (Tracing out the left factor preserves positivity).**

$$\forall M, \operatorname{PosSemidef}\left(M\right) \Rightarrow \operatorname{PosSemidef}\left(\operatorname{partialTraceLeft}\left(M\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/PartialTraceMutualInformation.partialTraceLeft_posSemidef` (`✓ std3`). ∎

*Citation.* Zayn Blore (2026). *Partial trace and spectral von Neumann entropy in CsdLean4*. URL: <https://github.com/zblore/csd-lean4/tree/13eda16971c66de4bc9f550e418dd4fdf59a5121/CsdLean4/Mathlib>.

*Commentary.*

For arbitrary finite carriers A and B, the reduced matrix is a finite sum of principal submatrices.

**Theorem 1.2 (Tracing out the right factor preserves positivity).**

$$\forall M, \operatorname{PosSemidef}\left(M\right) \Rightarrow \operatorname{PosSemidef}\left(\operatorname{partialTraceRight}\left(M\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/PartialTraceMutualInformation.partialTraceRight_posSemidef` (`✓ std3`). ∎

*Citation.* Zayn Blore (2026). *Partial trace and spectral von Neumann entropy in CsdLean4*. URL: <https://github.com/zblore/csd-lean4/tree/13eda16971c66de4bc9f550e418dd4fdf59a5121/CsdLean4/Mathlib>.

*Commentary.*

The same principal-submatrix argument applies to the other factor.

**Theorem 1.3 (The left partial trace preserves trace).**

$$\forall M, \operatorname{trace}\left(\operatorname{partialTraceLeft}\left(M\right)\right) = \operatorname{trace}\left(M\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/PartialTraceMutualInformation.trace_partialTraceLeft` (`✓ std3`). ∎

*Citation.* Zayn Blore (2026). *Partial trace and spectral von Neumann entropy in CsdLean4*. URL: <https://github.com/zblore/csd-lean4/tree/13eda16971c66de4bc9f550e418dd4fdf59a5121/CsdLean4/Mathlib>.

*Commentary.*

For every joint matrix, summing the reduced diagonal recovers its diagonal sum.

**Theorem 1.4 (The right partial trace preserves trace).**

$$\forall M, \operatorname{trace}\left(\operatorname{partialTraceRight}\left(M\right)\right) = \operatorname{trace}\left(M\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/PartialTraceMutualInformation.trace_partialTraceRight` (`✓ std3`). ∎

*Citation.* Zayn Blore (2026). *Partial trace and spectral von Neumann entropy in CsdLean4*. URL: <https://github.com/zblore/csd-lean4/tree/13eda16971c66de4bc9f550e418dd4fdf59a5121/CsdLean4/Mathlib>.

*Commentary.*

Together with positivity, trace preservation gives a normalized marginal.

**Definition 1.5 (Mutual information of a joint density state).**

$$\operatorname{quantumMutualInformation}\left(\rho\right) = \operatorname{vonNeumannEntropy}\left(\operatorname{marginalRight}\left(\rho\right)\right) + \operatorname{vonNeumannEntropy}\left(\operatorname{marginalLeft}\left(\rho\right)\right) - \operatorname{vonNeumannEntropy}\left(\rho\right)$$

*Formalization.* `D5/S3/Quantum/Information/PartialTraceMutualInformation.quantumMutualInformation` (`✓ std3`).

*Citation.* John Watrous (2018). *The Theory of Quantum Information — spectral calculus, reductions and entropy*. URL: <https://cs.uwaterloo.ca/~watrous/TQI/TQI.pdf>.

*Commentary.*

The only input is the joint state. marginalRight retains A and marginalLeft retains B; each is constructed by partial trace.

**Theorem 1.6 (Entropy adds on independent product states).**

$$\forall \rho, \sigma, \operatorname{vonNeumannEntropy}\left(\operatorname{productState}\left(\rho, \sigma\right)\right) = \operatorname{vonNeumannEntropy}\left(\rho\right) + \operatorname{vonNeumannEntropy}\left(\sigma\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/PartialTraceMutualInformation.vonNeumannEntropy_productState` (`✓ std3`). ∎

*Citation.* Zayn Blore (2026). *Partial trace and spectral von Neumann entropy in CsdLean4*. URL: <https://github.com/zblore/csd-lean4/tree/13eda16971c66de4bc9f550e418dd4fdf59a5121/CsdLean4/Mathlib>.

*Commentary.*

The spectrum of the product is the multiset of pairwise eigenvalue products. For any two density states on finite carriers, including singular states, the proof uses the zero value of x log x at zero.

**Theorem 1.7 (Independent product states have zero mutual information).**

$$\forall \rho, \sigma, \operatorname{quantumMutualInformation}\left(\operatorname{productState}\left(\rho, \sigma\right)\right) = 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/PartialTraceMutualInformation.quantumMutualInformation_productState` (`✓ std3`). ∎

*Citation.* Zayn Blore (2026). *Partial trace and spectral von Neumann entropy in CsdLean4*. URL: <https://github.com/zblore/csd-lean4/tree/13eda16971c66de4bc9f550e418dd4fdf59a5121/CsdLean4/Mathlib>.

*Commentary.*

The actual partial traces recover the two factors. Their entropies cancel the entropy of the product by tensor additivity.

## References

- Truth anchor: `D5/S3/Quantum/Information/PartialTraceMutualInformation.partialTraceLeft_posSemidef`
- Truth anchor: `D5/S3/Quantum/Information/PartialTraceMutualInformation.partialTraceRight_posSemidef`
- Truth anchor: `D5/S3/Quantum/Information/PartialTraceMutualInformation.quantumMutualInformation`
- Truth anchor: `D5/S3/Quantum/Information/PartialTraceMutualInformation.quantumMutualInformation_productState`
- Truth anchor: `D5/S3/Quantum/Information/PartialTraceMutualInformation.trace_partialTraceLeft`
- Truth anchor: `D5/S3/Quantum/Information/PartialTraceMutualInformation.trace_partialTraceRight`
- Truth anchor: `D5/S3/Quantum/Information/PartialTraceMutualInformation.vonNeumannEntropy_productState`
- Dependency: [D5/S3/Quantum/Divergence/VonNeumannEntropyPinching](../Divergence/VonNeumannEntropyPinching.md)
