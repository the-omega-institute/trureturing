# Finite-time endpoint average on the central-defect path

## Abstract

The actual central-defect evolution has a positive spectral gap and a finite-window endpoint bound.

**Theorem 1.1 (The central-defect endpoint average).**

Lean statement: `D5/S3/Quantum/Matrix/ReflectedSpectralWindow.central_defect_endpoint_average`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/ReflectedSpectralWindow.central_defect_endpoint_average` (`✓ std3`). ∎

*Citation.* Andrew M. Childs; Richard Cleve; Enrico Deotto; Edward Farhi; Sam Gutmann; Daniel A. Spielman (2003). *Exponential algorithmic speedup by a quantum walk*. DOI: [10.48550/arXiv.quant-ph/0209131](https://doi.org/10.48550/arXiv.quant-ph/0209131). URL: <https://arxiv.org/abs/quant-ph/0209131v2>.

*Commentary.*

Use a path on 2n vertices with n at least one, zero diagonal, unit nearest-neighbor weights and square-root-two weight on the central edge. Enumerate all the eigenvalues with algebraic multiplicity, and define the gap as the minimum of the absolute differences at distinct indices. This gap is strictly positive.

For any positive error parameter, let the time window start at zero and have length at least the vertex count divided by the error parameter and the actual gap. The real time average of the squared norm of the entry from vertex zero to vertex 2n minus one of the matrix exponential of the entrywise complexified path matrix multiplied by minus i times the evolution time strictly exceeds the ratio of one minus the error parameter to the vertex count.

For the weighted path in Childs et al., Section III.D, Lemma 1, the real cosine integral gives half of the source sufficient time. The existing spectral gap theorem gives simple eigenvalues. Coordinate reversal preserves the matrix and each eigenline, so the eigenvectors have equal absolute weights at the endpoints. The exponential acts on these eigenlines by the corresponding phases. The diagonal part of the integrated energy is bounded by Cauchy–Schwarz. Integration of the real cosine terms bounds the remaining interference by its off-diagonal weight.

## References

- Truth anchor: `D5/S3/Quantum/Matrix/ReflectedSpectralWindow.central_defect_endpoint_average`
- Dependency: [D5/S3/Quantum/Dynamics/EnergyEigenstateStationarity](../Dynamics/EnergyEigenstateStationarity.md)
- Dependency: [D5/S3/Quantum/Matrix/CentralSqrtTwoDefectGap](CentralSqrtTwoDefectGap.md)
