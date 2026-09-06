# Phase Damping in Selected Coordinates

## Abstract

Nontrivial phase damping transported by a matrix equivalence fixes precisely the matrices diagonal in those coordinates, including Hadamard coordinates.

Write M for the complex matrices indexed by Fin(2) in each coordinate. For an equivalence Q from M to M, a damping coefficient c in [0,1], and rho in M, phaseDampingInBasis applies Q, then phaseDamping, then the inverse equivalence.

$$
\operatorname{phaseDampingInBasis}\left(Q, c, \rho\right) = Q^{-1}(\operatorname{phaseDamping}\left(c, Q(\rho)\right))
$$

**Theorem 1.1 (Fixed points are diagonal in the chosen coordinates).**

$$\forall Q \in \operatorname{Equiv}\left(M, M\right),\ \forall c \in [0,1],\ \forall \rho \in M,\ c \neq 1 \Rightarrow (\operatorname{phaseDampingInBasis}\left(Q, c, \rho\right) = \rho \iff (\forall i, j \in \operatorname{Fin}\left(2\right),\ i \neq j \Rightarrow Q(\rho)_{ij} = 0))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/PointerBasis.phase_damping_in_basis_fixed_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Wojciech H. Zurek (2003). *Decoherence, einselection, and the quantum origins of the classical*. DOI: [10.1103/RevModPhys.75.715](https://doi.org/10.1103/RevModPhys.75.715).

*Commentary.*

For every equivalence Q from M to M, every DampingCoefficient c whose real value is not one, and every rho in M, phaseDampingInBasis(Q,c,rho) equals rho if and only if Q(rho)(i,j) = 0 whenever i and j in Fin(2) are distinct. The equivalence is not required to be linear or induced by a unitary basis change, and rho need not be a density matrix.

Applying the inverse-equivalence equality reduces the fixed-point assertion to phaseDamping(c,Q(rho)) = Q(rho). The diagonal fixed-point characterization in `D5/S3/Quantum/Decoherence.phase_damping_fixed_iff_diagonal` then proves both directions. The exclusion of c = 1 is essential: at that coefficient the transported map fixes every matrix.

The Hadamard coordinate transform is conjugation by the normalized two-point Hadamard matrix. Its entrywise definition is the following formula, with a,b,d,e complex:

$$
\operatorname{hadamardCoordinates}\left(\begin{pmatrix}a&b\\d&e\end{pmatrix}\right) = \frac{1}{2}\begin{pmatrix}a+b+d+e&a-b+d-e\\a+b-d-e&a-b-d+e\end{pmatrix}
$$

Applying this transform twice returns rho, so it defines the equivalence hadamardCoordinateEquiv with the same forward and inverse map. The definition fourierPhaseDamping specializes phaseDampingInBasis to this equivalence.

**Theorem 1.2 (Fourier-record fixed points are Hadamard-diagonal).**

$$\forall c \in [0,1],\ \forall \rho \in M,\ c \neq 1 \Rightarrow (\operatorname{fourierPhaseDamping}\left(c, \rho\right) = \rho \iff (\forall i, j \in \operatorname{Fin}\left(2\right),\ i \neq j \Rightarrow \operatorname{hadamardCoordinates}\left(\rho\right)_{ij} = 0))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/PointerBasis.fourier_phase_damping_fixed_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Wojciech H. Zurek (2003). *Decoherence, einselection, and the quantum origins of the classical*. DOI: [10.1103/RevModPhys.75.715](https://doi.org/10.1103/RevModPhys.75.715).

*Commentary.*

For every DampingCoefficient c with real value different from one and every rho in M, fourierPhaseDamping(c,rho) = rho if and only if hadamardCoordinates(rho)(i,j) = 0 for all distinct i,j in Fin(2). This is the preceding theorem instantiated at the explicit Hadamard equivalence. Zurek's pointer-state discussion provides background; the fixed-point statement here concerns the specified transported map.

## References

- Truth anchor: `D5/S3/Quantum/Decoherence.phase_damping_fixed_iff_diagonal`
- Truth anchor: `D5/S3/Quantum/PointerBasis.fourier_phase_damping_fixed_iff`
- Truth anchor: `D5/S3/Quantum/PointerBasis.phase_damping_in_basis_fixed_iff`
- Dependency: [D5/S3/Quantum/Decoherence](Decoherence.md)
