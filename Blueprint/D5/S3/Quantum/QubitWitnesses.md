# Qubit Witness Skeletons

## Abstract

Explicit qubit incompatibility, entanglement, and dephasing witnesses.

<a id="describe-pauli-x-and-z-have-no-nonzero-common-eigenvector"></a>

**Theorem 1.1 (Pauli X and Z have no nonzero common eigenvector).**

$$\forall \psi\in\mathbb{C}^{2},\ \forall x,z\in\mathbb{C},\ (X\psi=x\psi \land Z\psi=z\psi) \Rightarrow \psi=0$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QubitWitnesses.pauli_observables_have_no_common_eigenvector` (`✓ std3`). ∎

*Citation.* Julian Schwinger (1960). *Unitary Operator Bases*. DOI: [10.1073/pnas.46.4.570](https://doi.org/10.1073/pnas.46.4.570).

*Commentary.*

The standard Pauli X and Z observables have no nonzero common eigenvector on C^2. This is an explicit incompatibility witness only: it does not prove the Robertson variance inequality, arbitrary-window full-matrix generation, prime-power tensor factorization, general qudit Weyl relations, or any classical ontology forcing the structure. Original numerical-certificate claim not formalized: the source atom's full matrix-unit relations with exact zero certificate error.

<a id="describe-the-bell-coefficient-matrix-is-not-a-simple-tensor"></a>

**Theorem 1.2 (The Bell coefficient matrix is not a simple tensor).**

$\neg\exists \ell,r\in\mathbb{C}^{2},\ \operatorname{productCoefficients}(\ell,r)=\operatorname{bellCoefficients}$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QubitWitnesses.bell_coefficients_are_not_product` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The coefficient matrix of the unnormalized Bell vector |00> + |11> cannot be factored as an outer product. A nonzero normalization scalar does not change this obstruction. This elementary algebraic witness is proved directly in the repository; Bell's 1964 paper treats the spin singlet and locality, not this exact vector or factorization argument. This declaration proves neither a CHSH expectation nor Tsirelson optimality, a local-hidden-variable bound, Kochen-Specker contextuality, hidden-address interpretations, or that probability is not ignorance. Original numerical-certificate claims not formalized: the source atom's CHSH values 2*sqrt(2) = 2.8284 and the classical local-fiber bound 2.0.

<a id="describe-iterated-phase-damping-has-the-exact-qubit-certificate"></a>

**Theorem 1.3 (Iterated phase damping has the exact qubit certificate).**

$$\forall c\in[0,1],\ \forall N\in\mathbb{N},\ \rho_{N}:=\operatorname{phaseDampingIterate}(c,N,\operatorname{equalSuperpositionDensity}),\ (\rho_{N})_{00}=\frac{1}{2} \land (\rho_{N})_{11}=\frac{1}{2} \land (\rho_{N})_{01}=\frac{1}{2}c^{N} \land (\rho_{N})_{10}=\frac{1}{2}c^{N}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QubitWitnesses.equal_superposition_phase_damping_certificate` (`✓ std3`). ∎

*Citation.* Wojciech H. Zurek (2003). *Decoherence, einselection, and the quantum origins of the classical*. DOI: [10.1103/RevModPhys.75.715](https://doi.org/10.1103/RevModPhys.75.715).

*Commentary.*

For the standard real phase-damping map with retention coefficient c in [0,1], N repetitions leave both equal-superposition populations at one half and multiply both coherence entries by c^N. The map is assumed, not derived from a system-environment Hamiltonian. The declaration does not identify this repository's ledger with an environment, bookkeeping with decoherence, or address selection with einselection. Original certificate coverage: the source atom's symbolic (1/2) * c0^N coherence law and fixed one-half populations are formalized exactly; the atom supplies no fixed numeric c0 or N.

## References

- Truth anchor: `D5/S3/Quantum/QubitWitnesses.bell_coefficients_are_not_product`
- Truth anchor: `D5/S3/Quantum/QubitWitnesses.equal_superposition_phase_damping_certificate`
- Truth anchor: `D5/S3/Quantum/QubitWitnesses.pauli_observables_have_no_common_eigenvector`
