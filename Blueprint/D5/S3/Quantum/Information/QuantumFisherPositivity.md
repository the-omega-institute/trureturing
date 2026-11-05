# Positivity of a finite Hermitian Fisher form

## Abstract

Finite-dimensional Hermitian Fisher-form quadratic forms are nonnegative.

Fix finite parameter and state indices. A positive semidefinite complex state matrix rho and a Hermitian matrix L_i for every parameter i define the real Fisher-form entry J_ij = Re(trace(rho L_i L_j)). The theorem establishes the full real quadratic form directly, with no claim about infinite-dimensional or unbounded-operator models.

**Theorem 1.1 (The Fisher quadratic form is nonnegative).**

$$\forall iota \in Type,\; \forall d \in Type,\; [\operatorname{Fintype}\left(iota\right)] [\operatorname{Fintype}\left(d\right)] [\operatorname{DecidableEq}\left(d\right)] \forall rho \in \operatorname{Matrix}\left(d, d, \mathbb{C}\right),\; \forall a \in iota \to \mathbb{R},\; \forall L \in iota \to \operatorname{Matrix}\left(d, d, \mathbb{C}\right),\; \operatorname{Matrix.trace}\left(rho\right) = 1 \Rightarrow \left(\operatorname{Matrix.PosSemidef}\left(rho\right) \Rightarrow \left(\left(\forall i \in iota,\; \operatorname{Matrix.IsHermitian}\left(L\left(i\right)\right)\right) \Rightarrow 0 \le \sum_{i\in iota} \sum_{j\in iota} a\left(i\right) \cdot \operatorname{Complex.re}\left(\operatorname{Matrix.trace}\left(rho \cdot L\left(i\right) \cdot L\left(j\right)\right)\right) \cdot a\left(j\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/QuantumFisherPositivity.quantum_fisher_quadratic_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a real coefficient function a, the combined Hermitian matrix is the finite sum A = Σ_i (a_i : C) • L_i. Hermiticity of every L_i makes A Hermitian. The finite sum expands the displayed quadratic form to Re(trace(rho A²)).

Cyclicity changes this to Re(trace(A rho A)). The Gram matrix A* A is positive semidefinite, so the positive-state trace pairing is nonnegative. This is the finite-dimensional bridge behind the statistical positivity clause. A separate coordinate-congruence application is outside this declaration.

**Theorem 1.2 (Real Jacobian congruences preserve Fisher nonnegativity).**

$$\forall iota \in Type,\; \forall d \in Type,\; \forall kappa \in Type,\; [\operatorname{Fintype}\left(iota\right)] [\operatorname{Fintype}\left(d\right)] [\operatorname{Fintype}\left(kappa\right)] [\operatorname{DecidableEq}\left(d\right)] \forall rho \in \operatorname{Matrix}\left(d, d, \mathbb{C}\right),\; \forall b \in kappa \to \mathbb{R},\; \forall L \in iota \to \operatorname{Matrix}\left(d, d, \mathbb{C}\right),\; \forall T \in \operatorname{Matrix}\left(iota, kappa, \mathbb{R}\right),\; \operatorname{Matrix.trace}\left(rho\right) = 1 \Rightarrow \left(\operatorname{Matrix.PosSemidef}\left(rho\right) \Rightarrow \left(\left(\forall p \in iota,\; \operatorname{Matrix.IsHermitian}\left(L\left(p\right)\right)\right) \Rightarrow 0 \le \sum_{r\in kappa} \sum_{s\in kappa} b\left(r\right) \cdot \sum_{p\in iota} \sum_{q\in iota} T\left(p, r\right) \cdot \operatorname{Complex.re}\left(\operatorname{Matrix.trace}\left(rho \cdot L\left(p\right) \cdot L\left(q\right)\right)\right) \cdot T\left(q, s\right) \cdot b\left(s\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/QuantumFisherPositivity.quantum_fisher_congruence_quadratic_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a real matrix T and coefficient vector b, the displayed transformed form is the original Fisher form evaluated at c = T.mulVec b. The first theorem therefore proves its nonnegativity by finite sum expansion. Since this holds for every coefficient vector and real Jacobian, no transformed direction has a negative value, so this Fisher form cannot supply a Lorentzian negative direction.

## References

- Truth anchor: `D5/S3/Quantum/Information/QuantumFisherPositivity.quantum_fisher_congruence_quadratic_nonneg`
- Truth anchor: `D5/S3/Quantum/Information/QuantumFisherPositivity.quantum_fisher_quadratic_nonneg`
- Dependency: [D5/S3/Quantum/Matrix/MatrixSelfPairing](../Matrix/MatrixSelfPairing.md)
