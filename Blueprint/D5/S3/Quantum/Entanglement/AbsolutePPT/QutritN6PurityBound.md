# Qutrit APPT purity for n = 6

## Abstract

Literal qutrit APPT density matrices satisfy the sharp purity bound for n = 6.

**Theorem 1.1 (Sharp density-matrix purity estimate).**

$$\forall (rho:Matrix\left((Fin\left(3\right)\times Fin\left(6\right)), (Fin\left(3\right)\times Fin\left(6\right)), \mathbb{C}\right)), ((Matrix.PosSemidef\left(rho\right))\land (Matrix.trace\left(rho\right)=1)\land (APPT\left(rho\right)))\Rightarrow Complex.re\left(Matrix.trace\left(rho\cdot rho\right)\right)\leq \frac{26}{(20)^{2}}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/QutritN6PurityBound.purity_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every positive semidefinite trace-one complex matrix on Fin 3 × Fin 6 satisfying literal APPT has the stated real trace-square bound. APPT means that the partial transpose of U rho Uᴴ is positive semidefinite for every unitary U, as defined in QutritPerturbationAttainment. The proof applies QutritSpectralReduction.spectral_reduction to obtain ordered spectral certificate coordinates with both boundary LMIs and matching purity, then consumes the private rational gap certificate. All displayed quotients are real division.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/QutritN6PurityBound.purity_bound`
- Dependency: [D5/S3/Quantum/Entanglement/AbsolutePPT/QutritSpectralReduction](QutritSpectralReduction.md)
