# Qutrit APPT purity for n = 4

## Abstract

Literal qutrit APPT density matrices satisfy the sharp purity bound for n = 4.

**Theorem 1.1 (Sharp density-matrix purity estimate).**

$$\forall (rho:Matrix\left((Fin\left(3\right)\times Fin\left(4\right)), (Fin\left(3\right)\times Fin\left(4\right)), \mathbb{C}\right)), ((Matrix.PosSemidef\left(rho\right))\land (Matrix.trace\left(rho\right)=1)\land (APPT\left(rho\right)))\Rightarrow Complex.re\left(Matrix.trace\left(rho\cdot rho\right)\right)\leq \frac{20}{(14)^{2}}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/QutritN4PurityBound.purity_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every positive semidefinite trace-one complex matrix on Fin 3 × Fin 4 satisfying literal APPT has the stated real trace-square bound. APPT means that the partial transpose of U rho Uᴴ is positive semidefinite for every unitary U, as defined in QutritPerturbationAttainment. The proof applies QutritSpectralReduction.spectral_reduction to obtain ordered spectral certificate coordinates with both boundary LMIs and matching purity, then consumes the private rational gap certificate. All displayed quotients are real division.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/QutritN4PurityBound.purity_bound`
- Dependency: [D5/S3/Quantum/Entanglement/AbsolutePPT/QutritSpectralReduction](QutritSpectralReduction.md)
