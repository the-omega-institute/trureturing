# Qutrit APPT purity for n = 8

## Abstract

Literal qutrit APPT density matrices satisfy the sharp purity bound for n = 8.

**Theorem 1.1 (Sharp ordered-spectrum certificate).**

$$\forall (l:Fin\left(24\right)\to \mathbb{R}), ((Antitone\left(l\right))\land (0\leq l\left(23\right))\land (\sum_{i:Fin\left(24\right)} l\left(i\right)=1)\land (Matrix.PosSemidef\left(K1\left(boundaryValues\left(5, l\right)\right)\right))\land (Matrix.PosSemidef\left(K2\left(boundaryValues\left(5, l\right)\right)\right)))\Rightarrow \sum_{i:Fin\left(24\right)} (l\left(i\right))^{2}\leq \frac{32}{(26)^{2}}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/QutritN8PurityBound.certificate_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any antitone real twenty-four-vector of mass one with nonnegative last entry, the two qutrit boundary matrices imply squared mass at most 32/26². The boundary selector is QutritSpectralReduction.boundaryValues 5; K1 and K2 are its real three-dimensional matrices. This certificate has no tensor-factor hypothesis and applies to both the 3-by-8 and 4-by-6 density reductions. Its proof is an exact rational gap certificate.

**Theorem 1.2 (Sharp density-matrix purity estimate).**

$$\forall (rho:Matrix\left((Fin\left(3\right)\times Fin\left(8\right)), (Fin\left(3\right)\times Fin\left(8\right)), \mathbb{C}\right)), ((Matrix.PosSemidef\left(rho\right))\land (Matrix.trace\left(rho\right)=1)\land (APPT\left(rho\right)))\Rightarrow Complex.re\left(Matrix.trace\left(rho\cdot rho\right)\right)\leq \frac{32}{(26)^{2}}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/QutritN8PurityBound.purity_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every positive semidefinite trace-one complex matrix on Fin 3 × Fin 8 satisfying literal APPT has the stated real trace-square bound. APPT means that the partial transpose of U rho Uᴴ is positive semidefinite for every unitary U, as defined in QutritPerturbationAttainment. The proof applies QutritSpectralReduction.spectral_reduction to obtain ordered spectral certificate coordinates with both boundary LMIs and matching purity, then consumes the rational gap certificate. All displayed quotients are real division.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/QutritN8PurityBound.certificate_bound`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/QutritN8PurityBound.purity_bound`
- Dependency: [D5/S3/Quantum/Entanglement/AbsolutePPT/QutritSpectralReduction](QutritSpectralReduction.md)
