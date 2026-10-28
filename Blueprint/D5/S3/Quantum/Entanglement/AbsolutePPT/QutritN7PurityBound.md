# Qutrit APPT purity for n = 7

## Abstract

Literal qutrit APPT density matrices satisfy the sharp purity bound for n = 7.

**Theorem 1.1 (The reusable length-21 spectral certificate).**

$$\forall (l:Fin\left(21\right)\to\mathbb{R}), ((Antitone\left(l\right))\land (0\leq l\left(20\right))\land (\sum_{i:Fin\left(21\right)}(l\left(i\right))=1)\land (Matrix.PosSemidef\left(QutritSpectralReduction.K1\left(QutritSpectralReduction.boundaryValues\left(4, l\right)\right)\right))\land (Matrix.PosSemidef\left(QutritSpectralReduction.K2\left(QutritSpectralReduction.boundaryValues\left(4, l\right)\right)\right)))\Rightarrow \sum_{i:Fin\left(21\right)}((l\left(i\right))^{2})\leq \frac{29}{(23)^{2}}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/QutritN7PurityBound.certificate_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every antitone real 21-coordinate vector of mass one with nonnegative last coordinate and both qutrit boundary matrices positive semidefinite has square sum at most 29/529. The rational gap certificate applies directly to spectral data. Boundary-preserving insertion and deletion use this endpoint after positive mass normalization; no literal APPT sufficiency is asserted for arbitrary boundary-feasible spectra.

**Theorem 1.2 (Sharp density-matrix purity estimate).**

$$\forall (rho:Matrix\left((Fin\left(3\right)\times Fin\left(7\right)), (Fin\left(3\right)\times Fin\left(7\right)), \mathbb{C}\right)), ((Matrix.PosSemidef\left(rho\right))\land (Matrix.trace\left(rho\right)=1)\land (APPT\left(rho\right)))\Rightarrow Complex.re\left(Matrix.trace\left(rho\cdot rho\right)\right)\leq \frac{29}{(23)^{2}}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/QutritN7PurityBound.purity_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every positive semidefinite trace-one complex matrix on Fin 3 × Fin 7 satisfying literal APPT has the stated real trace-square bound. APPT means that the partial transpose of U rho Uᴴ is positive semidefinite for every unitary U, as defined in QutritPerturbationAttainment. The proof applies QutritSpectralReduction.spectral_reduction to obtain ordered spectral certificate coordinates with both boundary LMIs and matching purity, then consumes the reusable rational gap certificate. All displayed quotients are real division.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/QutritN7PurityBound.certificate_bound`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/QutritN7PurityBound.purity_bound`
- Dependency: [D5/S3/Quantum/Entanglement/AbsolutePPT/QutritSpectralReduction](QutritSpectralReduction.md)
