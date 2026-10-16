# Qutrit APPT purity for n = 6

## Abstract

Literal qutrit APPT density matrices satisfy the sharp purity bound for n = 6.

**Theorem 1.1 (The reusable length-18 spectral certificate).**

$$\forall (l:Fin\left(18\right)\to \mathbb{R}), ((Antitone\left(l\right))\land (0\leq l\left(17\right))\land (\sum_{i:Fin\left(18\right)} l\left(i\right)=1)\land (Matrix.PosSemidef\left(QutritSpectralReduction.K1\left(QutritSpectralReduction.boundaryValues\left(3, l\right)\right)\right))\land (Matrix.PosSemidef\left(QutritSpectralReduction.K2\left(QutritSpectralReduction.boundaryValues\left(3, l\right)\right)\right)))\Rightarrow \sum_{i:Fin\left(18\right)} (l\left(i\right))^{2}\leq \frac{26}{(20)^{2}}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/QutritN6PurityBound.certificate_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every antitone real 18-coordinate vector of mass one with nonnegative last coordinate and both qutrit boundary matrices positive semidefinite, the spectral square sum is at most 26/400. This exposes the existing kernel-checked rational gap certificate without changing its statement or proof. The four-by-four spectral interpolation consumes this certificate after middle-coordinate insertion or deletion and mass normalization. The hypotheses are spectral LMIs; the certificate itself does not assume or characterize four-by-four APPT.

**Theorem 1.2 (Sharp density-matrix purity estimate).**

$$\forall (rho:Matrix\left((Fin\left(3\right)\times Fin\left(6\right)), (Fin\left(3\right)\times Fin\left(6\right)), \mathbb{C}\right)), ((Matrix.PosSemidef\left(rho\right))\land (Matrix.trace\left(rho\right)=1)\land (APPT\left(rho\right)))\Rightarrow Complex.re\left(Matrix.trace\left(rho\cdot rho\right)\right)\leq \frac{26}{(20)^{2}}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/QutritN6PurityBound.purity_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every positive semidefinite trace-one complex matrix on Fin 3 × Fin 6 satisfying literal APPT has the stated real trace-square bound. APPT means that the partial transpose of U rho Uᴴ is positive semidefinite for every unitary U, as defined in QutritPerturbationAttainment. The proof applies QutritSpectralReduction.spectral_reduction to obtain ordered spectral certificate coordinates with both boundary LMIs and matching purity, then consumes the public reusable rational gap certificate. All displayed quotients are real division.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/QutritN6PurityBound.certificate_bound`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/QutritN6PurityBound.purity_bound`
- Dependency: [D5/S3/Quantum/Entanglement/AbsolutePPT/QutritSpectralReduction](QutritSpectralReduction.md)
