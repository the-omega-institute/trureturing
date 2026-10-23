# Extreme two-qutrit states have at most six spectral levels

## Abstract

The achievable upper bound on the number of distinct eigenvalues of extreme two-qutrit absolutely PPT states is six.

**Definition 1.1 (Absolutely PPT density matrices).**

$$apStates=(\{rho\mid ((rho).PosSemidef)\land ((rho).trace=1)\land (APPT\left(rho\right))\}:Set\left(Matrix\left((Fin\left(3\right)\times Fin\left(3\right)), (Fin\left(3\right)\times Fin\left(3\right)), \mathbb{C}\right)\right))$$

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/QutritExtremeSixLevels.apStates` (`✓ std3`).

*Citation.* Nalan Wang; Lin Chen; Zhiwei Song (2026). *Extreme points of absolutely PPT states with exactly three distinct eigenvalues*. DOI: [10.1088/1402-4896/ae9148](https://doi.org/10.1088/1402-4896/ae9148). URL: <https://arxiv.org/abs/2603.20717v1>.

*Commentary.*

Definition 1, page 3: “A separable (resp. PPT) state ρ is called absolutely separable (resp. PPT) if it remains separable (PPT) regardless of what global unitary operation is applied. That is, for any unitary matrix U, the state UρU† is separable (resp. PPT).” Here the PPT case is represented by the positive semidefinite trace-one Matrix condition and APPT.

**Definition 1.2 (The achievable upper bound).**

$$claim=((\forall (rho:Matrix\left((Fin\left(3\right)\times Fin\left(3\right)), (Fin\left(3\right)\times Fin\left(3\right)), \mathbb{C}\right)), (rho\in Set.extremePoints\left(\mathbb{R}, apStates\right))\Rightarrow ((spectrum\left(\mathbb{C}, rho\right)).ncard\leq 6))\land (\exists (rho:Matrix\left((Fin\left(3\right)\times Fin\left(3\right)), (Fin\left(3\right)\times Fin\left(3\right)), \mathbb{C}\right)), (rho\in Set.extremePoints\left(\mathbb{R}, apStates\right))\land ((spectrum\left(\mathbb{C}, rho\right)).ncard=6)))$$

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/QutritExtremeSixLevels.claim` (`✓ std3`).

*Citation.* Nalan Wang; Lin Chen; Zhiwei Song (2026). *Extreme points of absolutely PPT states with exactly three distinct eigenvalues*. DOI: [10.1088/1402-4896/ae9148](https://doi.org/10.1088/1402-4896/ae9148). URL: <https://arxiv.org/abs/2603.20717v1>.

*Commentary.*

Section VII, Conclusions, page 29: “Fourth, what is the achievable upper bound of distinct eigenvalues of extreme two-qutrit AP states?” The encoding uses Set.extremePoints over the real scalar field and the complex spectrum. Set.ncard counts distinct eigenvalues without multiplicity. The upper bound is six, and six is attained.

**Theorem 1.3 (Six is the sharp bound).**

$$(\forall (rho:Matrix\left((Fin\left(3\right)\times Fin\left(3\right)), (Fin\left(3\right)\times Fin\left(3\right)), \mathbb{C}\right)), (rho\in Set.extremePoints\left(\mathbb{R}, apStates\right))\Rightarrow ((spectrum\left(\mathbb{C}, rho\right)).ncard\leq 6))\land (\exists (rho:Matrix\left((Fin\left(3\right)\times Fin\left(3\right)), (Fin\left(3\right)\times Fin\left(3\right)), \mathbb{C}\right)), (rho\in Set.extremePoints\left(\mathbb{R}, apStates\right))\land ((spectrum\left(\mathbb{C}, rho\right)).ncard=6))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/QutritExtremeSixLevels.result` (`✓ std3`). ∎

*Resolves.* `Problems/wang-chen-song-2026-appt-extreme-six-levels` (proved) by `D5/S3/Quantum/Entanglement/AbsolutePPT/QutritExtremeSixLevels.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"wang-chen-song-2026-appt-extreme-six-levels","declaration_gid":"D5/S3/Quantum/Entanglement/AbsolutePPT/QutritExtremeSixLevels.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Nalan Wang; Lin Chen; Zhiwei Song (2026). *Extreme points of absolutely PPT states with exactly three distinct eigenvalues*. DOI: [10.1088/1402-4896/ae9148](https://doi.org/10.1088/1402-4896/ae9148). URL: <https://arxiv.org/abs/2603.20717v1>.

*Commentary.*

Every extreme two-qutrit AP state has at most six distinct eigenvalues, and an extreme state with six distinct eigenvalues exists. A feasible two-sided perturbation excludes seven or more levels; the supporting functional proves attainment.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/QutritExtremeSixLevels.apStates`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/QutritExtremeSixLevels.claim`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/QutritExtremeSixLevels.result`
- Dependency: [D5/S3/Quantum/Entanglement/AbsolutePPT/QutritSpectralFeasiblePerturbation](QutritSpectralFeasiblePerturbation.md)
