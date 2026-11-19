# Periodic two-site marginal differential

## Abstract

Differential rank of the actual two-site marginal on the periodic binary bond-two chart

**Definition 1.1 (Affine chart).**

Lean statement: `D5/S3/Quantum/TensorNetworks/PeriodicMPSTwoSiteDifferential.chart`

*Formalization.* `D5/S3/Quantum/TensorNetworks/PeriodicMPSTwoSiteDifferential.chart` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The two symbol matrices are diag(a,b) and ((c,1),(d,e)). The chart fixes a and varies the real and imaginary parts of b,c,d,e.

**Definition 1.2 (Radial column and real coordinate derivatives).**

Lean statement: `D5/S3/Quantum/TensorNetworks/PeriodicMPSTwoSiteDifferential.augmented`

*Formalization.* `D5/S3/Quantum/TensorNetworks/PeriodicMPSTwoSiteDifferential.augmented` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The value is the first column. The next eight columns are derivatives along the real and imaginary axes of b,c,d,e. Rows index all complex entries of the Hermitian marginal.

**Theorem 1.3 (Full projective differential rank at every length).**

$$\forall r \in Nat,\; \exists a \in Complex,\; \exists x \in Fin\left(4\right) \to Complex,\; \exists s \in Fin\left(9\right) \to Prod\left(Prod\left(Fin\left(2\right), Fin\left(2\right)\right), Prod\left(Fin\left(2\right), Fin\left(2\right)\right)\right),\; det\left(submatrix\left(augmented\left(r, a, x\right), s, id\right)\right) \neq 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/PeriodicMPSTwoSiteDifferential.projective_rank_eight` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

For every natural r the length r+4 admits a point of the displayed chart with a nonsingular nine-row minor. Complex independence of the value and the eight real derivative columns implies that the derivative has rank eight after quotienting out the real line of the value.

Expanding the actual partial trace gives the trace of two Kronecker blocks followed by the complement transfer power. Evaluating Gaussian-integer polynomial lines in dual numbers retains the value and derivative and commutes with reduction modulo 13, where the imaginary unit maps to 5. The certificate verifies the selected minors by elimination and checks the base transfer identity at exponents 16 and 4 at four points. The square-zero ideal and characteristic 13 lift this to equality at exponents 164 and 8 for every direction.

This differential result addresses local identifiability within the chart. Global exclusion of phase-inequivalent states with the same observed density remains a separate part of the periodic sharp-threshold question.

## References

- Truth anchor: `D5/S3/Quantum/TensorNetworks/PeriodicMPSTwoSiteDifferential.augmented`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/PeriodicMPSTwoSiteDifferential.chart`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/PeriodicMPSTwoSiteDifferential.projective_rank_eight`
- Dependency: [D5/S3/Quantum/TensorNetworks/PeriodicMPSTwoSiteAmbiguity](PeriodicMPSTwoSiteAmbiguity.md)
