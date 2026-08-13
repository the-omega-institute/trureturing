# Zeta Conjugation Covariance

## Abstract

Riemann zeta and both completed readings commute with conjugation and conjugate reflection.

**Theorem 1.1 (Completed zeta commutes with conjugation).**

$$\forall s\in \mathbb{C},\ \Lambda(\overline{s}) = \overline{\Lambda(s)}.$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/Symmetry/ZetaConjugationCovariance.completed_riemann_zeta_conj` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every complex parameter, mathlib's meromorphic completed Riemann zeta at the conjugate parameter equals the conjugate of its original value. The proof first transports conjugation through the real theta-kernel Mellin integral defining the pole-removed completion, then restores the explicit pole terms.

**Theorem 1.2 (Completed zeta has antiunitary covariance).**

$$\forall s\in \mathbb{C},\ \Lambda(1 - \overline{s}) = \overline{\Lambda(s)}.$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/Symmetry/ZetaConjugationCovariance.completed_riemann_zeta_one_sub_conj` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every complex parameter, completed zeta at one minus the conjugate parameter equals the conjugate of completed zeta at the original parameter. This composes the global conjugation theorem with mathlib's completed-zeta functional equation; no pole exclusions or analytic hypotheses are added.

**Theorem 1.3 (Riemann zeta commutes with conjugation).**

$$\forall s\in \mathbb{C},\ \zeta(\overline{s}) = \overline{\zeta(s)}.$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/Symmetry/ZetaConjugationCovariance.riemann_zeta_conj` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The conjugation covariance holds for every complex parameter, including mathlib's totalized value at zero. Away from zero the proof divides the completed covariance by the conjugation-compatible real Gamma factor; the zero case uses the exact value zeta of zero equals minus one-half.

**Theorem 1.4 (Xi reading commutes with conjugation).**

$$\forall s\in \mathbb{C},\ \xi(\overline{s}) = \overline{\xi(s)}.$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/Symmetry/ZetaConjugationCovariance.xi_reading_conj` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The repository's entire xi reading inherits global conjugation covariance from the pole-removed completed zeta function and its real polynomial prefactor.

**Theorem 1.5 (Xi reading has antiunitary covariance).**

$$\forall s\in \mathbb{C},\ \xi(1 - \overline{s}) = \overline{\xi(s)}.$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/Symmetry/ZetaConjugationCovariance.xi_reading_one_sub_conj` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The entire completed reading satisfies the same conjugate-reflection identity. The proof composes its newly proved conjugation covariance with the frozen xi reflection theorem.

## References

- Truth anchor: `D5/S3/Zeros/Symmetry/ZetaConjugationCovariance.completed_riemann_zeta_conj`
- Truth anchor: `D5/S3/Zeros/Symmetry/ZetaConjugationCovariance.completed_riemann_zeta_one_sub_conj`
- Truth anchor: `D5/S3/Zeros/Symmetry/ZetaConjugationCovariance.riemann_zeta_conj`
- Truth anchor: `D5/S3/Zeros/Symmetry/ZetaConjugationCovariance.xi_reading_conj`
- Truth anchor: `D5/S3/Zeros/Symmetry/ZetaConjugationCovariance.xi_reading_one_sub_conj`
- Dependency: [D5/S3/Zeros/CompletedZeta](../CompletedZeta.md)
