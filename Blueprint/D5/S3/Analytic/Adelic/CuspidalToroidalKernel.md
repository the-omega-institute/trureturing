# Cuspidal Toroidal Kernel

## Abstract

All normalized cuspidal quadratic-torus periods vanish exactly when the base central value vanishes.

**Theorem 1.1 (Cuspidal all-torus kernel equals the central-value kernel).**

$$\forall Index \in \operatorname{Type}\left(\right), P \in Index \to \operatorname{Complex}\left(\right), C \in Index \to \operatorname{Real}\left(\right), Ltwist \in Index \to \operatorname{Real}\left(\right), Lcenter \in \operatorname{Real}\left(\right), Ladjoint \in \operatorname{Real}\left(\right),\; \left(\left(\forall i \in Index,\; \operatorname{normSq}\left(P\left(i\right)\right) = \frac{C\left(i\right) \times (Lcenter \times Ltwist\left(i\right))}{Ladjoint}\right) \land \left(Ladjoint \ne 0 \land \left(\exists i \in Index,\; C\left(i\right) \ne 0 \land Ltwist\left(i\right) \ne 0\right)\right)\right) \Rightarrow \left(\left(\forall i \in Index,\; P\left(i\right) = 0\right) \Leftrightarrow Lcenter = 0\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Adelic/CuspidalToroidalKernel.cuspidal_all_torus_kernel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The normalized period, local factor, base central value, twisted central value, and adjoint denominator are exposed directly. Their norm-square relation is the displayed source identity.

A zero base central value forces every period norm square to vanish. Conversely, the nonzero denominator and one nonzero local and twisted witness let cancellation recover the base value.

Thus universal invisibility across the indexed quadratic-torus family is precisely the zero locus of the base central value.

## References

- Truth anchor: `D5/S3/Analytic/Adelic/CuspidalToroidalKernel.cuspidal_all_torus_kernel`
