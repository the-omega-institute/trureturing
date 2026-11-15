# ActualPsiTailEulerBridge

## Abstract

Actual psi Euler equation and moments

**Theorem 1.1 (Actual psi Euler equation and moments).**

Lean statement: `D5/S3/Weil/Mertens/ActualPsiTailEulerBridge.actual_tail_bridge`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/ActualPsiTailEulerBridge.actual_tail_bridge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual signed psi tail is L1 above log 2. For every U>=log 2, its actual transform is analytic on Re s>0, all polynomial moments converge and its first two derivatives are the actual moments. The Euler expression equals Phi(U,s) on Re s>0, using the current actual-tail calculus and the actual Qpsi=Mpsi germ. This supplies the original fixed-cutoff signed_peaks API directly, without an EulerTail compatibility structure.

## References

- Truth anchor: `D5/S3/Weil/Mertens/ActualPsiTailEulerBridge.actual_tail_bridge`
- Dependency: [D5/S3/Analytic/Laplace/ActivationTailEuler](../../Analytic/Laplace/ActivationTailEuler.md)
- Dependency: [D5/S3/Analytic/Laplace/EulerPoleObstruction](../../Analytic/Laplace/EulerPoleObstruction.md)
- Dependency: [D5/S3/Weil/Mertens/PsiLaplaceForcing](PsiLaplaceForcing.md)
