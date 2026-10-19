# Universal Ky Fan upper bound

## Abstract

The square-root upper-bound interface for zero-one matrices.

**Definition 1.1 (Universal upper-bound statement).**

Lean statement: `D5/S3/Combinatorics/Graph/KyFanGap/Upper.upperBoundStatement`

*Formalization.* `D5/S3/Combinatorics/Graph/KyFanGap/Upper.upperBoundStatement` (`✓ std3`).

*Citation.* Jon Crall, Claude Fable 5, Claude Opus 4.8, GPT-5.6 Thinking, and GPT-5.6 High (2026). *Formal rectangular singular-value variational bounds*. URL: <https://github.com/AIQ-Kitware/aiq-dkps-formalization/tree/64e234954217f3ca907ac980c8cbde2900109a66/ForTauCeti/Analysis/InnerProductSpace>.

*Commentary.*

The statement bounds the Ky Fan sum of every symmetric zero-one matrix by the square-root expression.

**Theorem 1.2 (Empty prefix).**

Lean statement: `D5/S3/Combinatorics/Graph/KyFanGap/Upper.kyFan_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/KyFanGap/Upper.kyFan_zero` (`✓ std3`). ∎

*Citation.* Jon Crall, Claude Fable 5, Claude Opus 4.8, GPT-5.6 Thinking, and GPT-5.6 High (2026). *Formal rectangular singular-value variational bounds*. URL: <https://github.com/AIQ-Kitware/aiq-dkps-formalization/tree/64e234954217f3ca907ac980c8cbde2900109a66/ForTauCeti/Analysis/InnerProductSpace>.

*Commentary.*

The empty Ky Fan prefix has value zero.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/KyFanGap/Upper.kyFan_zero`
- Truth anchor: `D5/S3/Combinatorics/Graph/KyFanGap/Upper.upperBoundStatement`
- Dependency: [D5/S3/Combinatorics/Graph/KyFanGap/SignedVariational](SignedVariational.md)
