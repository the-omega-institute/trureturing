# FillmanLimPositiveSemigroup

## Abstract

A hyperbolic relative matrix forces a hyperbolic positive product.

**Theorem 1.1 (Hyperbolicity in a positive semigroup).**

$$\forall A: Matrix\left(Fin\left(2\right), Fin\left(2\right), Real\right), \forall B: Matrix\left(Fin\left(2\right), Fin\left(2\right), Real\right), (\operatorname{Matrix}.\operatorname{det}\left(A\right) = (1)) \Rightarrow ((\operatorname{Matrix}.\operatorname{det}\left(B\right) = (1)) \Rightarrow ((2 < \lvert \operatorname{Matrix}.\operatorname{trace}\left((A) * (\operatorname{Matrix}.\operatorname{adjugate}\left(B\right))\right) \rvert) \Rightarrow (\exists C: Matrix\left(Fin\left(2\right), Fin\left(2\right), Real\right), (C \in \operatorname{Submonoid}.\operatorname{closure}\left(\left\{A, B\right\}\right)) \land (2 < \lvert \operatorname{Matrix}.\operatorname{trace}\left(C\right) \rvert))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Spectral/FillmanLimPositiveSemigroup.positiveRelativeCriterion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jake Fillman and Yi-Sheng Lim (2026). *On the identification of certain classes of gap-rich sets*. DOI: [10.48550/arXiv.2609.21029](https://doi.org/10.48550/arXiv.2609.21029). URL: <https://arxiv.org/abs/2609.21029v1>.

*Commentary.*

Two determinant-one real matrices with hyperbolic relative product generate a hyperbolic positive product. Elliptic powers approach the adjugate; trace-two generators have affine power traces, which handle both signs at the parabolic boundary.

**Theorem 1.2 (Positive powers remain hyperbolic).**

$$\forall A: Matrix\left(Fin\left(2\right), Fin\left(2\right), Real\right), (\operatorname{Matrix}.\operatorname{det}\left(A\right) = (1)) \Rightarrow ((2 < \lvert \operatorname{Matrix}.\operatorname{trace}\left(A\right) \rvert) \Rightarrow (\forall n: Nat, (0 < n) \Rightarrow (2 < \lvert \operatorname{Matrix}.\operatorname{trace}\left((A)^{n}\right) \rvert)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Spectral/FillmanLimPositiveSemigroup.hyperbolicTracePower` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jake Fillman and Yi-Sheng Lim (2026). *On the identification of certain classes of gap-rich sets*. DOI: [10.48550/arXiv.2609.21029](https://doi.org/10.48550/arXiv.2609.21029). URL: <https://arxiv.org/abs/2609.21029v1>.

*Commentary.*

For determinant-one real two by two matrices, absolute trace greater than two persists under every positive integer power. The trace recurrence gives monotone growth after choosing the trace sign.

## References

- Truth anchor: `D5/S3/Analytic/Spectral/FillmanLimPositiveSemigroup.hyperbolicTracePower`
- Truth anchor: `D5/S3/Analytic/Spectral/FillmanLimPositiveSemigroup.positiveRelativeCriterion`
- Dependency: [D5/S0/Observation/MatrixTracePowerSum](../../../S0/Observation/MatrixTracePowerSum.md)
