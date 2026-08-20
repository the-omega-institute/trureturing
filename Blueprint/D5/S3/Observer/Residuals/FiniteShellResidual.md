# Finite Shell Residual

## Abstract

A finite shell compression can vanish while its complementary defect remains nonzero.

**Theorem 1.1 (A finite shell check does not close the residual).**

$$\forall N: \mathbb{N},\ \operatorname{shellProjection}(N) \cdot \operatorname{defectOperator}(N) \cdot \operatorname{shellProjection}(N) = 0 \land\\\operatorname{residualProjection}(N) \cdot \operatorname{defectOperator}(N) \cdot \operatorname{residualProjection}(N) \neq 0 \land\\\neg (\operatorname{shellProjection}(N) \cdot \operatorname{defectOperator}(N) \cdot \operatorname{shellProjection}(N) = 0 \Rightarrow \operatorname{residualProjection}(N) \cdot \operatorname{defectOperator}(N) \cdot \operatorname{residualProjection}(N) = 0).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Residuals/FiniteShellResidual.finite_shell_check_does_not_close_residual` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite shell size, the constructed defect vanishes after compression to the listed coordinates while its compression to the complementary residual coordinate remains nonzero.

The two explicit compressions therefore witness that the finite-shell vanishing assertion alone does not imply residual vanishing.

## References

- Truth anchor: `D5/S3/Observer/Residuals/FiniteShellResidual.finite_shell_check_does_not_close_residual`
