# Golden Modular Standard Pair

## Abstract

The golden modular step squares to a positive definite unimodular operator with reciprocal golden scales.

**Theorem 1.1 (The golden first phase forms a finite-dimensional standard pair).**

$$\begin{aligned}let F: \operatorname{Matrix}(\operatorname{Fin}(2), \operatorname{Fin}(2), \mathbb{R}) = \operatorname{matrix2}(0, 1, 1, 1);\\let Delta_{\phi}: \operatorname{Matrix}(\operatorname{Fin}(2), \operatorname{Fin}(2), \mathbb{R}) = F^{2};\\F^{2} = \operatorname{matrix2}(1, 1, 1, 2) \land\\\operatorname{det}(Delta_{\phi}) = 1 \land \operatorname{trace}(Delta_{\phi}) = 3 \land\\\operatorname{PosDef}(Delta_{\phi}) \land \operatorname{quadraticValue}(Delta_{\phi}, \operatorname{vector2}(1, 0)) = 1 \land\\\operatorname{quadraticValue}(Delta_{\phi}, \operatorname{vector2}(1, -1)) = 1 \land\\\varphi^{2} \cdot \operatorname{inv}(\varphi^{2}) = 1 \land\\\varphi^{2} + \operatorname{inv}(\varphi^{2}) = 3.\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/GoldenCoding/GoldenModularStandardPair.golden_modular_standard_pair` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The one-step matrix F has rows (0,1) and (1,1). Direct finite matrix multiplication identifies its square Delta_phi with the matrix having rows (1,1) and (1,2).

The squared operator has determinant one and trace three. Its quadratic form is (x_0+x_1)^2+x_1^2, so every nonzero real vector has strictly positive value.

The vectors (1,0) and (1,-1) both give quadratic-form value one. The squared golden ratio and its reciprocal square likewise have product one and sum three.

## References

- Truth anchor: `D5/S3/Observer/GoldenCoding/GoldenModularStandardPair.golden_modular_standard_pair`
