# Rare-Branch Conditional Error Sharpness

## Abstract

An arbitrarily small initial state error can reach maximal error after conditioning on a rare branch.

**Theorem 1.1 (A rare branch reaches maximal conditional error).**

$$\left(\forall epsilon \in \mathbb{R},\; \left(0 < epsilon \land epsilon < 1\right) \Rightarrow \left(\exists rho \in \operatorname{DensityState}(\operatorname{Fin}(3)),\; \exists sigma \in \operatorname{DensityState}(\operatorname{Fin}(3)),\; \exists P \in \operatorname{Matrix}(\operatorname{Fin}(3), \operatorname{Fin}(3), \mathbb{C}),\; \exists K \in \operatorname{Matrix}(\operatorname{Fin}(3), \operatorname{Fin}(3), \mathbb{C}),\; \operatorname{matrix}(rho) = \operatorname{diag}(1-epsilon, epsilon, 0) \land \left(\operatorname{matrix}(sigma) = \operatorname{diag}(1-epsilon, 0, epsilon) \land \left(P = \operatorname{diag}(0, 1, 0) + \operatorname{diag}(0, 0, 1) \land \left(K = \operatorname{diag}(1, 0, 0) \land \left({P}^{*} \cdot P + {K}^{*} \cdot K = 1 \land \left({P}^{*} \cdot P \le 1 \land \left(\operatorname{traceDistance}(rho, sigma) = epsilon \land \left(\operatorname{ReTr}(\operatorname{matrix}(rho) \cdot {P}^{*} \cdot P) = epsilon \land \left(\operatorname{ReTr}(\operatorname{matrix}(sigma) \cdot {P}^{*} \cdot P) = epsilon \land \left(1 / epsilon \cdot P \cdot \operatorname{matrix}(rho) \cdot {P}^{*} = \operatorname{diag}(0, 1, 0) \land \left(1 / epsilon \cdot P \cdot \operatorname{matrix}(sigma) \cdot {P}^{*} = \operatorname{diag}(0, 0, 1) \land \left(\operatorname{traceNorm}((\operatorname{diag}(0, 1, 0) - \operatorname{diag}(0, 0, 1))) / 2 = 1 \land \left(P = \operatorname{diag}(0, 1, 0) + \operatorname{diag}(0, 0, 1) \land \operatorname{max}(epsilon, epsilon) \cdot \operatorname{traceNorm}((1 / epsilon \cdot P \cdot rho \cdot {P}^{*} - 1 / epsilon \cdot P \cdot sigma \cdot {P}^{*})) / 2 = \operatorname{traceDistance}(rho, sigma)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right) \land \left(\neg \left(\exists f \in (\mathbb{R}) \to \mathbb{R},\; \operatorname{Tendsto}(f, \operatorname{nhdsGT}(0), \operatorname{nhds}(0)) \land \left(\forall rho \in \operatorname{DensityState}(\operatorname{Fin}(3)),\; \forall sigma \in \operatorname{DensityState}(\operatorname{Fin}(3)),\; \forall P \in \operatorname{Matrix}(\operatorname{Fin}(3), \operatorname{Fin}(3), \mathbb{C}),\; \left({P}^{*} \cdot P \le 1 \land \left(0 < \operatorname{ReTr}(\operatorname{matrix}(rho) \cdot {P}^{*} \cdot P) \land 0 < \operatorname{ReTr}(\operatorname{matrix}(sigma) \cdot {P}^{*} \cdot P)\right)\right) \Rightarrow \operatorname{traceNorm}((1 / \operatorname{ReTr}(\operatorname{matrix}(rho) \cdot {P}^{*} \cdot P) \cdot P \cdot \operatorname{matrix}(rho) \cdot {P}^{*} - 1 / \operatorname{ReTr}(\operatorname{matrix}(sigma) \cdot {P}^{*} \cdot P) \cdot P \cdot \operatorname{matrix}(sigma) \cdot {P}^{*})) / 2 \le \operatorname{f}(\operatorname{traceDistance}(rho, sigma))\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/RareBranchConditionalErrorSharpness.rare_branch_conditional_error_sharpness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive epsilon below one, the displayed diagonal density states have trace distance epsilon while the same single-Kraus branch has equal probability epsilon on both states.

After normalization, the two branch outputs are orthogonal rank-one projectors, so their trace distance is one and the weighted sharpness identity is attained.

The construction also rules out any uniform conditional-error bound whose value tends to zero with the initial trace distance.

## References

- Truth anchor: `D5/S3/Quantum/Measurement/RareBranchConditionalErrorSharpness.rare_branch_conditional_error_sharpness`
- Dependency: [D5/S3/Quantum/Measurement/BranchConditionedTraceDistance](BranchConditionedTraceDistance.md)
