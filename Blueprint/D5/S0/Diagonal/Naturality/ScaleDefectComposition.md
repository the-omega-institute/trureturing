# Diagonal Defect Across Three Scales

## Abstract

Coherent projections through an intermediate scale obey the Lipschitz diagonal-defect bound.

**Theorem 1.1 (Diagonal scale defects compose).**

$$\forall S: \operatorname{Type}, [\operatorname{Preorder}(S)],\ T, U: S \to \operatorname{Type},\ k, i, j: S, E: T_{j}, L: \operatorname{NNReal},\\{}[\operatorname{PseudoMetricSpace}(U_{i})], [\operatorname{PseudoMetricSpace}(U_{k})],\ k \leq i \leq j,\ P_{j,i}: T_{j} \to T_{i}, P_{i,k}: T_{i} \to T_{k}, P_{j,k}: T_{j} \to T_{k},\ Q_{j,i}: U_{j} \to U_{i}, Q_{i,k}: U_{i} \to U_{k}, Q_{j,k}: U_{j} \to U_{k},\ Delta_{j}: T_{j} \to U_{j}, Delta_{i}: T_{i} \to U_{i}, Delta_{k}: T_{k} \to U_{k},\ P_{j,k} = P_{i,k} \circ P_{j,i} \land Q_{j,k} = Q_{i,k} \circ Q_{j,i} \land \operatorname{LipschitzWith}\left(L, Q_{i,k}\right) \Rightarrow\\\operatorname{naturalityDefect}\left(P_{j,k}, Q_{j,k}, Delta_{j}, Delta_{k}, E\right) \leq L \cdot \operatorname{naturalityDefect}\left(P_{j,i}, Q_{j,i}, Delta_{j}, Delta_{i}, E\right) +\\\operatorname{naturalityDefect}\left(P_{i,k}, Q_{i,k}, Delta_{i}, Delta_{k}, P_{j,i}(E)\right).$$

*Proof.* Machine-checked in Lean as `D5/S0/Diagonal/Naturality/ScaleDefectComposition.diagonal_scale_defect_comp_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let k <= i <= j be three scales. Each scale has a table carrier T_s, an output carrier U_s, and a diagonal map Delta_s. The table projections P and output projections Q are typed separately.

The direct projections are publicly required to equal the composites P_(i,k) after P_(j,i) and Q_(i,k) after Q_(j,i). Output carriers at i and k carry the pseudometrics used by the three defects.

If Q_(i,k) is L-Lipschitz, insert Q_(i,k) Delta_i P_(j,i)(E) between the endpoints. The metric triangle inequality and the Lipschitz distance bound give L times the j-to-i defect plus the i-to-k defect at P_(j,i)(E).

The pointwise defect is imported from the frozen diagonal-naturality family and is exactly dist(Q Delta(E), Delta(P(E))). Pinned Mathlib supplies dist_triangle and LipschitzWith.dist_le_mul.

## References

- Truth anchor: `D5/S0/Diagonal/Naturality/ScaleDefectComposition.diagonal_scale_defect_comp_le`
- Dependency: [D5/S0/Diagonal/Naturality/NaturalityDefectComposition](NaturalityDefectComposition.md)
