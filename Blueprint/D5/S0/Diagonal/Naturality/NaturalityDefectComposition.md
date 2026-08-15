# Naturality Defect Under Composition

## Abstract

Pointwise naturality defects satisfy a Lipschitz composition bound.

**Definition 1.1 (Pointwise naturality defect).**

$$\forall A, Am, B, Bm: \operatorname{Type},\ [\operatorname{PseudoMetricSpace}(Bm)],\ \forall projectA: A \to Am, projectB: B \to Bm,\ globalMap: A \to B, localMap: Am \to Bm, x: A,\ \operatorname{naturalityDefect}\left(projectA, projectB, globalMap, localMap, x\right) = \operatorname{dist}\left(\operatorname{projectB}\left(\operatorname{globalMap}\left(x\right)\right), \operatorname{localMap}\left(\operatorname{projectA}\left(x\right)\right)\right).$$

*Formalization.* `D5/S0/Diagonal/Naturality/NaturalityDefectComposition.naturalityDefect` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a global map from A to B, projections from A to Am and from B to Bm, and a local map from Am to Bm, the pointwise naturality defect at x is the distance between projecting the global output and applying the local map to the projected input.

**Theorem 1.2 (Naturality defect obeys the composition bound).**

$$\forall A, Am, B, Bm, C, Cm: \operatorname{Type},\ [\operatorname{PseudoMetricSpace}(Bm)], [\operatorname{PseudoMetricSpace}(Cm)],\ \forall projectA: A \to Am, projectB: B \to Bm, projectC: C \to Cm,\ globalF: B \to C, localF: Bm \to Cm, globalG: A \to B, localG: Am \to Bm,\ K: \operatorname{NNReal}, x: A,\ \operatorname{LipschitzWith}\left(K, localF\right) \Rightarrow \operatorname{naturalityDefect}\left(projectA, projectC, globalF \circ globalG, localF \circ localG, x\right) \leq \operatorname{naturalityDefect}\left(projectB, projectC, globalF, localF, \operatorname{globalG}\left(x\right)\right) + K \cdot \operatorname{naturalityDefect}\left(projectA, projectB, globalG, localG, x\right).$$

*Proof.* Machine-checked in Lean as `D5/S0/Diagonal/Naturality/NaturalityDefectComposition.naturality_defect_comp_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let globalF and globalG be composable global maps, and let localF and localG be their composable local approximations. The local approximation of the composite is localF after localG.

If localF is K-Lipschitz, then at every x the defect of globalF after globalG is at most the defect of globalF at globalG(x), plus K times the defect of globalG at x. The proof inserts localF of projectB(globalG(x)), applies the metric triangle inequality, and then applies the imported Lipschitz distance bound.

Loogle found dist_triangle and LipschitzWith.dist_le_mul as exact supporting declarations, and the Lean proof imports and applies both. Full-statement pinned-library and repository searches found no duplicate with this typed composition shape.

## References

- Truth anchor: `D5/S0/Diagonal/Naturality/NaturalityDefectComposition.naturalityDefect`
- Truth anchor: `D5/S0/Diagonal/Naturality/NaturalityDefectComposition.naturality_defect_comp_le`
