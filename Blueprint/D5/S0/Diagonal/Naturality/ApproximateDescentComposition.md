# Approximate Descent Composition

## Abstract

Uniform pseudometric errors of approximate descents obey the Lipschitz composition budget.

**Definition 1.1 (Uniform naturality defect).**

$$\forall A, Am, B, Bm: \operatorname{Type},\\{}[\operatorname{PseudoMetricSpace}(Bm)], \forall projectA: A \to Am, projectB: B \to Bm,\\{}globalMap: A \to B, localMap: Am \to Bm,\\{}\operatorname{uniformNaturalityDefect}\left(projectA, projectB, globalMap, localMap\right) = \operatorname{supremum}\left(x, \operatorname{naturalityDefect}\left(projectA, projectB, globalMap, localMap, x\right)\right).$$

*Formalization.* `D5/S0/Diagonal/Naturality/ApproximateDescentComposition.uniformNaturalityDefect` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The global defect is constructed from the source interface as the supremum, over source states, of the imported pointwise pseudometric defect.

**Theorem 1.2 (Approximate descent composition bound).**

$$\forall X, Xbar, Y, Ybar, Z, Zbar: \operatorname{Type},\\{}[\operatorname{PseudoMetricSpace}(Ybar)], [\operatorname{PseudoMetricSpace}(Zbar)],\\{}projectX: X \to Xbar, projectY: Y \to Ybar, projectZ: Z \to Zbar,\\{}globalF: X \to Y, localF: Xbar \to Ybar, globalG: Y \to Z, localG: Ybar \to Zbar,\\{}epsilonF, epsilonG: Real, L: NNReal,\\{}\operatorname{Nonempty}\left(X\right) \land {\forall x, \operatorname{naturalityDefect}\left(projectX, projectY, globalF, localF, x\right) \leq epsilonF} \land {\forall y, \operatorname{naturalityDefect}\left(projectY, projectZ, globalG, localG, y\right) \leq epsilonG} \land \operatorname{LipschitzWith}\left(L, localG\right) \Rightarrow \operatorname{uniformNaturalityDefect}\left(projectX, projectZ, globalG \circ globalF, localG \circ localF\right) \leq epsilonG + L \cdot epsilonF.$$

*Proof.* Machine-checked in Lean as `D5/S0/Diagonal/Naturality/ApproximateDescentComposition.approximate_descent_comp_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The maps F and G have local approximations with public pointwise bounds epsilonF and epsilonG. The outer local approximation is L-Lipschitz.

The global defect of the composite is at most epsilonG plus L times epsilonF. The proof directly applies the frozen pointwise composition theorem and then takes the supremum.

Repository search found the exact pointwise theorem but no existing uniform supremum statement. The imported theorem already applies the pinned metric triangle and Lipschitz distance declarations.

## References

- Truth anchor: `D5/S0/Diagonal/Naturality/ApproximateDescentComposition.approximate_descent_comp_bound`
- Truth anchor: `D5/S0/Diagonal/Naturality/ApproximateDescentComposition.uniformNaturalityDefect`
- Dependency: [D5/S0/Diagonal/Naturality/NaturalityDefectComposition](NaturalityDefectComposition.md)
