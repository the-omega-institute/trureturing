# Budget and First-Gap Geometry of Green Classes

## Abstract

Uniform Green-class volume depends only on budget, while exact drift depends on the first gap.

**Theorem 1.1 (Budget controls volume while the first hole controls drift).**

$$\begin{gathered}\forall O: \operatorname{Type},\\{}\operatorname{Fintype}(O) \land \operatorname{Nonempty}(O) \land \operatorname{MeasurableSpace}(O) \land \operatorname{MeasurableSingletonClass}(O) \land\\{}\operatorname{TopologicalSpace}(O) \land \operatorname{DiscreteTopology}(O) \land \operatorname{Nontrivial}(O) \Rightarrow\\{}\forall S: \operatorname{Finset}(\mathbb{N}), t: \mathbb{N} \to O,\\{}\operatorname{stringMeasure}(O, G(S, t)) = (\operatorname{card}(O)^{-1})^{\operatorname{card}(S)} \land\\{}(\forall U: \operatorname{Finset}(\mathbb{N}), \operatorname{card}(U) = \operatorname{card}(S) \Rightarrow \operatorname{stringMeasure}(O, G(U, t)) = \operatorname{stringMeasure}(O, G(S, t))) \land\\{}\operatorname{diam}(G(S, t)) = \frac{1}{2}^{\operatorname{firstHole}(S)} \land\\{}(\frac{1}{2}^{\operatorname{card}(S)} \le \operatorname{diam}(G(S, t)) \land (\operatorname{diam}(G(S, t)) = \frac{1}{2}^{\operatorname{card}(S)} \iff S = \operatorname{range}(\operatorname{card}(S)))).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S0/Asymptotics/MetricGeometry/GreenClassBudgetGeometry.green_class_budget_geometry` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let O be a finite nonempty nontrivial alphabet carrying the measurable discrete structure used by the uniform product law and the PiNat prefix metric. For a finite support S and target t, the Green class G(S,t) consists of all infinite strings agreeing with t on S.

Its uniform product measure is (card O)^(-1) raised to card S. Hence replacing S by any support U of the same cardinality leaves the volume unchanged: the regression budget sees how many coordinates were tested, not where they lie.

Its prefix-metric diameter is exactly (1/2)^firstHole(S), so the least untested coordinate fixes the full drift radius regardless of tests placed later. At fixed budget, (1/2)^card(S) is the smallest possible diameter, and equality holds exactly when S is the gapless prefix range(card(S)).

The proof applies the frozen canonical Green-class measure, exact-diameter, and prefix-extremality theorems. It introduces no replacement Green class, measure, metric, or first-hole definition.

## References

- Truth anchor: `D5/S0/Asymptotics/MetricGeometry/GreenClassBudgetGeometry.green_class_budget_geometry`
- Dependency: [D5/S0/Asymptotics/MetricGeometry/GreenClassDiameter](GreenClassDiameter.md)
