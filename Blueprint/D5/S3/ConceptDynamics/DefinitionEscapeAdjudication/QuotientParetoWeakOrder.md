# Decidable Weak Pareto Order on the Finite Quotient

## Abstract

Existential weak Pareto dominance on explicit finite classes is representative-independent, decidable by a finite scan, and a partial order.

**Definition 1.1 (Existential representative relation).**

$$\begin{gathered}\forall Action, Information, Residual, Transfer, Cost, Risk: \operatorname{Type},\\{}[\operatorname{DecidableEq}\left(Action\right)], [\operatorname{LE}\left(Information\right)], [\operatorname{LE}\left(Residual\right)], [\operatorname{LE}\left(Transfer\right)], [\operatorname{LE}\left(Cost\right)], [\operatorname{LE}\left(Risk\right)],\\{}[\forall a, b: Information, \operatorname{Decidable}\left(a \leq b\right)], [\forall a, b: Residual, \operatorname{Decidable}\left(a \leq b\right)], [\forall a, b: Transfer, \operatorname{Decidable}\left(a \leq b\right)],\\{}[\forall a, b: Cost, \operatorname{Decidable}\left(a \leq b\right)], [\forall a, b: Risk, \operatorname{Decidable}\left(a \leq b\right)],\\{}value: Action \to \operatorname{GainVector}\left(Information, Residual, Transfer, Cost, Risk\right), F: \operatorname{Finset}\left(Action\right),\\{}C, D: \operatorname{FiniteParetoQuotient}\left(value, F\right),\\{}\operatorname{QuotientParetoWeak}\left(value, F, C, D\right) \iff \exists x: \operatorname{ParetoCarrier}\left(F\right), x \in \operatorname{val}\left(C\right) \land \exists y: \operatorname{ParetoCarrier}\left(F\right), y \in \operatorname{val}\left(D\right) \land \operatorname{ParetoWeakOn}\left(value, F, x, y\right).\end{gathered}$$

*Formalization.* `D5/S3/ConceptDynamics/DefinitionEscapeAdjudication/QuotientParetoWeakOrder.QuotientParetoWeak` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A class weakly dominates another when one representative pair satisfies the existing carrier-level ParetoWeakOn relation.

**Definition 1.2 (Finite product scan).**

$$\begin{gathered}\forall Action, Information, Residual, Transfer, Cost, Risk: \operatorname{Type},\\{}[\operatorname{DecidableEq}\left(Action\right)], [\operatorname{LE}\left(Information\right)], [\operatorname{LE}\left(Residual\right)], [\operatorname{LE}\left(Transfer\right)], [\operatorname{LE}\left(Cost\right)], [\operatorname{LE}\left(Risk\right)],\\{}[\forall a, b: Information, \operatorname{Decidable}\left(a \leq b\right)], [\forall a, b: Residual, \operatorname{Decidable}\left(a \leq b\right)], [\forall a, b: Transfer, \operatorname{Decidable}\left(a \leq b\right)],\\{}[\forall a, b: Cost, \operatorname{Decidable}\left(a \leq b\right)], [\forall a, b: Risk, \operatorname{Decidable}\left(a \leq b\right)],\\{}value: Action \to \operatorname{GainVector}\left(Information, Residual, Transfer, Cost, Risk\right), F: \operatorname{Finset}\left(Action\right),\\{}C, D: \operatorname{FiniteParetoQuotient}\left(value, F\right),\\{}\operatorname{quotientParetoWeakScan}\left(value, F, C, D\right) = \operatorname{decide}\left(\operatorname{Nonempty}\left(\operatorname{filter}\left(\operatorname{product}\left(\operatorname{val}\left(C\right), \operatorname{val}\left(D\right)\right), \lambda p, \operatorname{ParetoWeakOn}\left(value, F, \operatorname{fst}\left(p\right), \operatorname{snd}\left(p\right)\right)\right)\right)\right).\end{gathered}$$

*Formalization.* `D5/S3/ConceptDynamics/DefinitionEscapeAdjudication/QuotientParetoWeakOrder.quotientParetoWeakScan` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The decision procedure forms the finite product of the two explicit classes, filters it by ParetoWeakOn, and decides nonemptiness.

**Definition 1.3 (Finite-scan decidability).**

$$\begin{gathered}\forall Action, Information, Residual, Transfer, Cost, Risk: \operatorname{Type},\\{}[\operatorname{DecidableEq}\left(Action\right)], [\operatorname{Preorder}\left(Information\right)], [\operatorname{Preorder}\left(Residual\right)], [\operatorname{Preorder}\left(Transfer\right)], [\operatorname{Preorder}\left(Cost\right)], [\operatorname{Preorder}\left(Risk\right)],\\{}[\forall a, b: Information, \operatorname{Decidable}\left(a \leq b\right)], [\forall a, b: Residual, \operatorname{Decidable}\left(a \leq b\right)], [\forall a, b: Transfer, \operatorname{Decidable}\left(a \leq b\right)],\\{}[\forall a, b: Cost, \operatorname{Decidable}\left(a \leq b\right)], [\forall a, b: Risk, \operatorname{Decidable}\left(a \leq b\right)],\\{}value: Action \to \operatorname{GainVector}\left(Information, Residual, Transfer, Cost, Risk\right), F: \operatorname{Finset}\left(Action\right),\\{}C, D: \operatorname{FiniteParetoQuotient}\left(value, F\right),\\{}\operatorname{quotientParetoWeakDecidable}\left(value, F, C, D\right): \operatorname{Decidable}\left(\operatorname{QuotientParetoWeak}\left(value, F, C, D\right)\right).\end{gathered}$$

*Formalization.* `D5/S3/ConceptDynamics/DefinitionEscapeAdjudication/QuotientParetoWeakOrder.quotientParetoWeakDecidable` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Correctness of the product scan supplies a Decidable term for the quotient relation.

**Theorem 1.4 (Representative-independent decidable partial order).**

$$\begin{gathered}\forall Action, Information, Residual, Transfer, Cost, Risk: \operatorname{Type},\\{}[\operatorname{DecidableEq}\left(Action\right)], [\operatorname{Preorder}\left(Information\right)], [\operatorname{Preorder}\left(Residual\right)], [\operatorname{Preorder}\left(Transfer\right)], [\operatorname{Preorder}\left(Cost\right)], [\operatorname{Preorder}\left(Risk\right)],\\{}[\forall a, b: Information, \operatorname{Decidable}\left(a \leq b\right)], [\forall a, b: Residual, \operatorname{Decidable}\left(a \leq b\right)], [\forall a, b: Transfer, \operatorname{Decidable}\left(a \leq b\right)],\\{}[\forall a, b: Cost, \operatorname{Decidable}\left(a \leq b\right)], [\forall a, b: Risk, \operatorname{Decidable}\left(a \leq b\right)],\\{}value: Action \to \operatorname{GainVector}\left(Information, Residual, Transfer, Cost, Risk\right), F: \operatorname{Finset}\left(Action\right),\\{}(\forall C, D: \operatorname{FiniteParetoQuotient}\left(value, F\right), \operatorname{QuotientParetoWeak}\left(value, F, C, D\right) \iff \forall x: \operatorname{ParetoCarrier}\left(F\right), x \in \operatorname{val}\left(C\right) \Rightarrow \forall y: \operatorname{ParetoCarrier}\left(F\right), y \in \operatorname{val}\left(D\right) \Rightarrow \operatorname{ParetoWeakOn}\left(value, F, x, y\right)) \land\\{}(\forall C, D: \operatorname{FiniteParetoQuotient}\left(value, F\right), \operatorname{quotientParetoWeakScan}\left(value, F, C, D\right) = true \iff \operatorname{QuotientParetoWeak}\left(value, F, C, D\right)) \land\\{}(\forall C, D: \operatorname{FiniteParetoQuotient}\left(value, F\right), \operatorname{Nonempty}\left(\operatorname{Decidable}\left(\operatorname{QuotientParetoWeak}\left(value, F, C, D\right)\right)\right)) \land\\{}(\forall C: \operatorname{FiniteParetoQuotient}\left(value, F\right), \operatorname{QuotientParetoWeak}\left(value, F, C, C\right)) \land\\{}(\forall C, D, E: \operatorname{FiniteParetoQuotient}\left(value, F\right), \operatorname{QuotientParetoWeak}\left(value, F, C, D\right) \Rightarrow \operatorname{QuotientParetoWeak}\left(value, F, D, E\right) \Rightarrow \operatorname{QuotientParetoWeak}\left(value, F, C, E\right)) \land\\{}(\forall C, D: \operatorname{FiniteParetoQuotient}\left(value, F\right), \operatorname{QuotientParetoWeak}\left(value, F, C, D\right) \Rightarrow \operatorname{QuotientParetoWeak}\left(value, F, D, C\right) \Rightarrow C = D) \land\\{}(F = \emptyset \Rightarrow \forall C, D: \operatorname{FiniteParetoQuotient}\left(value, F\right), \operatorname{QuotientParetoWeak}\left(value, F, C, D\right)).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/DefinitionEscapeAdjudication/QuotientParetoWeakOrder.quotient_pareto_weak_finite_decidable_partial_order` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

One dominating representative pair implies that every pair dominates: members of one explicit class are related by the symmetric Pareto kernel, so the frozen weak-preorder laws transport the comparison between representatives.

The same transport proves transitivity and antisymmetry. Reflexivity uses the proved nonemptiness of every quotient class. If the action carrier is empty, the quotient has no element and the quantified relation statement is vacuous; no artificial element is introduced.

## References

- Truth anchor: `D5/S3/ConceptDynamics/DefinitionEscapeAdjudication/QuotientParetoWeakOrder.QuotientParetoWeak`
- Truth anchor: `D5/S3/ConceptDynamics/DefinitionEscapeAdjudication/QuotientParetoWeakOrder.quotientParetoWeakDecidable`
- Truth anchor: `D5/S3/ConceptDynamics/DefinitionEscapeAdjudication/QuotientParetoWeakOrder.quotientParetoWeakScan`
- Truth anchor: `D5/S3/ConceptDynamics/DefinitionEscapeAdjudication/QuotientParetoWeakOrder.quotient_pareto_weak_finite_decidable_partial_order`
- Dependency: [D5/S3/ConceptDynamics/DefinitionEscapeAdjudication/FiniteParetoQuotient](FiniteParetoQuotient.md)
