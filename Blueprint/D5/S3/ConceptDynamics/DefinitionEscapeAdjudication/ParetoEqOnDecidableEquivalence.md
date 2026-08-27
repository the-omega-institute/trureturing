# Decidable Symmetric Pareto Kernel

## Abstract

The symmetric kernel of weak Pareto dominance on a finite action carrier is a decidable equivalence relation.

**Definition 1.1 (Five coordinate decisions decide the symmetric kernel).**

$$\begin{gathered}\forall Action, Information, Residual, Transfer, Cost, Risk: \operatorname{Type},\\{}[\operatorname{DecidableEq}\left(Action\right)], [\operatorname{LE}\left(Information\right)], [\operatorname{LE}\left(Residual\right)], [\operatorname{LE}\left(Transfer\right)], [\operatorname{LE}\left(Cost\right)], [\operatorname{LE}\left(Risk\right)],\\{}[\forall a, b: Information, \operatorname{Decidable}\left(a \leq b\right)], [\forall a, b: Residual, \operatorname{Decidable}\left(a \leq b\right)], [\forall a, b: Transfer, \operatorname{Decidable}\left(a \leq b\right)],\\{}[\forall a, b: Cost, \operatorname{Decidable}\left(a \leq b\right)], [\forall a, b: Risk, \operatorname{Decidable}\left(a \leq b\right)],\\{}value: Action \to \operatorname{GainVector}\left(Information, Residual, Transfer, Cost, Risk\right), F: \operatorname{Finset}\left(Action\right),\\{}x, y: \operatorname{ParetoCarrier}\left(F\right),\\{}\operatorname{Decidable}\left(\operatorname{ParetoEqOn}\left(value, F, x, y\right)\right).\end{gathered}$$

*Formalization.* `D5/S3/ConceptDynamics/DefinitionEscapeAdjudication/ParetoEqOnDecidableEquivalence.paretoEqOnDecidable` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The decision procedure unfolds both weak-dominance directions and combines the ten resulting coordinate comparisons. It requires no enumeration of the ambient action or coordinate types.

**Theorem 1.2 (The symmetric Pareto kernel obeys the three equivalence laws).**

$$\begin{gathered}\forall Action, Information, Residual, Transfer, Cost, Risk: \operatorname{Type},\\{}[\operatorname{DecidableEq}\left(Action\right)], [\operatorname{Preorder}\left(Information\right)], [\operatorname{Preorder}\left(Residual\right)], [\operatorname{Preorder}\left(Transfer\right)], [\operatorname{Preorder}\left(Cost\right)], [\operatorname{Preorder}\left(Risk\right)],\\{}value: Action \to \operatorname{GainVector}\left(Information, Residual, Transfer, Cost, Risk\right), F: \operatorname{Finset}\left(Action\right),\\{}(\forall x: \operatorname{ParetoCarrier}\left(F\right), \operatorname{ParetoEqOn}\left(value, F, x, x\right)) \land\\{}(\forall x, y: \operatorname{ParetoCarrier}\left(F\right), \operatorname{ParetoEqOn}\left(value, F, x, y\right) \Rightarrow \operatorname{ParetoEqOn}\left(value, F, y, x\right)) \land\\{}(\forall x, y, z: \operatorname{ParetoCarrier}\left(F\right), \operatorname{ParetoEqOn}\left(value, F, x, y\right) \Rightarrow \operatorname{ParetoEqOn}\left(value, F, y, z\right) \Rightarrow \operatorname{ParetoEqOn}\left(value, F, x, z\right)).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/DefinitionEscapeAdjudication/ParetoEqOnDecidableEquivalence.pareto_eq_on_equivalence_laws` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The carrier is the subtype selected by the finite action set. ParetoEqOn is defined as weak dominance in both directions; it is not defined by vector equality or an external label.

Reflexivity and transitivity reuse the frozen five-coordinate weak Pareto preorder theorem. Symmetry swaps the two kernel conjuncts; the preceding definition supplies the independent decision clause.

## References

- Truth anchor: `D5/S3/ConceptDynamics/DefinitionEscapeAdjudication/ParetoEqOnDecidableEquivalence.paretoEqOnDecidable`
- Truth anchor: `D5/S3/ConceptDynamics/DefinitionEscapeAdjudication/ParetoEqOnDecidableEquivalence.pareto_eq_on_equivalence_laws`
- Dependency: [D5/S3/ConceptDynamics/DefinitionEscapeAdjudication/ParetoWeakPreorder](ParetoWeakPreorder.md)
