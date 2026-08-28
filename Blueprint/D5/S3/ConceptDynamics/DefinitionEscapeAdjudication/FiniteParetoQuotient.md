# Explicit Finite Pareto Quotient

## Abstract

The symmetric weak-Pareto kernel on a finite carrier has explicit finite classes, a complete class enumeration, and the required empty and singleton laws.

**Definition 1.1 (Explicit symmetric-kernel class).**

$$\begin{gathered}\forall Action, Information, Residual, Transfer, Cost, Risk: \operatorname{Type},\\{}[\operatorname{DecidableEq}\left(Action\right)], [\operatorname{LE}\left(Information\right)], [\operatorname{LE}\left(Residual\right)], [\operatorname{LE}\left(Transfer\right)], [\operatorname{LE}\left(Cost\right)], [\operatorname{LE}\left(Risk\right)],\\{}[\forall a, b: Information, \operatorname{Decidable}\left(a \leq b\right)], [\forall a, b: Residual, \operatorname{Decidable}\left(a \leq b\right)], [\forall a, b: Transfer, \operatorname{Decidable}\left(a \leq b\right)],\\{}[\forall a, b: Cost, \operatorname{Decidable}\left(a \leq b\right)], [\forall a, b: Risk, \operatorname{Decidable}\left(a \leq b\right)],\\{}value: Action \to \operatorname{GainVector}\left(Information, Residual, Transfer, Cost, Risk\right), F: \operatorname{Finset}\left(Action\right),\\{}x: \operatorname{ParetoCarrier}\left(F\right),\\{}\operatorname{paretoClass}\left(value, F, x\right) = \operatorname{filter}\left(\operatorname{carrierEnum}\left(F\right), \lambda y, \operatorname{ParetoEqOn}\left(value, F, y, x\right)\right).\end{gathered}$$

*Formalization.* `D5/S3/ConceptDynamics/DefinitionEscapeAdjudication/FiniteParetoQuotient.paretoClass` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The class is computed by filtering the attached finite carrier with the decidable symmetric weak-Pareto kernel.

**Definition 1.2 (Finite image of all Pareto classes).**

$$\begin{gathered}\forall Action, Information, Residual, Transfer, Cost, Risk: \operatorname{Type},\\{}[\operatorname{DecidableEq}\left(Action\right)], [\operatorname{LE}\left(Information\right)], [\operatorname{LE}\left(Residual\right)], [\operatorname{LE}\left(Transfer\right)], [\operatorname{LE}\left(Cost\right)], [\operatorname{LE}\left(Risk\right)],\\{}[\forall a, b: Information, \operatorname{Decidable}\left(a \leq b\right)], [\forall a, b: Residual, \operatorname{Decidable}\left(a \leq b\right)], [\forall a, b: Transfer, \operatorname{Decidable}\left(a \leq b\right)],\\{}[\forall a, b: Cost, \operatorname{Decidable}\left(a \leq b\right)], [\forall a, b: Risk, \operatorname{Decidable}\left(a \leq b\right)],\\{}value: Action \to \operatorname{GainVector}\left(Information, Residual, Transfer, Cost, Risk\right), F: \operatorname{Finset}\left(Action\right),\\{}\operatorname{paretoClassImage}\left(value, F\right) = \operatorname{image}\left(\operatorname{carrierEnum}\left(F\right), \operatorname{paretoClass}\left(value, F\right)\right).\end{gathered}$$

*Formalization.* `D5/S3/ConceptDynamics/DefinitionEscapeAdjudication/FiniteParetoQuotient.paretoClassImage` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Taking the finite image removes duplicate classes while retaining an explicit representative-produced enumeration.

**Definition 1.3 (Finite Pareto quotient carrier).**

$$\begin{gathered}\forall Action, Information, Residual, Transfer, Cost, Risk: \operatorname{Type},\\{}[\operatorname{DecidableEq}\left(Action\right)], [\operatorname{LE}\left(Information\right)], [\operatorname{LE}\left(Residual\right)], [\operatorname{LE}\left(Transfer\right)], [\operatorname{LE}\left(Cost\right)], [\operatorname{LE}\left(Risk\right)],\\{}[\forall a, b: Information, \operatorname{Decidable}\left(a \leq b\right)], [\forall a, b: Residual, \operatorname{Decidable}\left(a \leq b\right)], [\forall a, b: Transfer, \operatorname{Decidable}\left(a \leq b\right)],\\{}[\forall a, b: Cost, \operatorname{Decidable}\left(a \leq b\right)], [\forall a, b: Risk, \operatorname{Decidable}\left(a \leq b\right)],\\{}value: Action \to \operatorname{GainVector}\left(Information, Residual, Transfer, Cost, Risk\right), F: \operatorname{Finset}\left(Action\right),\\{}\operatorname{FiniteParetoQuotient}\left(value, F\right) = \{C: \operatorname{Finset}\left(\operatorname{ParetoCarrier}\left(F\right)\right) \mid C \in \operatorname{paretoClassImage}\left(value, F\right)\}.\end{gathered}$$

*Formalization.* `D5/S3/ConceptDynamics/DefinitionEscapeAdjudication/FiniteParetoQuotient.FiniteParetoQuotient` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The quotient carrier is the subtype of finite classes in the class image; it does not invoke Lean's abstract Quotient type.

**Definition 1.4 (Complete explicit quotient enumeration).**

$$\begin{gathered}\forall Action, Information, Residual, Transfer, Cost, Risk: \operatorname{Type},\\{}[\operatorname{DecidableEq}\left(Action\right)], [\operatorname{LE}\left(Information\right)], [\operatorname{LE}\left(Residual\right)], [\operatorname{LE}\left(Transfer\right)], [\operatorname{LE}\left(Cost\right)], [\operatorname{LE}\left(Risk\right)],\\{}[\forall a, b: Information, \operatorname{Decidable}\left(a \leq b\right)], [\forall a, b: Residual, \operatorname{Decidable}\left(a \leq b\right)], [\forall a, b: Transfer, \operatorname{Decidable}\left(a \leq b\right)],\\{}[\forall a, b: Cost, \operatorname{Decidable}\left(a \leq b\right)], [\forall a, b: Risk, \operatorname{Decidable}\left(a \leq b\right)],\\{}value: Action \to \operatorname{GainVector}\left(Information, Residual, Transfer, Cost, Risk\right), F: \operatorname{Finset}\left(Action\right),\\{}\operatorname{quotientEnum}\left(value, F\right) = \operatorname{attach}\left(\operatorname{paretoClassImage}\left(value, F\right)\right).\end{gathered}$$

*Formalization.* `D5/S3/ConceptDynamics/DefinitionEscapeAdjudication/FiniteParetoQuotient.quotientEnum` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Attaching image-membership proofs turns the class image into an enumeration whose elements already have the quotient subtype.

**Definition 1.5 (Fintype from the explicit class image).**

$$\begin{gathered}\forall Action, Information, Residual, Transfer, Cost, Risk: \operatorname{Type},\\{}[\operatorname{DecidableEq}\left(Action\right)], [\operatorname{LE}\left(Information\right)], [\operatorname{LE}\left(Residual\right)], [\operatorname{LE}\left(Transfer\right)], [\operatorname{LE}\left(Cost\right)], [\operatorname{LE}\left(Risk\right)],\\{}[\forall a, b: Information, \operatorname{Decidable}\left(a \leq b\right)], [\forall a, b: Residual, \operatorname{Decidable}\left(a \leq b\right)], [\forall a, b: Transfer, \operatorname{Decidable}\left(a \leq b\right)],\\{}[\forall a, b: Cost, \operatorname{Decidable}\left(a \leq b\right)], [\forall a, b: Risk, \operatorname{Decidable}\left(a \leq b\right)],\\{}value: Action \to \operatorname{GainVector}\left(Information, Residual, Transfer, Cost, Risk\right), F: \operatorname{Finset}\left(Action\right),\\{}\operatorname{finiteParetoQuotientFintype}\left(value, F\right): \operatorname{Fintype}\left(\operatorname{FiniteParetoQuotient}\left(value, F\right)\right).\end{gathered}$$

*Formalization.* `D5/S3/ConceptDynamics/DefinitionEscapeAdjudication/FiniteParetoQuotient.finiteParetoQuotientFintype` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The class image supplies a finite type structure directly, including when the quotient is empty; no Nonempty premise is introduced.

**Theorem 1.6 (Classes are exact and their enumeration is complete).**

$$\begin{gathered}\forall Action, Information, Residual, Transfer, Cost, Risk: \operatorname{Type},\\{}[\operatorname{DecidableEq}\left(Action\right)], [\operatorname{Preorder}\left(Information\right)], [\operatorname{Preorder}\left(Residual\right)], [\operatorname{Preorder}\left(Transfer\right)], [\operatorname{Preorder}\left(Cost\right)], [\operatorname{Preorder}\left(Risk\right)],\\{}[\forall a, b: Information, \operatorname{Decidable}\left(a \leq b\right)], [\forall a, b: Residual, \operatorname{Decidable}\left(a \leq b\right)], [\forall a, b: Transfer, \operatorname{Decidable}\left(a \leq b\right)],\\{}[\forall a, b: Cost, \operatorname{Decidable}\left(a \leq b\right)], [\forall a, b: Risk, \operatorname{Decidable}\left(a \leq b\right)],\\{}value: Action \to \operatorname{GainVector}\left(Information, Residual, Transfer, Cost, Risk\right), F: \operatorname{Finset}\left(Action\right),\\{}(\forall x: \operatorname{ParetoCarrier}\left(F\right), x \in \operatorname{carrierEnum}\left(F\right)) \land\\{}(\forall x, y: \operatorname{ParetoCarrier}\left(F\right), y \in \operatorname{paretoClass}\left(value, F, x\right) \iff \operatorname{ParetoEqOn}\left(value, F, y, x\right)) \land\\{}(\forall x: \operatorname{ParetoCarrier}\left(F\right), x \in \operatorname{paretoClass}\left(value, F, x\right)) \land\\{}(\forall x, y: \operatorname{ParetoCarrier}\left(F\right), \operatorname{paretoClass}\left(value, F, x\right) = \operatorname{paretoClass}\left(value, F, y\right) \iff \operatorname{ParetoEqOn}\left(value, F, x, y\right)) \land\\{}(\forall C: \operatorname{FiniteParetoQuotient}\left(value, F\right), \operatorname{Nonempty}\left(\operatorname{val}\left(C\right)\right)) \land\\{}(\forall C: \operatorname{FiniteParetoQuotient}\left(value, F\right), \forall z: \operatorname{ParetoCarrier}\left(F\right), z \in \operatorname{val}\left(C\right) \Rightarrow \operatorname{paretoClass}\left(value, F, z\right) = \operatorname{val}\left(C\right)) \land\\{}(\forall C: \operatorname{FiniteParetoQuotient}\left(value, F\right), C \in \operatorname{quotientEnum}\left(value, F\right)) \land\\{}(F = \emptyset \Rightarrow \forall C: \operatorname{FiniteParetoQuotient}\left(value, F\right), False) \land\\{}(\operatorname{card}\left(F\right) = 1 \Rightarrow \exists C: \operatorname{FiniteParetoQuotient}\left(value, F\right), \forall D: \operatorname{FiniteParetoQuotient}\left(value, F\right), D = C).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/DefinitionEscapeAdjudication/FiniteParetoQuotient.finite_pareto_quotient_exact_and_complete` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every carrier element is enumerated; class membership is exactly ParetoEqOn; classes are reflexive, equal exactly for equivalent representatives, nonempty, stable under reclassification, and all occur in quotientEnum.

The same declaration verifies both boundary cases: an empty carrier has no quotient element, while a one-element carrier has exactly one quotient class.

## References

- Truth anchor: `D5/S3/ConceptDynamics/DefinitionEscapeAdjudication/FiniteParetoQuotient.FiniteParetoQuotient`
- Truth anchor: `D5/S3/ConceptDynamics/DefinitionEscapeAdjudication/FiniteParetoQuotient.finiteParetoQuotientFintype`
- Truth anchor: `D5/S3/ConceptDynamics/DefinitionEscapeAdjudication/FiniteParetoQuotient.finite_pareto_quotient_exact_and_complete`
- Truth anchor: `D5/S3/ConceptDynamics/DefinitionEscapeAdjudication/FiniteParetoQuotient.paretoClass`
- Truth anchor: `D5/S3/ConceptDynamics/DefinitionEscapeAdjudication/FiniteParetoQuotient.paretoClassImage`
- Truth anchor: `D5/S3/ConceptDynamics/DefinitionEscapeAdjudication/FiniteParetoQuotient.quotientEnum`
- Dependency: [D5/S3/ConceptDynamics/DefinitionEscapeAdjudication/ParetoEqOnDecidableEquivalence](ParetoEqOnDecidableEquivalence.md)
