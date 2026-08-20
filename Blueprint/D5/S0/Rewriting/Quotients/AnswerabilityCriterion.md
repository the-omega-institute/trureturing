# Answerability Criterion

## Abstract

Factorization, fiber constancy, and absence of a defect pair are equivalent criteria for answering a question from a concept readout.

**Theorem 1.1 (Three equivalent criteria characterize answerability).**

$$\forall X, B, A: \operatorname{Type},\\anchor: X, concept: X \to B, question: X \to A,\\(\exists answer: B \to A, question = answer \circ concept \Leftrightarrow \forall x, y: X, concept(x) = concept(y) \Rightarrow question(x) = question(y)) \land\\(\forall x, y: X, concept(x) = concept(y) \Rightarrow question(x) = question(y) \Leftrightarrow \{(x, y): X \times X \mid concept(x) = concept(y) \land question(x) \neq question(y)\} = \emptyset) \land\\(\{(x, y): X \times X \mid concept(x) = concept(y) \land question(x) \neq question(y)\} = \emptyset \Leftrightarrow \exists answer: B \to A, question = answer \circ concept).$$

*Proof.* Machine-checked in Lean as `D5/S0/Rewriting/Quotients/AnswerabilityCriterion.answerability_criterion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The state anchor is part of the source model. It supplies an actual question value, which is exactly the inhabitance needed to extend a fiber-constant question from the image of the concept readout to its full answer domain.

The defect relation is constructed directly from the two readouts: it contains precisely those state pairs with equal concept values and unequal question values. Thus its emptiness is independently equivalent to constancy on every concept fiber.

Pinned Mathlib's Function.factorsThrough_iff is the exact factorization criterion and is applied directly. Repository searches found only an adjacent one-way kernel-refinement theorem, not this complete three-clause equivalence.

## References

- Truth anchor: `D5/S0/Rewriting/Quotients/AnswerabilityCriterion.answerability_criterion`
