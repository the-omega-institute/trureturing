# Gettier Witness

## Abstract

A Gettier witness is justified true belief accompanied by an admissible same-evidence counterexample.

**Definition 1.1 (Gettier witness).**

$$\operatorname{gettier}\left(P, E, Bel, Just, Adm, a\right) \iff\\{}\operatorname{P}\left(a\right) \land\\{}\operatorname{Bel}\left(E, P, a\right) \land\\{}\operatorname{Just}\left(\operatorname{E}\left(a\right), P\right) \land\\{}\exists x, \operatorname{Adm}\left(x\right) \land \operatorname{E}\left(x\right) = \operatorname{E}\left(a\right) \land \neg\operatorname{P}\left(x\right).$$

*Formalization.* `D5/S3/ConceptDynamics/Epistemic/GettierWitness.gettier` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Let X be a state type and B an evidence type. Fix a state predicate P, evidence map E, evidence-indexed belief operator Bel, justification predicate Just, admissibility predicate Adm, and anchor a.

The anchor satisfies P, Bel receives E and affirms P at a, and Just affirms P for E(a). In addition, an admissible witness x has exactly the same evidence as a while P(x) is false.

The source ends immediately after the displayed definition. No conclusion after that truncation is supplied here.

**Theorem 1.2 (Concrete positive and negative instances).**

$$\begin{gathered}\operatorname{P}\left(n\right) \iff n = 0, \operatorname{E}\left(n\right) = 7,\\{}\left(Bel_{0}\right)\left(E, P, n\right) \iff n = 0, \left(Bel_{1}\right)\left(E, P, n\right) \iff n = 1,\\{}\operatorname{Just}\left(e, P\right) \iff e = 7, \operatorname{Adm}\left(n\right) \iff n = 1,\\{}\operatorname{gettier}\left(P, E, Bel_{0}, Just, Adm, 0\right) \land \neg\operatorname{gettier}\left(P, E, Bel_{1}, Just, Adm, 0\right).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Epistemic/GettierWitness.gettier_concrete_examples` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Take natural-number states with P true exactly at 0, constant evidence E(n) = 7, justification true exactly for evidence 7, and admissibility true exactly at state 1.

When belief is true exactly at anchor 0, state 1 is the required admissible counterexample: E(1) = E(0) = 7 and P(1) is false, while all three anchor clauses hold.

Keeping every other component fixed but requiring belief at state 1 breaks the belief clause at anchor 0, since 0 is not 1. Thus the first instance satisfies gettier and the second does not.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Epistemic/GettierWitness.gettier`
- Truth anchor: `D5/S3/ConceptDynamics/Epistemic/GettierWitness.gettier_concrete_examples`
