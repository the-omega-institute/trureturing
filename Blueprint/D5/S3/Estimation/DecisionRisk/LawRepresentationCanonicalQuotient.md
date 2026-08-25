# Law Representations and the Canonical Quotient

## Abstract

A law-determining representation refines the canonical law quotient.

**Theorem 1.1 (Law-determining representations refine the canonical quotient).**

$$\forall State, Representation, Law: Type,\\{}Lambda: State \to Law, r: State \to Representation,\\{}\phi: Representation \to Law, Lambda = \phi \circ r \Rightarrow\\{}(\forall x, y: State, \operatorname{r}\left(x\right) = \operatorname{r}\left(y\right) \Rightarrow \operatorname{Lambda}\left(x\right) = \operatorname{Lambda}\left(y\right)) \land\\{}\operatorname{Injective}\left(\operatorname{kerLift}\left(Lambda\right)\right) \land Lambda = \operatorname{kerLift}\left(Lambda\right) \circ \operatorname{quotientProjection}\left(\operatorname{ker}\left(Lambda\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/DecisionRisk/LawRepresentationCanonicalQuotient.law_determining_representation_refines_canonical_law_quotient` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The complete experiment law is an arbitrary typed map from State to Law. A representation determines it through the displayed decodeLaw factorization.

Equal representation values therefore give equal complete laws. The same law map defines the canonical equality-kernel quotient; its Mathlib kerLift is injective and reconstructs the law after the quotient projection.

Thus the quotient retains exactly the state distinctions visible to the experiment law. No second law, quotient, or equivalence relation is introduced.

## References

- Truth anchor: `D5/S3/Estimation/DecisionRisk/LawRepresentationCanonicalQuotient.law_determining_representation_refines_canonical_law_quotient`
