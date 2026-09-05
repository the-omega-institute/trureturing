# Finite-Generation Inheritance of Three Object Laws

## Abstract

Three external object laws inherited by finite generators and finitary rules hold on their generated closure.

**Theorem 1.1 (Finite generation inherits temporal, unitary, and ledger laws).**

$$\forall \sigma: \operatorname{FiniteGenerationSystem}, t, u, l,\\{}(\forall i, {\operatorname{t}\left(\operatorname{generator}\left(\sigma, i\right)\right) \land \operatorname{u}\left(\operatorname{generator}\left(\sigma, i\right)\right) \land \operatorname{l}\left(\operatorname{generator}\left(\sigma, i\right)\right)}) \land (\forall r, x, (\forall j, {\operatorname{t}\left(x_{j}\right) \land \operatorname{u}\left(x_{j}\right) \land \operatorname{l}\left(x_{j}\right)}) \Rightarrow {\operatorname{t}\left(\operatorname{construct}\left(\sigma, r, x\right)\right) \land \operatorname{u}\left(\operatorname{construct}\left(\sigma, r, x\right)\right) \land \operatorname{l}\left(\operatorname{construct}\left(\sigma, r, x\right)\right)})\\{}\Rightarrow \forall y, \operatorname{Generated}\left(\sigma, y\right) \Rightarrow {\operatorname{t}\left(y\right) \land \operatorname{u}\left(y\right) \land \operatorname{l}\left(y\right)}.$$

*Proof.* Machine-checked in Lean as `D5/S0/Computability/FiniteGeneratedPropertyInheritance.finite_generated_property_inheritance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let Sigma be a finite generation system on internal property objects. Write Three(x) for the conjunction of the external temporal, unitary, and ledgered predicates at x. If every registered generator satisfies Three and every registered finite-arity rule preserves Three on its inputs, every generated object satisfies Three.

The proof is structural induction on the Generated derivation. The generator case is exactly the supplied generator law; the rule case applies the preservation law to the induction hypotheses for all finitely many inputs.

The three properties remain predicates supplied to the theorem, rather than fields inserted into the object. Their inheritance is therefore proved rather than true by construction. The module reuses the existing InternalProperty carrier and does not repackage the separate fixed-code construction.

## References

- Truth anchor: `D5/S0/Computability/FiniteGeneratedPropertyInheritance.finite_generated_property_inheritance`
- Dependency: [D5/S0/Computability/PropertyObject](PropertyObject.md)
