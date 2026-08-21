# Coding-Dependent Orders on Finite Interpretations

## Abstract

Any chosen finite interpretation can receive the unique shortest prefix codeword.

**Theorem 1.1 (Any chosen finite interpretation can be uniquely shortest).**

$$\forall n \in \mathbb{N}, \forall i: \operatorname{Fin}(n),\ \exists c: \operatorname{Fin}(n) \to \operatorname{List}(Bool \times \operatorname{Fin}(n)),\ \operatorname{Injective}(c) \land \operatorname{IsPrefixFree}(\operatorname{range}(c)) \land\ \forall j: \operatorname{Fin}(n), j \neq i \Rightarrow \lvert c(i) \rvert < \lvert c(j) \rvert.$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/InterpretationOrderCoding.exists_prefix_code_with_chosen_unique_shortest` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The finite interpretation family is indexed by `Fin n`, and the chosen index itself witnesses that the family is nonempty. The code is injective and its range is prefix-free.

The coding alphabet is `Bool x Fin n`, so it is allowed to depend on the interpretation family. The chosen interpretation receives a one-symbol word. Every other interpretation receives a two-symbol word whose first symbol separates it from the chosen word and whose second symbol records its index.

Consequently, shortest code length cannot select an objective interpretation while the coding language is unconstrained: any designated interpretation can be made uniquely shortest. Restricting to acceptable universal languages and comparing only up to an invariance constant are boundary conditions motivated by this result; they are not formalized as additional conclusions here.

Repository search found and directly reused `IsPrefixFree` from `D5/S0/Computability/Coding/PrefixFreeCode`. Pinned Mathlib provides the list prefix relation but no prefix-code predicate or theorem assigning a unique shortest codeword to a chosen labelled member. The repository Kraft converse is adjacent but returns an unlabelled list of codewords, so it does not prove this selected-member result.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Coding/InterpretationOrderCoding.exists_prefix_code_with_chosen_unique_shortest`
- Dependency: [D5/S0/Computability/Coding/PrefixFreeCode](../../../S0/Computability/Coding/PrefixFreeCode.md)
