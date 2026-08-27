# Observer Strategy Factorization

## Abstract

Observer strategy factorization is equivalent to reverse kernel inclusion.

**Theorem 1.1 (An effective interface implements exactly its fiber-constant policies).**

$$\forall X: \operatorname{Type}, O: \operatorname{Type}, Policy: \operatorname{Type},\\{}q: X \to O, Pi: X \to Policy,\\{}\operatorname{Surjective}(q) \Rightarrow (\operatorname{Refines}(Pi, q) \iff \operatorname{ker}(q) \subseteq \operatorname{ker}(Pi)).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/RefinementAlgebra/ObserverStrategyFactorization.observer_strategy_factorization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The observer interface is surjective onto its declared coordinate carrier, matching the source convention that interfaces use only realized values. The policy readout need not be surjective.

A factorization makes the policy constant on every interface fiber. Conversely, a section of the effective interface constructs the policy implementation from the kernel-inclusion premise.

The repository's existing effective-kernel theorem assumes both readouts are surjective, so applying it here would add a premise absent from the source.

## References

- Truth anchor: `D5/S3/ConceptDynamics/RefinementAlgebra/ObserverStrategyFactorization.observer_strategy_factorization`
- Dependency: [D5/S3/ConceptDynamics/ConceptJoinUniversal](../ConceptJoinUniversal.md)
