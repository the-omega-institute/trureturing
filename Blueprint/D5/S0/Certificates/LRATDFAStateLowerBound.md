# LRAT Certificates for Sparse DFAO State Lower Bounds

## Abstract

A kernel-checked LRAT refutation of any certified finite-prefix encoding rules out every globally correct DFAO within the same state budget.

**Theorem 1.1 (Finite-prefix refutation gives a global bounded-state exclusion).**

$$\operatorname{Refutation}(\operatorname{formula}(E)) \implies \neg\operatorname{HasGlobalModelAtMost}(P, b)$$

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/LRATDFAStateLowerBound.no_global_model_at_most_of_prefix_refutation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Here E is a certified encoding of the prefix-model predicate for the sparse problem P at extent e and state budget b. Global correctness implies finite-prefix fitting; the certified encoding turns any prefix model into a satisfying valuation, while the Mathlib LRAT empty-clause proof excludes every such valuation.

**Theorem 1.2 (An upper machine and a lower refutation prove exact minimality).**

$$\operatorname{HasGlobalModel}(P, s) \land \operatorname{Refutation}(\operatorname{formula}(E)) \implies \operatorname{IsMinimalStateCount}(P, s)$$

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/LRATDFAStateLowerBound.minimal_state_count_of_prefix_refutation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Here E is a certified encoding of the prefix-model predicate for P at extent e and state budget s minus one. A globally correct machine at the proposed state count supplies the upper bound. Refuting every finite-prefix model below that count supplies the lower bound, so exact typed state minimality follows.

## References

- Truth anchor: `D5/S0/Certificates/LRATDFAStateLowerBound.minimal_state_count_of_prefix_refutation`
- Truth anchor: `D5/S0/Certificates/LRATDFAStateLowerBound.no_global_model_at_most_of_prefix_refutation`
- Dependency: [D5/S0/Certificates/DFAIdentificationCNF](DFAIdentificationCNF.md)
- Dependency: [D5/S0/Certificates/LRATUnsatisfiable](LRATUnsatisfiable.md)
