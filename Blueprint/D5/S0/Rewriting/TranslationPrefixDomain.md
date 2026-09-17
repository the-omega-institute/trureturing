# Domains of Guarded Translation Words

## Abstract

Domains of Guarded Translation Words.

**Theorem 1.1 (All prefixes determine successful evaluation).**

Lean statement: `D5/S0/Rewriting/TranslationPrefixDomain.eval_eq_some_iff`

*Proof.* Machine-checked in Lean as `D5/S0/Rewriting/TranslationPrefixDomain.eval_eq_some_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a finite coordinate set, a natural capacity at each coordinate, and a finite word of integer translation vectors, evaluation succeeds at a specified endpoint exactly when every prefix displacement added to the initial state lies between zero and the capacity in every coordinate, and the endpoint is the initial state plus the sum of the word. Prefixes include the empty word and the whole word. The recursive evaluation stops at the first state outside the box; the empty word also checks its initial state.

## References

- Truth anchor: `D5/S0/Rewriting/TranslationPrefixDomain.eval_eq_some_iff`
- Dependency: [D5/S0/Automata/TypedPartialDFAOOverBase](../Automata/TypedPartialDFAOOverBase.md)
