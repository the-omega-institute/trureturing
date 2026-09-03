# Typed Partial DFAOs over a Numeration Base

## Abstract

Typed partial DFAOs preserve an underlying numeration automaton and separate global correctness from finite-prefix fitting.

**Theorem 1.1 (Every bounded global model fits every finite prefix).**

$$\operatorname{HasGlobalModelAtMost}(P, k) \implies \operatorname{HasPrefixModelAtMost}(P, N, k)$$

*Proof.* Machine-checked in Lean as `D5/S0/Automata/TypedPartialDFAOOverBase.sparse_global_model_implies_prefix_model` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The base automaton owns legality, while every defined DFAO transition projects to a legal base transition. Sparse correctness is stated independently from finite-prefix fitting.

The theorem is the logical direction required by finite UNSAT certificates: any globally correct bounded-state machine would also be a model of every genuine finite prefix.

## References

- Truth anchor: `D5/S0/Automata/TypedPartialDFAOOverBase.sparse_global_model_implies_prefix_model`
- Dependency: [D5/S0/Automata/DFAOStateLowerBound](DFAOStateLowerBound.md)
