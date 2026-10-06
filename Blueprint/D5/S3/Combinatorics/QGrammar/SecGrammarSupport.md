# Support Reduction for the Sec Derivative

## Abstract

Positive coefficients make support evolution exactly the collection of normalized positional branches.

**Theorem 1.1 (Support reduction and positivity).**

Lean statement: `D5/S3/Combinatorics/QGrammar/SecGrammarSupport.support_reduction`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/QGrammar/SecGrammarSupport.support_reduction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Guo-Niu Han, Kathy Q. Ji, Huan Xiong (2026). *q-Derivative Grammar*. DOI: [10.48550/arXiv.2604.23959](https://doi.org/10.48550/arXiv.2604.23959). URL: <https://arxiv.org/abs/2604.23959v2>.

*Commentary.*

At every step all polynomial coefficients are nonnegative. A word belongs to the next support exactly when it is obtained by choosing a support word, a position, and a supported replacement, then applying the DIO normalization to the resulting concatenation.

## References

- Truth anchor: `D5/S3/Combinatorics/QGrammar/SecGrammarSupport.support_reduction`
- Dependency: [D5/S3/Combinatorics/QGrammar/SecGrammarDefs](SecGrammarDefs.md)
