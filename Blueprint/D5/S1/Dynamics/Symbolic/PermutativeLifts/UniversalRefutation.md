# A single base refutes the general minimal branch

## Abstract

A single base refutes the general minimal branch.

**Definition 1.1 (Construction).**

Lean statement: `D5/S1/Dynamics/Symbolic/PermutativeLifts/UniversalRefutation.claim`

*Formalization.* `D5/S1/Dynamics/Symbolic/PermutativeLifts/UniversalRefutation.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Z. Kang; T. Jäger (2026). *On lifts of strictly ergodic subshifts by permutative sliding block codes*. DOI: [10.48550/arXiv.2609.01140](https://doi.org/10.48550/arXiv.2609.01140). URL: <https://arxiv.org/abs/2609.01140v1>.

*Commentary.*

The claim quantifies over all finite discrete alphabets with at least two letters and all nonempty minimal two-sided subshifts, and asserts the existence of a length at least two and a bipermutative code whose complete inverse image is minimal. Its literal negation follows from the single explicit infinite binary factorial subshift: every allowed length and every such code have a nonminimal whole lift. This settles only the general minimal branch specified in the problem dossier. Unique ergodicity and the optional Toeplitz hypothesis are not conclusions of this formal result. Priority remains unestablished; the coboundary mechanism has prior literature.

**Theorem 1.2 (Result).**

Lean statement: `D5/S1/Dynamics/Symbolic/PermutativeLifts/UniversalRefutation.result`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Symbolic/PermutativeLifts/UniversalRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/kang-jager-2026-universal-permutative-lift-refutation` (refuted) by `D5/S1/Dynamics/Symbolic/PermutativeLifts/UniversalRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"kang-jager-2026-universal-permutative-lift-refutation","declaration_gid":"D5/S1/Dynamics/Symbolic/PermutativeLifts/UniversalRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Z. Kang; T. Jäger (2026). *On lifts of strictly ergodic subshifts by permutative sliding block codes*. DOI: [10.48550/arXiv.2609.01140](https://doi.org/10.48550/arXiv.2609.01140). URL: <https://arxiv.org/abs/2609.01140v1>.

*Commentary.*

The claim quantifies over all finite discrete alphabets with at least two letters and all nonempty minimal two-sided subshifts, and asserts the existence of a length at least two and a bipermutative code whose complete inverse image is minimal. Its literal negation follows from the single explicit infinite binary factorial subshift: every allowed length and every such code have a nonminimal whole lift. This settles only the general minimal branch specified in the problem dossier. Unique ergodicity and the optional Toeplitz hypothesis are not conclusions of this formal result. Priority remains unestablished; the coboundary mechanism has prior literature.

## References

- Truth anchor: `D5/S1/Dynamics/Symbolic/PermutativeLifts/UniversalRefutation.claim`
- Truth anchor: `D5/S1/Dynamics/Symbolic/PermutativeLifts/UniversalRefutation.result`
- Dependency: [D5/S1/Dynamics/Symbolic/PermutativeLifts/UniversalLiftSplitting](UniversalLiftSplitting.md)
