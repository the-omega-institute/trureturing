# Odd-Test Family Budget Upper Bound

## Abstract

The admissible finite odd-test family bounds a negative rank-one pencil's budget by its Rayleigh-infimum endpoint.

**Theorem 1.1 (The odd-test family bounds the budget by its infimum endpoint).**

$$\begin{gathered}\forall n: \mathbb{N},\\{}B: \operatorname{Matrix}(\operatorname{Fin}(n), \operatorname{Fin}(n), \mathbb{C}),\\{}s: \operatorname{Fin}(n) \to \mathbb{C},\\{}R0, R: \mathbb{R},\\{}((\exists o: \operatorname{Fin}(n) \to \mathbb{C}, \langle s, o \rangle \neq 0) \land\\{}\operatorname{BddBelow}(\left\{\exists o: \operatorname{Fin}(n) \to \mathbb{C}, \langle s, o \rangle \neq 0 \land q = \frac{\operatorname{Re}(\langle o, \operatorname{mulVec}(B, o) \rangle)}{\operatorname{normSq}(\langle s, o \rangle)} \mid q \in \mathbb{R}\right\}) \land\\{}(\forall o: \operatorname{Fin}(n) \to \mathbb{C}, \langle s, o \rangle \neq 0 \Rightarrow 0 \le \operatorname{Re}(\langle o, \operatorname{mulVec}(B, o) \rangle) - (R - R0) \cdot \operatorname{normSq}(\langle s, o \rangle))) \Rightarrow\\{}R \le R0 + \operatorname{sInf}(\left\{\exists o: \operatorname{Fin}(n) \to \mathbb{C}, \langle s, o \rangle \neq 0 \land q = \frac{\operatorname{Re}(\langle o, \operatorname{mulVec}(B, o) \rangle)}{\operatorname{normSq}(\langle s, o \rangle)} \mid q \in \mathbb{R}\right\}).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Budget/OddTestBudgetUpperBound.odd_test_budget_at_most_upper` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The public odd-test quotient set contains the Rayleigh quotient of every finite complex test with nonzero boundary pairing. Its upper endpoint is the reference budget plus the real infimum of that entire set.

The family is explicitly nonempty and bounded below. Nonnegativity of the negative rank-one pencil is assumed for every admissible test; each nonzero boundary pairing has positive norm square, so division makes the shifted budget a lower bound of every quotient. The conditional infimum property then gives the endpoint bound.

The repository contains a generic parity endpoint construction, but no finite-matrix theorem exposing this negative rank-one pencil. The proof reuses the pinned norm-square, positive-division, and real infimum lemmas.

## References

- Truth anchor: `D5/S3/Weil/Budget/OddTestBudgetUpperBound.odd_test_budget_at_most_upper`
