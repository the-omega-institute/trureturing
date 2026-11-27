# A counterexample to Guyot's square-root state bound

## Abstract

The square root of the subword closure of abcdabcdabdc requires at least sixteen complete DFA states.

**Definition 1.1 (Square root of a subword closure).**

$$\forall A \in Type,\; \forall w \in \operatorname{List}\left(A\right),\; \operatorname{squareRootLanguage}\left(w\right) = \{x : \operatorname{List}\left(A\right) \mid \operatorname{Sublist}\left(\operatorname{append}\left(x, x\right), w\right)\}$$

*Formalization.* `D5/S0/Automata/GuyotSquareRootStateComplexityRefutation.squareRootLanguage` (`✓ std3`).

*Citation.* Jérôme Guyot (2024). *On state complexity for subword-closed languages*. URL: <https://arxiv.org/abs/2407.10355v1>.

*Commentary.*

The predicate Sublist means scattered subsequence, allowing omitted letters while preserving their order. Append joins two words, so the test uses two consecutive copies of x.

**Definition 1.2 (Universal upper-bound conjunct of Conjecture 1).**

$$claim \Leftrightarrow (\forall n \in \mathbb{N},\; 0 < n \Rightarrow (\forall A \in Type,\; [\operatorname{Finite}\left(A\right)] \forall w \in \operatorname{List}\left(A\right),\; \operatorname{length}\left(w\right) \le n \Rightarrow \left(\exists m \in \mathbb{N},\; m \le \operatorname{div}\left(n + 2, 3\right)^{2} - \operatorname{div}\left(n + 2, 3\right) + 3 \land (\exists M \in \operatorname{DFA}\left(A, \operatorname{Fin}\left(m\right)\right),\; \operatorname{accepts}\left(M\right) = \operatorname{squareRootLanguage}\left(w\right))\right)))$$

*Formalization.* `D5/S0/Automata/GuyotSquareRootStateComplexityRefutation.claim` (`✓ std3`).

*Citation.* Jérôme Guyot (2024). *On state complexity for subword-closed languages*. URL: <https://arxiv.org/abs/2407.10355v1>.

*Commentary.*

Conjecture 1 in §2.2 states “∀ n ∈ ℕ₍>₀₎, κ(√↓(Uₙ)) = α(n) ≤ c(n)² − c(n) + 3.”

The upper-bound conjunct concerns α(n), the largest quotient count for words of length at most n. The conjectured equality involving Uₙ is separate.

For each positive n, each finite alphabet A, and each word w of length at most n, the bound calls for a complete DFA M on Fin(m) whose accepted language is exactly the square root of the subword closure of w. Nat.div gives c(n) as (n + 2) div 3. The expression uses natural subtraction, which agrees with ordinary subtraction since c(n)² is at least c(n).

The source counts all distinct left quotients, including the empty quotient when it occurs. Every quotient is the continuation language of a reached DFA state. Conversely, the distinct quotients form a complete DFA with transitions given by further left quotienting, and its finite state set can be indexed by Fin(m).

**Theorem 1.3 (Sixteen distinct quotients at length twelve).**

$$\neg (\forall n \in \mathbb{N},\; 0 < n \Rightarrow (\forall A \in Type,\; [\operatorname{Finite}\left(A\right)] \forall w \in \operatorname{List}\left(A\right),\; \operatorname{length}\left(w\right) \le n \Rightarrow \left(\exists m \in \mathbb{N},\; m \le \operatorname{div}\left(n + 2, 3\right)^{2} - \operatorname{div}\left(n + 2, 3\right) + 3 \land (\exists M \in \operatorname{DFA}\left(A, \operatorname{Fin}\left(m\right)\right),\; \operatorname{accepts}\left(M\right) = \operatorname{squareRootLanguage}\left(w\right))\right)))$$

*Proof.* Machine-checked in Lean as `D5/S0/Automata/GuyotSquareRootStateComplexityRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/guyot-2024-square-root-state-complexity` (refuted) by `D5/S0/Automata/GuyotSquareRootStateComplexityRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"guyot-2024-square-root-state-complexity","declaration_gid":"D5/S0/Automata/GuyotSquareRootStateComplexityRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Jérôme Guyot (2024). *On state complexity for subword-closed languages*. URL: <https://arxiv.org/abs/2407.10355v1>.

*Commentary.*

Use n = 12 and the alphabet Fin(4), with a, b, c, d represented by 0, 1, 2, 3. For w = abcdabcdabdc, the bound allows at most 15 states.

The selected prefixes are the empty word, a, b, c, d, aa, ab, ac, ad, ba, bc, bd, ca, cd, da, and bcd. Among the empty suffix and the four one-letter suffixes, each pair of prefixes has a suffix for which the sublist test on the doubled concatenation gives opposite answers.

Mathlib's leftQuotient_accepts_apply identifies the left quotient by a prefix with the language accepted from the state reached by that prefix. Thus the sixteen prefixes reach distinct states, contradicting the bound of fifteen.

## References

- Truth anchor: `D5/S0/Automata/GuyotSquareRootStateComplexityRefutation.claim`
- Truth anchor: `D5/S0/Automata/GuyotSquareRootStateComplexityRefutation.result`
- Truth anchor: `D5/S0/Automata/GuyotSquareRootStateComplexityRefutation.squareRootLanguage`
