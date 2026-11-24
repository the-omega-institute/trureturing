# A shortest first-factor reset can miss the product optimum

## Abstract

A three-by-four DFA product whose shortest reset has a different initial letter from the shortest first-factor reset.

**Theorem 1.1 (The shortest-first strategy can be suboptimal).**

$$\neg (\begin{aligned}\forall k,m,n: \mathbb{N}, 0 < k \land \left(0 < m \land 0 < n\right) \to\\\forall A: \operatorname{DFA}\left(\operatorname{Fin}\left(k\right), \operatorname{Fin}\left(m\right)\right), \forall B: \operatorname{DFA}\left(\operatorname{Fin}\left(k\right), \operatorname{Fin}\left(n\right)\right),\\(\exists r: \operatorname{Fin}\left(k\right)^{*}, \operatorname{R}\left(A, \operatorname{Q}\left(A\right), r\right)) \land (\exists s: \operatorname{Fin}\left(k\right)^{*}, \operatorname{R}\left(B, \operatorname{Q}\left(B\right), s\right)) \to\\\begin{aligned}\exists u,v: \operatorname{Fin}\left(k\right)^{*}, (\\(\operatorname{R}\left(A, \operatorname{Q}\left(A\right), u\right) \land (\forall w: \operatorname{Fin}\left(k\right)^{*}, \operatorname{R}\left(A, \operatorname{Q}\left(A\right), w\right) \Rightarrow \lvert u\rvert \le \lvert w\rvert))\\\land (\operatorname{R}\left(B, \operatorname{I}\left(B, \operatorname{Q}\left(B\right), u\right), v\right) \land (\forall w: \operatorname{Fin}\left(k\right)^{*}, \operatorname{R}\left(B, \operatorname{I}\left(B, \operatorname{Q}\left(B\right), u\right), w\right) \Rightarrow \lvert v\rvert \le \lvert w\rvert))\\\land (\operatorname{R}\left((A \times B), \operatorname{Q}\left((A \times B)\right), uv\right) \land (\forall w: \operatorname{Fin}\left(k\right)^{*}, \operatorname{R}\left((A \times B), \operatorname{Q}\left((A \times B)\right), w\right) \Rightarrow \lvert uv\rvert \le \lvert w\rvert)))\end{aligned}\end{aligned})$$

*Proof.* Machine-checked in Lean as `D5/S0/Automata/FernauRystsovShortestResetPrefix.result` (`✓ std3`). ∎

*Resolves.* `Problems/fernau-rystsov-2026-shortest-reset-prefix` (refuted) by `D5/S0/Automata/FernauRystsovShortestResetPrefix.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"fernau-rystsov-2026-shortest-reset-prefix","declaration_gid":"D5/S0/Automata/FernauRystsovShortestResetPrefix.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Henning Fernau and Igor Rystsov (2026). *Shortest Synchronizing Words on Product Automata*. DOI: [10.48550/arXiv.2611.09136](https://doi.org/10.48550/arXiv.2611.09136). URL: <https://arxiv.org/abs/2611.09136v1>.

*Commentary.*

Take a shared alphabet Fin(k) and state sets Fin(m) and Fin(n), with all three sizes positive. Each DFA has a total transition for each state and letter. The product A × B applies the same letter in both coordinates. The predicate R(A,S,w) means that the image I(A,S,w) of S under the word w is a singleton. Write Q(A) for the full state set and use juxtaposition for word concatenation. All word quantifiers include the empty word. The start and accepting fields have no role in the reset predicates.

The fourth question of §7 asks about choosing a shortest first-factor reset before solving subset synchronization on the second factor. Here optimality means attaining the global product minimum. Lemma 6 already gives feasibility by concatenating whole-factor resets. Once u resets A, a suffix v resets the residual second-factor subset exactly when uv resets the product. For a globally shortest uv, any shorter reset of that subset would give a shorter product reset. This is why the shortest-prefix formulation implies the suffix minimality in the displayed proposition.

On the alphabet {a,b}, the first factor has transitions a ↦ (0,0,1) and b ↦ (1,2,0). The second has a ↦ (1,1,2,0) and b ↦ (0,2,3,0), with states listed in increasing order. Evaluating every word of lengths zero through four gives the unique shortest first- and second-factor resets aa and bbb and the unique shortest product reset bbaa. The product reset begins with b, so aa cannot be its prefix. After aa the second-factor image is {1,2}, whose shortest reset is bbb. The staged word aabbb thus has length five, while bbaa has length four.

## References

- Truth anchor: `D5/S0/Automata/FernauRystsovShortestResetPrefix.result`
