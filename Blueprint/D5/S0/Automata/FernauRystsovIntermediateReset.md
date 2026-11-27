# Every intermediate reset threshold occurs in a DFA product

## Abstract

Two finite chains over a shared binary alphabet realize every product reset threshold between the maximum and the sum of their factor thresholds.

**Definition 1.1 (Minimum observed reset length).**

Lean statement: `D5/S0/Automata/FernauRystsovIntermediateReset.Threshold`

*Formalization.* `D5/S0/Automata/FernauRystsovIntermediateReset.Threshold` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Henning Fernau and Igor Rystsov (2026). *Shortest Synchronizing Words on Product Automata*. DOI: [10.48550/arXiv.2611.09136](https://doi.org/10.48550/arXiv.2611.09136). URL: <https://arxiv.org/abs/2611.09136v1>.

*Commentary.*

For any state type σ, a total DFA M over Bool, a function ℓ from finite Boolean words to natural numbers and a natural number n, Threshold ℓ M n asserts that there exists a word w with ℓ(w) = n and singleton full-state image under evaluation. Every finite word v with singleton full-state image must satisfy n ≤ ℓ(v). The function ℓ is a parameter, and the attainment theorem instantiates it with List.length. The definition quantifies over the empty word as well.

**Theorem 1.2 (Attainment throughout the product interval).**

$$\begin{aligned}\forall r,s,m: \mathbb{N}, (\operatorname{max}\left(r, s\right) \le m \land m \le r + s) \longrightarrow\\\exists A: \operatorname{DFA}\left(\mathrm{Bool}, \operatorname{Fin}\left(r + 1\right)\right), \exists B: \operatorname{DFA}\left(\mathrm{Bool}, \operatorname{Fin}\left(s + 1\right)\right), \operatorname{T}\left(A, r\right) \land \left(\operatorname{T}\left(B, s\right) \land \operatorname{T}\left(A \times B, m\right)\right)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S0/Automata/FernauRystsovIntermediateReset.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Henning Fernau and Igor Rystsov (2026). *Shortest Synchronizing Words on Product Automata*. DOI: [10.48550/arXiv.2611.09136](https://doi.org/10.48550/arXiv.2611.09136). URL: <https://arxiv.org/abs/2611.09136v1>.

*Commentary.*

The second bullet of §7, p. 19, asks “Can we show that each “intermediate number” between the lower and upper bound of Proposition 7 can be attained?”

Write T(M,n) when some finite word of length n maps the entire state set of M to a singleton, and every word with singleton full-state image has length at least n. Words include the empty word. Both automata have total transitions and use Bool, with a = false and b = true. Their state sets are Fin(r+1) and Fin(s+1), which are nonempty even at threshold zero. The product A × B acts on the full Cartesian state set by applying the same letter in both coordinates. The designated start and accepting states play no role in the full-state reset test.

Put t = r+s−m, so 0 ≤ t ≤ min(r,s). In the first chain, a advances one step up to r, and b advances one step only below t. In the second chain, a fixes every state and b advances one step up to s. The factor reset words are r copies of a and s copies of b. No shorter word can take the bottom to the fixed top in either factor because each coordinate advances by at most one per letter.

In the product, s copies of b bring every first coordinate to at least t and every second coordinate to s. Then r−t copies of a finish the first coordinate while fixing the second. Any reset word must send (0,0) to the fixed pair (r,s). The potential max(i−t,0)+j increases by at most one per letter. Letter a can increase only the first summand, and letter b leaves the first summand unchanged while advancing the second coordinate. The total increase from (0,0) to (r,s) is m, which proves minimality over all words.

The lower endpoint has t = min(r,s) and the upper endpoint has t = 0. A zero factor threshold gives a singleton with the empty reset word, and m then equals the other threshold. Proposition 7 supplies the necessity of the interval for finite factor and product thresholds.

## References

- Truth anchor: `D5/S0/Automata/FernauRystsovIntermediateReset.Threshold`
- Truth anchor: `D5/S0/Automata/FernauRystsovIntermediateReset.result`
