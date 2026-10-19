# Nonconvergence for all-odd subtraction games

## Abstract

All-odd finite subtraction games have nonconvergent winning probabilities.

**Definition 1.1 (Legal subtractions).**

$$\forall S \in \operatorname{Finset}\left(\mathbb{N}\right),\; \forall n \in \mathbb{N},\; \operatorname{legalMoves}\left(S, n\right) = \operatorname{Finset}.\operatorname{filter}\left((\lambda (s:\mathbb{N})\mapsto(0 < s) \land (s \le n)), S\right)$$

*Formalization.* `D5/S3/Combinatorics/Games/CapitelliSommaAllOddNonconvergence.legalMoves` (`✓ std3`).

*Citation.* Nicolás Capitelli, Francisco Somma (2024). *On sequences arising from randomizing subtraction games*. DOI: [10.48550/arXiv.2405.19593](https://doi.org/10.48550/arXiv.2405.19593). URL: <https://arxiv.org/abs/2405.19593v1>.

*Commentary.*

Section 1, p. 2: “At a given position (number of chips in the pile) 0 ≤ m ≤ n, an element k′ ∈ {k ∈ S | k ≤ m} is randomly selected with equal probability, and the next player to move removes k′ chips from the pile.” The paper takes S to consist of positive integers. Here S is a finite set of natural numbers; the filter explicitly requires a positive subtraction and includes precisely those at most n.

**Definition 1.2 (Probability of winning).**

$$\forall S \in \operatorname{Finset}\left(\mathbb{N}\right),\; \forall n \in \mathbb{N},\; \operatorname{winProb}\left(S, n\right) = \operatorname{if} \operatorname{Finset}.\operatorname{Nonempty}\left(\operatorname{legalMoves}\left(S, n\right)\right) \operatorname{then} 1-\frac{\sum_{s \in \operatorname{Finset}.\operatorname{attach}\left(\operatorname{legalMoves}\left(S, n\right)\right)} \operatorname{winProb}\left(S, (n-\operatorname{val}\left(s\right))\right)}{(\operatorname{Finset}.\operatorname{card}\left(\operatorname{legalMoves}\left(S, n\right)\right):\mathbb{R})} \operatorname{else} 0$$

*Formalization.* `D5/S3/Combinatorics/Games/CapitelliSommaAllOddNonconvergence.winProb` (`✓ std3`).

*Citation.* Nicolás Capitelli, Francisco Somma (2024). *On sequences arising from randomizing subtraction games*. DOI: [10.48550/arXiv.2405.19593](https://doi.org/10.48550/arXiv.2405.19593). URL: <https://arxiv.org/abs/2405.19593v1>.

*Commentary.*

Section 1, p. 2: “The first player who is confronted with a position m for which {k ∈ S | k ≤ m} = ∅, loses.” The function winProb S n is the probability that the next player wins. It is zero without a legal move and otherwise one minus the uniform average of the follower probabilities. The sum uses attach, whose elements carry their membership proofs; val is the underlying natural number. Subtraction of natural indices is truncated subtraction. The cardinality is cast to the reals, and the displayed quotient is real division. Recursion terminates because each legal subtraction is positive.

**Definition 1.3 (The all-odd conjecture).**

$$claim = (\forall S \in \operatorname{Finset}\left(\mathbb{N}\right),\; (\operatorname{Finset}.\operatorname{Nonempty}\left(S\right)) \Rightarrow ((\forall s \in \mathbb{N},\; (s \in S) \Rightarrow (\operatorname{Odd}\left(s\right))) \Rightarrow ((\operatorname{Finset}.\operatorname{gcd}\left(S, \operatorname{id}\right) = 1) \Rightarrow (\neg(\exists L \in \mathbb{R},\; \operatorname{Filter}.\operatorname{Tendsto}\left((\lambda (n:\mathbb{N})\mapsto\operatorname{winProb}\left(S, n\right)), \operatorname{Filter}.\operatorname{atTop}, \operatorname{nhds}\left(L\right)\right))))))$$

*Formalization.* `D5/S3/Combinatorics/Games/CapitelliSommaAllOddNonconvergence.claim` (`✓ std3`).

*Citation.* Nicolás Capitelli, Francisco Somma (2024). *On sequences arising from randomizing subtraction games*. DOI: [10.48550/arXiv.2405.19593](https://doi.org/10.48550/arXiv.2405.19593). URL: <https://arxiv.org/abs/2405.19593v1>.

*Commentary.*

Section 3, p. 7: “However, we do not show that an all-odd subtraction set necesarily do not converge (although we conjeture it) nor we provide the exact limits of the even and odd subsequences for the (conjectured) non-convergent case.” The section assumes a finite nonempty subtraction set with gcd one. Odd natural numbers are positive, and nonconvergence means that no real limit exists.

**Theorem 1.4 (Every all-odd subtraction set fails to converge).**

$$\forall S \in \operatorname{Finset}\left(\mathbb{N}\right),\; (\operatorname{Finset}.\operatorname{Nonempty}\left(S\right)) \Rightarrow ((\forall s \in \mathbb{N},\; (s \in S) \Rightarrow (\operatorname{Odd}\left(s\right))) \Rightarrow ((\operatorname{Finset}.\operatorname{gcd}\left(S, \operatorname{id}\right) = 1) \Rightarrow (\neg(\exists L \in \mathbb{R},\; \operatorname{Filter}.\operatorname{Tendsto}\left((\lambda (n:\mathbb{N})\mapsto\operatorname{winProb}\left(S, n\right)), \operatorname{Filter}.\operatorname{atTop}, \operatorname{nhds}\left(L\right)\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Games/CapitelliSommaAllOddNonconvergence.result` (`✓ std3`). ∎

*Resolves.* `Problems/capitelli-somma-2024-all-odd-nonconvergence` (proved) by `D5/S3/Combinatorics/Games/CapitelliSommaAllOddNonconvergence.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"capitelli-somma-2024-all-odd-nonconvergence","declaration_gid":"D5/S3/Combinatorics/Games/CapitelliSommaAllOddNonconvergence.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Nicolás Capitelli, Francisco Somma (2024). *On sequences arising from randomizing subtraction games*. DOI: [10.48550/arXiv.2405.19593](https://doi.org/10.48550/arXiv.2405.19593). URL: <https://arxiv.org/abs/2405.19593v1>.

*Commentary.*

Put b(n)=(-1)^n(1-2 winProb S n) and d(n)=b(n)+b(n+1). Oddness makes b satisfy a positive averaging recurrence. At a newly legal subtraction, the change in the averaging denominator contributes b(n)+1, which is nonnegative since b(n) lies between minus one and one. Strong induction gives d(n) nonnegative, with d(m-1)=2 at the first legal move m=min S. For N at least max S, the finite sum over s in S and r<s of d(N-s+r) is conserved by telescoping and is at least two. Convergence of winProb would force d, and hence this finite sum, to tend to zero. This contradiction proves the proposition. The argument also applies without the gcd hypothesis. It does not determine the even and odd subsequence limits or the multiplicities of the characteristic roots.

## References

- Truth anchor: `D5/S3/Combinatorics/Games/CapitelliSommaAllOddNonconvergence.claim`
- Truth anchor: `D5/S3/Combinatorics/Games/CapitelliSommaAllOddNonconvergence.legalMoves`
- Truth anchor: `D5/S3/Combinatorics/Games/CapitelliSommaAllOddNonconvergence.result`
- Truth anchor: `D5/S3/Combinatorics/Games/CapitelliSommaAllOddNonconvergence.winProb`
