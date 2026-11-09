# Refutation of the prefix-reversal triple count asymptotic

## Abstract

A congruence sieve gives a quadratic upper bound strictly below the proposed coefficient at degrees divisible by four.

**Definition 1.1 (Number of generating pairs).**

$$\forall n \in \mathbb{N},\; \operatorname{f}\left(n\right) = \operatorname{Nat}.\operatorname{card}\left((\{p: \operatorname{Fin}\left(n\right)\times\operatorname{Fin}\left(n\right) // 2 \le \operatorname{val}\left(p.2\right) \land \left(\operatorname{val}\left(p.2\right) < \operatorname{val}\left(p.1\right) \land \operatorname{PrefixReversalTripleOddNonGeneration}.\operatorname{tripleSubgroup}\left(n, \operatorname{val}\left(p.1\right), \operatorname{val}\left(p.2\right)\right) = \operatorname{Top}.\operatorname{top}\right)\})\right)$$

*Formalization.* `D5/S0/CayleyGrowth/PrefixReversalTripleCountRefutation.f` (`✓ std3`).

*Citation.* Saúl A. Blanco, Mikhail P. Golubyatnikov, Elena V. Konstantinova, Natalia V. Maslova, Luka A. Nikiforov (2026). *Generating the symmetric group by three prefix reversals*. DOI: [10.46298/dmtcs.16975](https://doi.org/10.46298/dmtcs.16975). URL: <https://arxiv.org/abs/2511.16959v3>.

*Commentary.*

Conjecture 1, page 17: “Let f(n) be the number of pairs (m,k) such that 2 ≤ k < m < n and ⟨rₙ, rₘ, rₖ⟩ = Symₙ. Then f(n) = { (1/13)n² + O(n), n = 0 (mod 4); (1/9)n² + O(n), n = 1 (mod 4); (1/10)n² + O(n), n = 2 (mod 4); (1/7)n² + O(n), n = 3 (mod 4). }” The source positions j in {1,...,n} correspond to i = j - 1 in Fin n. The permutation prefixReversal of length L sends i < L to L - 1 - i and fixes the other indices. The subgroup tripleSubgroup is the closure of exactly the three reversals. The coordinates p.1 and p.2 are m and k. Their strict ordering counts each pair once. The two proofs of length at most n are supplied by the Fin bounds.

**Definition 1.2 (The four proposed coefficients).**

$$\forall q \in \operatorname{Fin}\left(4\right),\; \operatorname{leadingCoefficient}\left(q\right) = \operatorname{match} \operatorname{val}\left(q\right) \operatorname{with} \begin{aligned}0 \mapsto \frac{1}{13}\\1 \mapsto \frac{1}{9}\\2 \mapsto \frac{1}{10}\\\operatorname{otherwise} \mapsto \frac{1}{7}\end{aligned}$$

*Formalization.* `D5/S0/CayleyGrowth/PrefixReversalTripleCountRefutation.leadingCoefficient` (`✓ std3`).

*Citation.* Saúl A. Blanco, Mikhail P. Golubyatnikov, Elena V. Konstantinova, Natalia V. Maslova, Luka A. Nikiforov (2026). *Generating the symmetric group by three prefix reversals*. DOI: [10.46298/dmtcs.16975](https://doi.org/10.46298/dmtcs.16975). URL: <https://arxiv.org/abs/2511.16959v3>.

*Commentary.*

Conjecture 1, page 17: “Let f(n) be the number of pairs (m,k) such that 2 ≤ k < m < n and ⟨rₙ, rₘ, rₖ⟩ = Symₙ. Then f(n) = { (1/13)n² + O(n), n = 0 (mod 4); (1/9)n² + O(n), n = 1 (mod 4); (1/10)n² + O(n), n = 2 (mod 4); (1/7)n² + O(n), n = 3 (mod 4). }” These are real quotients. The last branch of the match is used for q.val = 3 because q : Fin 4.

**Definition 1.3 (Conjecture 1 with all asymptotic quantifiers).**

$$claim = (\forall q \in \operatorname{Fin}\left(4\right),\; \exists C \in \mathbb{R},\; 0 \le C \land \left(\exists N \in \mathbb{N},\; \forall n \in \mathbb{N},\; N \le n \Rightarrow \left(n \bmod 4 = \operatorname{val}\left(q\right) \Rightarrow \left|(\operatorname{f}\left(n\right): \mathbb{R}) - \operatorname{leadingCoefficient}\left(q\right) \cdot (n: \mathbb{R})^{2}\right| \le C \cdot (n: \mathbb{R})\right)\right))$$

*Formalization.* `D5/S0/CayleyGrowth/PrefixReversalTripleCountRefutation.claim` (`✓ std3`).

*Citation.* Saúl A. Blanco, Mikhail P. Golubyatnikov, Elena V. Konstantinova, Natalia V. Maslova, Luka A. Nikiforov (2026). *Generating the symmetric group by three prefix reversals*. DOI: [10.46298/dmtcs.16975](https://doi.org/10.46298/dmtcs.16975). URL: <https://arxiv.org/abs/2511.16959v3>.

*Commentary.*

Conjecture 1, page 17: “Let f(n) be the number of pairs (m,k) such that 2 ≤ k < m < n and ⟨rₙ, rₘ, rₖ⟩ = Symₙ. Then f(n) = { (1/13)n² + O(n), n = 0 (mod 4); (1/9)n² + O(n), n = 1 (mod 4); (1/10)n² + O(n), n = 2 (mod 4); (1/7)n² + O(n), n = 3 (mod 4). }” For each residue q, one nonnegative real C and one natural threshold N must work for every subsequent n in that residue. The operation n % 4 is the natural remainder, and the absolute value and polynomial are real.

**Theorem 1.4 (The four-clause asymptotic is false).**

$$\neg (\forall q \in \operatorname{Fin}\left(4\right),\; \exists C \in \mathbb{R},\; 0 \le C \land \left(\exists N \in \mathbb{N},\; \forall n \in \mathbb{N},\; N \le n \Rightarrow \left(n \bmod 4 = \operatorname{val}\left(q\right) \Rightarrow \left|(\operatorname{f}\left(n\right): \mathbb{R}) - \operatorname{leadingCoefficient}\left(q\right) \cdot (n: \mathbb{R})^{2}\right| \le C \cdot (n: \mathbb{R})\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S0/CayleyGrowth/PrefixReversalTripleCountRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/prefix-reversal-triple-count` (refuted) by `D5/S0/CayleyGrowth/PrefixReversalTripleCountRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"prefix-reversal-triple-count","declaration_gid":"D5/S0/CayleyGrowth/PrefixReversalTripleCountRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Saúl A. Blanco, Mikhail P. Golubyatnikov, Elena V. Konstantinova, Natalia V. Maslova, Luka A. Nikiforov (2026). *Generating the symmetric group by three prefix reversals*. DOI: [10.46298/dmtcs.16975](https://doi.org/10.46298/dmtcs.16975). URL: <https://arxiv.org/abs/2511.16959v3>.

*Commentary.*

For n divisible by four, generation forces m + k ≥ n, opposite parities for m and k, and at least one of m and k to have residue two or three modulo four. For every integer p with 3 ≤ p ≤ n, the simultaneous congruences m ≡ k ≡ n modulo p would preserve the proper nonempty set of positions with i ≡ 0 or i + 1 ≡ n modulo p. Apply these exclusions at p = 3, 5, 7, 11, 13, 17, 19. The Chinese remainder theorem leaves 115579079884800 pairs of residues modulo 19399380. In each residue pair a finite lattice estimate bounds four times the squared modulus times the number of pairs by (n + 38798760)². Thus f(n) ≤ (1146617856/14933966047)n² + 58198140n for every n ≥ 19399380 divisible by four. The difference 1/13 - 1146617856/14933966047 is the positive number 2148763/14933966047. Its quadratic contribution exceeds every proposed linear error along sufficiently large multiples of four. The other three residue assertions, the exact limiting coefficient, the existence of a limit and a matching lower bound remain open. The argument gives necessary conditions for generation and does not assert their sufficiency.

## References

- Truth anchor: `D5/S0/CayleyGrowth/PrefixReversalTripleCountRefutation.claim`
- Truth anchor: `D5/S0/CayleyGrowth/PrefixReversalTripleCountRefutation.f`
- Truth anchor: `D5/S0/CayleyGrowth/PrefixReversalTripleCountRefutation.leadingCoefficient`
- Truth anchor: `D5/S0/CayleyGrowth/PrefixReversalTripleCountRefutation.result`
- Dependency: [D5/S0/CayleyGrowth/PrefixReversalTripleEvenNonGeneration](PrefixReversalTripleEvenNonGeneration.md)
- Dependency: [D5/S0/CayleyGrowth/PrefixReversalTripleOddNonGeneration](PrefixReversalTripleOddNonGeneration.md)
