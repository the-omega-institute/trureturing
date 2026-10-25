# Kagey's Eventual Equality of Power-Sequence Minima

## Abstract

Prime-power sequence minima eventually equal the rational-relation minimum.

**Definition 1.1 (Admissible nondecreasing sequences).**

$$\forall n \in \mathrm{Nat},\; \forall k \in \mathrm{Nat},\; \forall m \in \mathrm{Nat},\; \forall b \in List\left(\mathrm{Nat}\right),\; Valid\left(n, k, m, b\right) \Leftrightarrow ((headOption\left(b\right) = some\left(k\right)) \land ((lastOption\left(b\right) = some\left(m\right)) \land ((\operatorname{List}.\operatorname{Pairwise}\left((\operatorname{fun} a d \mapsto a \le d), b\right)) \land ((\forall x \in \mathrm{Nat},\; (x \in b) \Rightarrow (\operatorname{List}.\operatorname{count}\left(x, b\right) < n)) \land (\exists c \in \mathbb{Z},\; (\operatorname{List}.\operatorname{prod}\left(b\right)) : \mathbb{Z} = c^{n})))))$$

*Formalization.* `D5/S3/Arith/Factorization/OeisA343825KageyPowerSequences.Valid` (`✓ std3`).

*Citation.* P. Kagey; OEIS Foundation Inc. (2021). *OEIS A343825, prime-power sequence minima and A071537*. URL: <https://oeis.org/A343825>.

*Commentary.*

Table read by antidiagonals upward: T(n,k) is the least m such that there exists a sequence k = b_1 <= b_2 <= ... <= b_t = m such that no term appears n or more times and the product of the sequence is of the form c^n, where c is an integer; n >= 1 and k >= 0. (OEIS A343825, NAME, revision 22; unpaginated.) The sequence is a list of natural numbers. Optional heads and last elements below are written headOption and lastOption; they denote `List.head?` and `List.getLast?`. Pairwise uses the natural order. The count of each member is strictly below n, and the natural product, cast to the integers, is an integer nth power.

**Definition 1.2 (The least power-sequence endpoint).**

$$\forall n \in \mathrm{Nat},\; \forall k \in \mathrm{Nat},\; T\left(n, k\right) = (\operatorname{if} h : (\exists m \in \mathrm{Nat},\; \exists b \in List\left(\mathrm{Nat}\right),\; Valid\left(n, k, m, b\right)) \operatorname{then} \operatorname{Nat}.\operatorname{find}\left(h\right) \operatorname{else} 0)$$

*Formalization.* `D5/S3/Arith/Factorization/OeisA343825KageyPowerSequences.T` (`✓ std3`).

*Citation.* P. Kagey; OEIS Foundation Inc. (2021). *OEIS A343825, prime-power sequence minima and A071537*. URL: <https://oeis.org/A343825>.

*Commentary.*

Table read by antidiagonals upward: T(n,k) is the least m such that there exists a sequence k = b_1 <= b_2 <= ... <= b_t = m such that no term appears n or more times and the product of the sequence is of the form c^n, where c is an integer; n >= 1 and k >= 0. (OEIS A343825, NAME, revision 22; unpaginated.) Nat.find selects the least natural endpoint with an admissible sequence. The value is extended by zero if there is no endpoint.

**Definition 1.3 (An integer-exponent relation).**

$$\forall k \in \mathrm{Nat},\; \forall m \in \mathrm{Nat},\; Relation\left(k, m\right) \Leftrightarrow (\exists e \in \mathrm{Nat} \to \mathbb{Z},\; (e\left(k\right) \ne 0) \land (\prod_{j \in \operatorname{Finset}.\operatorname{Icc}\left(k, m\right)} ((j) : \mathbb{Q})^{e\left(j\right)} = 1))$$

*Formalization.* `D5/S3/Arith/Factorization/OeisA343825KageyPowerSequences.Relation` (`✓ std3`).

*Citation.* P. Kagey; OEIS Foundation Inc. (2021). *OEIS A343825, prime-power sequence minima and A071537*. URL: <https://oeis.org/A343825>.

*Commentary.*

Least integer m >= n such that there exist integers k_n, k_n+1, ..., k_m with nonzero k_n, for which n^(k_n) * (n+1)^(k_n+1) * ... * m^(k_m) = 1. (OEIS A071537, NAME; unpaginated.) The source's starting index n is written k. Exponents are integers; the finite product is taken in the rationals over the closed natural interval from k to m. The first exponent must be nonzero.

**Definition 1.4 (The least relation endpoint).**

$$\forall k \in \mathrm{Nat},\; A071537\left(k\right) = (\operatorname{if} h : (\exists m \in \mathrm{Nat},\; (k \le m) \land (Relation\left(k, m\right))) \operatorname{then} \operatorname{Nat}.\operatorname{find}\left(h\right) \operatorname{else} 0)$$

*Formalization.* `D5/S3/Arith/Factorization/OeisA343825KageyPowerSequences.A071537` (`✓ std3`).

*Citation.* P. Kagey; OEIS Foundation Inc. (2021). *OEIS A343825, prime-power sequence minima and A071537*. URL: <https://oeis.org/A343825>.

*Commentary.*

Least integer m >= n such that there exist integers k_n, k_n+1, ..., k_m with nonzero k_n, for which n^(k_n) * (n+1)^(k_n+1) * ... * m^(k_m) = 1. (OEIS A071537, NAME; unpaginated.) Nat.find selects the least m at least k carrying such a relation. The value is extended by zero if there is no endpoint. A071537 has offset one.

**Definition 1.5 (The eventual-equality conjecture).**

$$claim \Leftrightarrow (\forall k \in \mathrm{Nat},\; (1 \le k) \Rightarrow (\exists N \in \mathrm{Nat},\; \forall p \in \mathrm{Nat},\; (\operatorname{Nat}.\operatorname{Prime}\left(p\right)) \Rightarrow ((N \le p) \Rightarrow (T\left(p, k\right) = A071537\left(k\right)))))$$

*Formalization.* `D5/S3/Arith/Factorization/OeisA343825KageyPowerSequences.claim` (`✓ std3`).

*Citation.* P. Kagey; OEIS Foundation Inc. (2021). *OEIS A343825, prime-power sequence minima and A071537*. URL: <https://oeis.org/A343825>.

*Commentary.*

Conjecture: T(p,k) = A071537(k) for fixed k and sufficiently large prime p. (OEIS A343825, COMMENT, revision 22; unpaginated.) For each natural k at least one, a threshold N works for every prime p at least N.

**Theorem 1.6 (Equality for all sufficiently large primes).**

$$\forall k \in \mathrm{Nat},\; (1 \le k) \Rightarrow (\exists N \in \mathrm{Nat},\; \forall p \in \mathrm{Nat},\; (\operatorname{Nat}.\operatorname{Prime}\left(p\right)) \Rightarrow ((N \le p) \Rightarrow (T\left(p, k\right) = A071537\left(k\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Factorization/OeisA343825KageyPowerSequences.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a343825-kagey-power-sequences` (proved) by `D5/S3/Arith/Factorization/OeisA343825KageyPowerSequences.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a343825-kagey-power-sequences","declaration_gid":"D5/S3/Arith/Factorization/OeisA343825KageyPowerSequences.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* P. Kagey; OEIS Foundation Inc. (2021). *OEIS A343825, prime-power sequence minima and A071537*. URL: <https://oeis.org/A343825>.

*Commentary.*

Fix k at least one and let m be its least rational-relation endpoint. Such an endpoint exists because the factorization vector of k times k+1 is the sum of the two factorization vectors. Reducing relation exponents modulo a sufficiently large prime gives multiplicities below that prime and a positive multiplicity at k. Sorting the replicated entries gives an admissible list whose endpoint is at most m. A rational prime-power root of a natural number has denominator one, so the root is an integer.

For each earlier endpoint, rational linear separation supplies an integer functional that vanishes at all later factorization vectors and is nonzero at k. A prime larger than the absolute value of its value at k cannot divide that value. Prime divisibility would therefore force the positive multiplicity at k to be at least the prime, a contradiction. The maximum of these finitely many thresholds and the upper threshold proves the equality, including k=1. The argument leaves an explicit threshold, a characterization of exceptional primes, and the separate prime-row permutation assertion open.

## References

- Truth anchor: `D5/S3/Arith/Factorization/OeisA343825KageyPowerSequences.A071537`
- Truth anchor: `D5/S3/Arith/Factorization/OeisA343825KageyPowerSequences.Relation`
- Truth anchor: `D5/S3/Arith/Factorization/OeisA343825KageyPowerSequences.T`
- Truth anchor: `D5/S3/Arith/Factorization/OeisA343825KageyPowerSequences.Valid`
- Truth anchor: `D5/S3/Arith/Factorization/OeisA343825KageyPowerSequences.claim`
- Truth anchor: `D5/S3/Arith/Factorization/OeisA343825KageyPowerSequences.result`
- Dependency: [D5/S3/Factorization/Embeddings/RationalValuationRecovery](../../Factorization/Embeddings/RationalValuationRecovery.md)
