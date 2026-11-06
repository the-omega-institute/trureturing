# Minimum Length of a Two-Dense Divisor Block

## Abstract

The first maximal two-dense divisor block has minimum cardinality.

Omar E. Pol's OEIS A401248 Conjecture 1 asserts a(n)=A384222(n,1). The complete increasing list contains every positive divisor once. Adjacent a,b remain joined when b is at most twice a; only a strict excess splits them. All positive integers are included. At n=1 the sole block is the singleton containing one. No squarefree, parity or finite cutoff assumption enters the statement.

The dense/rough divisor decomposition is prior mathematics: Weingartner, arXiv:1405.2585v3, Lemma 3 with theta(u)=2u and the t-dense characterization on pages 2-3. Here one chooses a largest interval-dense divisor instead of introducing an ordered prime-power prefix as an additional representation. Tenenbaum's 1986 Lemma 2.2 gives the consecutive-divisor ratio characterization.

**Definition 1.1 (The actual maximal blocks).**

$$\forall n: \mathbb{N}, \operatorname{divisorBlocks}(n) = \operatorname{splitBy}((a,b \mapsto \operatorname{decide}(b \le 2\cdot a)), \operatorname{map}(\operatorname{fst}, \operatorname{divisorsAntidiagonalList}(n)))$$

*Formalization.* `D5/S3/Factorization/TwoDenseDivisorBlockMinimum.divisorBlocks` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Use the same complete divisor list and splitBy predicate as the existing palindromic row. Equality at ratio two stays connected.

**Definition 1.2 (The unrestricted event).**

$$\forall n: \mathbb{N}, 0 < n \implies \forall B \in \operatorname{divisorBlocks}(n), \operatorname{headD}(\operatorname{row}(n), 0) \le \operatorname{length}(B)$$

*Formalization.* `D5/S3/Factorization/TwoDenseDivisorBlockMinimum.claim` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every positive n, compare the first row entry with the length of each actual maximal block. Positive n guarantees a nonempty list; the headD zero default adds no premise or cutoff.

**Theorem 1.3 (A full dense copy in each block).**

$$\forall u,v: \mathbb{N}, 0<u \land 0<v \land \operatorname{Coprime}(u, v) \land \operatorname{IsChain}(\operatorname{map}(\operatorname{fst}, \operatorname{divisorsAntidiagonalList}(u)), (a,b \mapsto b \le 2\cdot a)) \implies \forall B \in \operatorname{divisorBlocks}(u\cdot v), \operatorname{card}(\operatorname{divisors}(u)) \le \operatorname{length}(B)$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/TwoDenseDivisorBlockMinimum.block_card_ge_of_dense_factor` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume positive coprime u,v and a dense divisor list for u. For any member d of a block of uv, write d=gcd(d,u)gcd(d,v). Multiplying the whole divisor list of u by gcd(d,v) gives a dense list of divisors of uv containing d. Strict full-list gaps cannot split that copy. Cancellation makes the map injective, so its cardinality bounds the block length below. The separation argument is extracted from the theorem-local connectivity proof in TwoDenseDivisorBlockMaximum.

**Theorem 1.4 (The dense and rough factors).**

$$\forall u,v: \mathbb{N}, 0<u \land 0<v \land \operatorname{Coprime}(u, v) \land \operatorname{IsChain}(\operatorname{map}(\operatorname{fst}, \operatorname{divisorsAntidiagonalList}(u)), (a,b \mapsto b \le 2\cdot a)) \land (\forall p, \operatorname{Prime}(p) \land \operatorname{dvd}(p, v) \implies 2\cdot u < p) \implies \forall B \in \operatorname{divisorBlocks}(u\cdot v), \operatorname{headD}(\operatorname{row}(u\cdot v), 0) \le \operatorname{length}(B)$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/TwoDenseDivisorBlockMinimum.first_block_min_of_dense_factor` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If every prime dividing v exceeds 2u, every divisor outside D(u) also exceeds 2u. Sortedness and splitBy's exact append law identify D(u) as the first block. Its length is tau(u), and the copy bound applies to every other block.

**Theorem 1.5 (The first block is minimal).**

$$\forall n: \mathbb{N}, 0 < n \implies \forall B \in \operatorname{divisorBlocks}(n), \operatorname{headD}(\operatorname{row}(n), 0) \le \operatorname{length}(B)$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/TwoDenseDivisorBlockMinimum.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a401248-first-two-dense-divisor-block-minimum` (proved) by `D5/S3/Factorization/TwoDenseDivisorBlockMinimum.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a401248-first-two-dense-divisor-block-minimum","declaration_gid":"D5/S3/Factorization/TwoDenseDivisorBlockMinimum.result","resolution_kind":"proved"} -->

*Citation.* Omar E. Pol (2026). *OEIS A401248, minimum length of a two-dense divisor block*. URL: <https://oeis.org/A401248>.

*Commentary.*

Integer interval density means that for each positive x<u there is a divisor d with x<d<=2x. It is preserved on multiplying u by any positive p<=2u: use an old divisor when x<u, use p when u<=x<p, and otherwise scale a divisor above floor(x/p). Choose the largest interval-dense divisor u of n, which exists because one qualifies. Any prime p dividing n/u must exceed 2u, since otherwise up would be a larger qualifying divisor. Such a prime cannot divide u, so u and n/u are coprime. Interval coverage implies the actual sorted divisor list has no ratio exceeding two. Apply the dense/rough factor theorem to obtain the exact all-positive-n event.

## References

- Truth anchor: `D5/S3/Factorization/TwoDenseDivisorBlockMinimum.block_card_ge_of_dense_factor`
- Truth anchor: `D5/S3/Factorization/TwoDenseDivisorBlockMinimum.claim`
- Truth anchor: `D5/S3/Factorization/TwoDenseDivisorBlockMinimum.divisorBlocks`
- Truth anchor: `D5/S3/Factorization/TwoDenseDivisorBlockMinimum.first_block_min_of_dense_factor`
- Truth anchor: `D5/S3/Factorization/TwoDenseDivisorBlockMinimum.result`
- Dependency: [D5/S3/Factorization/TwoDenseDivisorBlocksPalindrome](TwoDenseDivisorBlocksPalindrome.md)
