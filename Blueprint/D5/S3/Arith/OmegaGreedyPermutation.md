# A363956 is a permutation

## Abstract

The greedy sequence A363956 is a permutation of the positive integers.

All variables are natural numbers. omega(x) counts distinct prime factors. prime(r) is the (r+1)-st prime, with prime(0)=2. The tail state starts at (2,{1,2}). Its next term is the natural infimum of positive unused multiples of prime(omega(current)-1), which is then inserted into the used set. seq(1)=1 and seq(n+2) reads tail term n. The auxiliary index 0 is 1. No coverage assumption occurs in this definition.

**Theorem 1.1 (The prescribed seeds).**

$$\operatorname{seq}\left(1\right) = 1 \land \operatorname{seq}\left(2\right) = 2$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/OmegaGreedyPermutation.sequence_initial` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Scott R. Shannon (2023). *OEIS A363956 — least unused multiples indexed by distinct prime factors*. URL: <https://oeis.org/A363956>.

*Commentary.*

The two seed values follow from the initial state and the index convention.

**Theorem 1.2 (Every term is positive).**

$$\forall n \in \mathbb{N}, 0 < \operatorname{seq}\left(n\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/OmegaGreedyPermutation.sequence_positive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Scott R. Shannon (2023). *OEIS A363956 — least unused multiples indexed by distinct prime factors*. URL: <https://oeis.org/A363956>.

*Commentary.*

For a positive queue prime p and a finite used set U, the multiple p times (max(U)+1) is positive and outside U. Thus the candidate set is nonempty and its infimum belongs to it. Every tail term is at least 2.

**Theorem 1.3 (Positive indices have distinct values).**

$$\forall i \in \mathbb{N}, \forall j \in \mathbb{N}, 0 < i \implies 0 < j \implies \operatorname{seq}\left(i\right) = \operatorname{seq}\left(j\right) \implies i = j$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/OmegaGreedyPermutation.sequence_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Scott R. Shannon (2023). *OEIS A363956 — least unused multiples indexed by distinct prime factors*. URL: <https://oeis.org/A363956>.

*Commentary.*

The stored history contains every previous tail term. The next minimum lies outside that history, so tail indices have distinct values. All tail terms are at least 2, separating them from the initial 1.

**Theorem 1.4 (The original minimum rule).**

$$\forall k \in \mathbb{N}, \operatorname{seq}\left(k + 3\right) = \operatorname{sInf}\left(\operatorname{candidates}\left(k\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/OmegaGreedyPermutation.sequence_greedy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Scott R. Shannon (2023). *OEIS A363956 — least unused multiples indexed by distinct prime factors*. URL: <https://oeis.org/A363956>.

*Commentary.*

candidates(k) is exactly the set of positive y different from seq(i+1) for every 0<=i<k+2, and divisible by prime(omega(seq(k+2))-1). Induction identifies the stored used set with those prior terms, so the displayed equality is the original smallest-unused rule.

**Theorem 1.5 (Every positive integer occurs).**

$$\forall m \in \mathbb{N}, 0 < m \implies \exists n \in \mathbb{N}, 0 < n \land \operatorname{seq}\left(n\right) = m$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/OmegaGreedyPermutation.a363956_surjective` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a363956-positive-permutation` (proved) by `D5/S3/Arith/OmegaGreedyPermutation.a363956_surjective`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a363956-positive-permutation","declaration_gid":"D5/S3/Arith/OmegaGreedyPermutation.a363956_surjective","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Scott R. Shannon (2023). *OEIS A363956 — least unused multiples indexed by distinct prime factors*. URL: <https://oeis.org/A363956>.

*Commentary.*

If a prime queue is selected infinitely often, each positive multiple appears: otherwise that missing multiple bounds infinitely many distinct outputs in a finite interval. Suppose queue 2 is selected only finitely often. Every prime output has omega=1 and selects queue 2, so only finitely many primes are output. Any selected prime has already appeared or is the next minimum itself. Thus the selected queues form a finite set, as do the omega values by injectivity of prime enumeration. Some queue is selected infinitely often, but its multiples have arbitrarily many distinct prime factors, a contradiction. Queue 2 therefore exhausts all positive even numbers. For each r, multiply the product of the first r+1 primes by successive positive powers of 2: these are distinct even numbers with exactly r+1 prime factors. Their occurrence forces infinitely many selections of prime(r). Every integer greater than 1 has a prime divisor, whose queue outputs it. The seed supplies 1.

## References

- Truth anchor: `D5/S3/Arith/OmegaGreedyPermutation.a363956_surjective`
- Truth anchor: `D5/S3/Arith/OmegaGreedyPermutation.sequence_greedy`
- Truth anchor: `D5/S3/Arith/OmegaGreedyPermutation.sequence_initial`
- Truth anchor: `D5/S3/Arith/OmegaGreedyPermutation.sequence_injective`
- Truth anchor: `D5/S3/Arith/OmegaGreedyPermutation.sequence_positive`
