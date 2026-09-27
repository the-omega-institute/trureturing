# Cohen's Consecutive-Cube Prime-Pair Thresholds

## Abstract

The printed thresholds in Cohen's Conjectures 28 and 29 fail at n = 11 and n = 12.

**Definition 1.1 (Twin-prime pairs between consecutive cubes).**

$$\forall n \in \mathrm{Nat},\; \operatorname{twinPairCount}\left(n\right): \mathrm{Nat} = Finset.card\left(Finset.filter\left(Finset.Ico\left(n^{3} + 1, (n + 1)^{3}\right), (\lambda p \mapsto (p + 2 < (n + 1)^{3}) \land \left((Nat.Prime\left(p\right)) \land (Nat.Prime\left(p + 2\right))\right))\right)\right)$$

*Formalization.* `D5/S0/Certificates/CohenConsecutiveCubePrimePairThresholdRefutation.twinPairCount` (`✓ std3`).

*Citation.* Joel E. Cohen (2025). *Conjectures about Primes and Cyclic Numbers*. DOI: [10.48550/arXiv.2508.08335](https://doi.org/10.48550/arXiv.2508.08335). URL: <https://cs.uwaterloo.ca/journals/JIS/VOL28/Cohen/cohen41.pdf>.

*Commentary.*

For each natural n, the half-open finite interval starts at n^3 + 1. The filter retains exactly the p for which n^3 < p, p + 2 < (n+1)^3, and both p and p + 2 are prime; its cardinality is twinPairCount(n).

**Definition 1.2 (Cousin-prime pairs between consecutive cubes).**

$$\forall n \in \mathrm{Nat},\; \operatorname{cousinPairCount}\left(n\right): \mathrm{Nat} = Finset.card\left(Finset.filter\left(Finset.Ico\left(n^{3} + 1, (n + 1)^{3}\right), (\lambda p \mapsto (p + 4 < (n + 1)^{3}) \land \left((Nat.Prime\left(p\right)) \land \left((Nat.Prime\left(p + 4\right)) \land \left((\neg Nat.Prime\left(p + 1\right)) \land \left((\neg Nat.Prime\left(p + 2\right)) \land (\neg Nat.Prime\left(p + 3\right))\right)\right)\right)\right))\right)\right)$$

*Formalization.* `D5/S0/Certificates/CohenConsecutiveCubePrimePairThresholdRefutation.cousinPairCount` (`✓ std3`).

*Citation.* Joel E. Cohen (2025). *Conjectures about Primes and Cyclic Numbers*. DOI: [10.48550/arXiv.2508.08335](https://doi.org/10.48550/arXiv.2508.08335). URL: <https://cs.uwaterloo.ca/journals/JIS/VOL28/Cohen/cohen41.pdf>.

*Commentary.*

For each natural n, the filter requires n^3 < p and p + 4 < (n+1)^3. It also requires p and p + 4 to be prime and p + 1, p + 2, and p + 3 not to be prime, so the endpoint primes are consecutive.

**Definition 1.3 (Conjecture 28).**

$$(claim28) \Leftrightarrow ((\forall n \in \mathrm{Nat},\; (1 \le n) \Rightarrow (2 \le \operatorname{twinPairCount}\left(n\right))) \land \left((\forall k \in \mathrm{Nat},\; (1 \le k) \Rightarrow (\exists N \in \mathrm{Nat},\; \forall n \in \mathrm{Nat},\; (N \le n) \Rightarrow (k \le \operatorname{twinPairCount}\left(n\right)))) \land \left((\forall n \in \mathrm{Nat},\; (1 \le n) \Rightarrow (1 \le \operatorname{twinPairCount}\left(n\right))) \land \left((\forall n \in \mathrm{Nat},\; (1 \le n) \Rightarrow (2 \le \operatorname{twinPairCount}\left(n\right))) \land \left((\forall n \in \mathrm{Nat},\; (3 \le n) \Rightarrow (3 \le \operatorname{twinPairCount}\left(n\right))) \land \left((\forall n \in \mathrm{Nat},\; (5 \le n) \Rightarrow (4 \le \operatorname{twinPairCount}\left(n\right))) \land \left((\forall n \in \mathrm{Nat},\; (8 \le n) \Rightarrow (5 \le \operatorname{twinPairCount}\left(n\right))) \land \left((\forall n \in \mathrm{Nat},\; (10 \le n) \Rightarrow (6 \le \operatorname{twinPairCount}\left(n\right))) \land \left((\forall n \in \mathrm{Nat},\; (10 \le n) \Rightarrow (7 \le \operatorname{twinPairCount}\left(n\right))) \land \left((\forall n \in \mathrm{Nat},\; (10 \le n) \Rightarrow (8 \le \operatorname{twinPairCount}\left(n\right))) \land \left((\forall n \in \mathrm{Nat},\; (10 \le n) \Rightarrow (9 \le \operatorname{twinPairCount}\left(n\right))) \land \left((\forall n \in \mathrm{Nat},\; (11 \le n) \Rightarrow (10 \le \operatorname{twinPairCount}\left(n\right))) \land \left((\forall n \in \mathrm{Nat},\; (13 \le n) \Rightarrow (11 \le \operatorname{twinPairCount}\left(n\right))) \land \left((\forall n \in \mathrm{Nat},\; (15 \le n) \Rightarrow (12 \le \operatorname{twinPairCount}\left(n\right))) \land \left((\forall n \in \mathrm{Nat},\; (15 \le n) \Rightarrow (13 \le \operatorname{twinPairCount}\left(n\right))) \land \left((\forall n \in \mathrm{Nat},\; (15 \le n) \Rightarrow (14 \le \operatorname{twinPairCount}\left(n\right))) \land \left((\forall n \in \mathrm{Nat},\; (15 \le n) \Rightarrow (15 \le \operatorname{twinPairCount}\left(n\right))) \land \left((\forall n \in \mathrm{Nat},\; (15 \le n) \Rightarrow (16 \le \operatorname{twinPairCount}\left(n\right))) \land (\forall n \in \mathrm{Nat},\; (20 \le n) \Rightarrow (17 \le \operatorname{twinPairCount}\left(n\right)))\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right))$$

*Formalization.* `D5/S0/Certificates/CohenConsecutiveCubePrimePairThresholdRefutation.claim28` (`✓ std3`).

*Citation.* Joel E. Cohen (2025). *Conjectures about Primes and Cyclic Numbers*. DOI: [10.48550/arXiv.2508.08335](https://doi.org/10.48550/arXiv.2508.08335). URL: <https://cs.uwaterloo.ca/journals/JIS/VOL28/Cohen/cohen41.pdf>.

*Commentary.*

The paper states: "Conjecture 28 (number of twin primes between consecutive cubes). For every n ∈ N, the number of pairs of twin primes between n³ and (n + 1)³ is never less than two. More generally, for every k ∈ N, there exists N(k) ∈ N such that for all n ≥ N(k) there are at least k pairs of twin primes between n³ and (n + 1)³. Specifically, N(1) = N(2) = 1, N(3) = 3, N(4) = 5, N(5) = 8, N(6) = N(7) = N(8) = N(9) = 10, N(10) = 11, N(11) = 13, N(12) = N(13) = N(14) = N(15) = N(16) = 15, and N(17) = 20." Each printed threshold is represented as its own universal conjunct. The existential N ranges over natural numbers; adding 1 ≤ N would strengthen that unused conjunct and does not affect the refutation.

**Definition 1.4 (Conjecture 29).**

$$(claim29) \Leftrightarrow ((\forall n \in \mathrm{Nat},\; (2 \le n) \Rightarrow (2 \le \operatorname{cousinPairCount}\left(n\right))) \land \left((\forall k \in \mathrm{Nat},\; (1 \le k) \Rightarrow (\exists N \in \mathrm{Nat},\; \forall n \in \mathrm{Nat},\; (N \le n) \Rightarrow (k \le \operatorname{cousinPairCount}\left(n\right)))) \land \left((\forall n \in \mathrm{Nat},\; (2 \le n) \Rightarrow (1 \le \operatorname{cousinPairCount}\left(n\right))) \land \left((\forall n \in \mathrm{Nat},\; (2 \le n) \Rightarrow (2 \le \operatorname{cousinPairCount}\left(n\right))) \land \left((\forall n \in \mathrm{Nat},\; (8 \le n) \Rightarrow (3 \le \operatorname{cousinPairCount}\left(n\right))) \land \left((\forall n \in \mathrm{Nat},\; (9 \le n) \Rightarrow (4 \le \operatorname{cousinPairCount}\left(n\right))) \land \left((\forall n \in \mathrm{Nat},\; (9 \le n) \Rightarrow (5 \le \operatorname{cousinPairCount}\left(n\right))) \land \left((\forall n \in \mathrm{Nat},\; (9 \le n) \Rightarrow (6 \le \operatorname{cousinPairCount}\left(n\right))) \land \left((\forall n \in \mathrm{Nat},\; (9 \le n) \Rightarrow (7 \le \operatorname{cousinPairCount}\left(n\right))) \land \left((\forall n \in \mathrm{Nat},\; (12 \le n) \Rightarrow (8 \le \operatorname{cousinPairCount}\left(n\right))) \land \left((\forall n \in \mathrm{Nat},\; (12 \le n) \Rightarrow (9 \le \operatorname{cousinPairCount}\left(n\right))) \land (\forall n \in \mathrm{Nat},\; (12 \le n) \Rightarrow (10 \le \operatorname{cousinPairCount}\left(n\right)))\right)\right)\right)\right)\right)\right)\right)\right)\right)\right))$$

*Formalization.* `D5/S0/Certificates/CohenConsecutiveCubePrimePairThresholdRefutation.claim29` (`✓ std3`).

*Citation.* Joel E. Cohen (2025). *Conjectures about Primes and Cyclic Numbers*. DOI: [10.48550/arXiv.2508.08335](https://doi.org/10.48550/arXiv.2508.08335). URL: <https://cs.uwaterloo.ca/journals/JIS/VOL28/Cohen/cohen41.pdf>.

*Commentary.*

The paper states: "Conjecture 29 (number of cousin primes between consecutive cubes). For n ∈ N with n > 1, the number of pairs of cousin primes between n³ and (n + 1)³ is never less than two. More generally, for every k ∈ N, there exists N(k) ∈ N such that, for all n ≥ N(k), there are at least k pairs of cousin primes between n³ and (n + 1)³. Specifically, N(1) = N(2) = 2, N(3) = 8, N(4) = N(5) = N(6) = N(7) = 9, N(8) = N(9) = N(10) = 12." Each printed threshold is represented as its own universal conjunct. The existential N ranges over natural numbers; adding 1 ≤ N would strengthen that unused conjunct and does not affect the refutation.

**Theorem 1.5 (Conjecture 28 is false).**

$$\neg claim28$$

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/CohenConsecutiveCubePrimePairThresholdRefutation.result28` (`✓ std3`). ∎

*Resolves.* `Problems/cohen-consecutive-cube-twin-prime-threshold-refutation` (refuted) by `D5/S0/Certificates/CohenConsecutiveCubePrimePairThresholdRefutation.result28`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"cohen-consecutive-cube-twin-prime-threshold-refutation","declaration_gid":"D5/S0/Certificates/CohenConsecutiveCubePrimePairThresholdRefutation.result28","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Joel E. Cohen (2025). *Conjectures about Primes and Cyclic Numbers*. DOI: [10.48550/arXiv.2508.08335](https://doi.org/10.48550/arXiv.2508.08335). URL: <https://cs.uwaterloo.ca/journals/JIS/VOL28/Cohen/cohen41.pdf>.

*Commentary.*

At n = 11 the open interval (1331,1728) contains exactly nine twin-prime pairs: (1427,1429), (1451,1453), (1481,1483), (1487,1489), (1607,1609), (1619,1621), (1667,1669), (1697,1699), and (1721,1723). Thus the printed N(10) = 11 threshold is false.

**Theorem 1.6 (Conjecture 29 is false).**

$$\neg claim29$$

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/CohenConsecutiveCubePrimePairThresholdRefutation.result29` (`✓ std3`). ∎

*Resolves.* `Problems/cohen-consecutive-cube-cousin-prime-threshold-refutation` (refuted) by `D5/S0/Certificates/CohenConsecutiveCubePrimePairThresholdRefutation.result29`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"cohen-consecutive-cube-cousin-prime-threshold-refutation","declaration_gid":"D5/S0/Certificates/CohenConsecutiveCubePrimePairThresholdRefutation.result29","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Joel E. Cohen (2025). *Conjectures about Primes and Cyclic Numbers*. DOI: [10.48550/arXiv.2508.08335](https://doi.org/10.48550/arXiv.2508.08335). URL: <https://cs.uwaterloo.ca/journals/JIS/VOL28/Cohen/cohen41.pdf>.

*Commentary.*

At n = 12 the open interval (1728,2197) contains exactly seven cousin-prime pairs: (1783,1787), (1867,1871), (1873,1877), (1993,1997), (1999,2003), (2083,2087), and (2137,2141). Thus the printed N(8) = N(9) = N(10) = 12 thresholds are false.

## References

- Truth anchor: `D5/S0/Certificates/CohenConsecutiveCubePrimePairThresholdRefutation.claim28`
- Truth anchor: `D5/S0/Certificates/CohenConsecutiveCubePrimePairThresholdRefutation.claim29`
- Truth anchor: `D5/S0/Certificates/CohenConsecutiveCubePrimePairThresholdRefutation.cousinPairCount`
- Truth anchor: `D5/S0/Certificates/CohenConsecutiveCubePrimePairThresholdRefutation.result28`
- Truth anchor: `D5/S0/Certificates/CohenConsecutiveCubePrimePairThresholdRefutation.result29`
- Truth anchor: `D5/S0/Certificates/CohenConsecutiveCubePrimePairThresholdRefutation.twinPairCount`
