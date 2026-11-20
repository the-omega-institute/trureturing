# Vasilyev's force-divergence question

## Abstract

There is a set of positive integers that forces divergence in every superset but contains no all-up tail.

**Definition 1.1 (Question 7.7).**

$$claim \Leftrightarrow \left(\forall A \in \operatorname{Set}\left(\mathbb{N}\right),\; A \subseteq P \Rightarrow \left(\operatorname{ForceDivergent}\left(A\right) \Rightarrow \operatorname{ContainsTail}\left(A\right)\right)\right)$$

*Formalization.* `D5/S1/Dynamics/Recurrence/VasilyevForceDivergenceRefutation.claim` (`✓ std3`).

*Citation.* Oleg Vasilyev (2026). *Up or down at every integer: Collatz-type maps of arbitrary sets and the up-down graph*. URL: <https://arxiv.org/html/2611.20344v2#S7.Thmtheorem7>.

*Commentary.*

Let P be the positive integers. At x in P the up and down steps are the ceilings of 3x/2 and x/2, respectively. The map T for a set S takes the up step at members of S and the down step elsewhere.

A subset A of P is force-divergent if, for every S with A contained in S and S contained in P, some positive starting vertex has an orbit under T that never enters a periodic cycle. A contains a tail if the whole forward up orbit of some positive vertex lies in A, including time zero.

**Theorem 1.2 (A force-divergent set without a chain tail).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Recurrence/VasilyevForceDivergenceRefutation.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Oleg Vasilyev (2026). *Up or down at every integer: Collatz-type maps of arbitrary sets and the up-down graph*. URL: <https://arxiv.org/html/2611.20344v2#S7.Thmtheorem7>.

*Commentary.*

Start with b(0) = 3. Define b(n + 1) to be the 2b(n)-th up iterate of n + 1. Omit exactly the values b(n + 1) from P to obtain A. Each positive vertex n + 1 then has an up iterate outside A.

Each up step increases a positive value by at least one, so b(n + 1) > 2b(n). For m = b(n + 1), the ceiling bounds put both D(m) and U(D(m)) strictly between b(n) and m. The gap contains no omitted value. Thus, for any superset S, an orbit at a positive vertex in S grows after one up step. At a vertex outside S, that vertex is an omitted m and its next three steps are down, up, up. The endpoint is at least 9m/8, which exceeds m.

Concatenating these blocks gives unbounded orbit values from every positive start under each allowed S. An eventually periodic orbit has only finitely many values. The same A therefore forces divergence and excludes every all-up tail.

## References

- Truth anchor: `D5/S1/Dynamics/Recurrence/VasilyevForceDivergenceRefutation.claim`
- Truth anchor: `D5/S1/Dynamics/Recurrence/VasilyevForceDivergenceRefutation.result`
