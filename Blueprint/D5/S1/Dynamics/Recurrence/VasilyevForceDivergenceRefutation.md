# Vasilyev's force-divergence question

## Abstract

There is a set of positive integers that forces divergence in every superset but contains no all-up tail.

**Definition 1.1 (Positive vertices).**

$$P = \{x : \mathbb{N} \mid 0 < x\}$$

*Formalization.* `D5/S1/Dynamics/Recurrence/VasilyevForceDivergenceRefutation.P` (`✓ std3`).

*Citation.* Oleg Vasilyev (2026). *Up or down at every integer: Collatz-type maps of arbitrary sets and the up-down graph*. URL: <https://arxiv.org/html/2611.20344v2#S7.Thmtheorem7>.

*Commentary.*

The positive integers are the vertices of Vasilyev's up-down graph.

**Definition 1.2 (Up step).**

$$\forall x \in \mathbb{N},\; \operatorname{U}\left(x\right) = \operatorname{div}\left(3 \cdot x + 1, 2\right)$$

*Formalization.* `D5/S1/Dynamics/Recurrence/VasilyevForceDivergenceRefutation.U` (`✓ std3`).

*Citation.* Oleg Vasilyev (2026). *Up or down at every integer: Collatz-type maps of arbitrary sets and the up-down graph*. URL: <https://arxiv.org/html/2611.20344v2#S7.Thmtheorem7>.

*Commentary.*

The map takes natural numbers to natural numbers and div denotes Nat.div. On positive vertices this gives the ceiling of 3x/2 in Definition 1.1.

**Definition 1.3 (Down step).**

$$\forall x \in \mathbb{N},\; \operatorname{D}\left(x\right) = \operatorname{div}\left(x + 1, 2\right)$$

*Formalization.* `D5/S1/Dynamics/Recurrence/VasilyevForceDivergenceRefutation.D` (`✓ std3`).

*Citation.* Oleg Vasilyev (2026). *Up or down at every integer: Collatz-type maps of arbitrary sets and the up-down graph*. URL: <https://arxiv.org/html/2611.20344v2#S7.Thmtheorem7>.

*Commentary.*

The map takes natural numbers to natural numbers and div denotes Nat.div. On positive vertices this gives the ceiling of x/2 in Definition 1.1.

**Definition 1.4 (Step for a chosen set).**

$$\forall S \in \operatorname{Set}\left(\mathbb{N}\right),\; \forall x \in \mathbb{N},\; \operatorname{T}\left(S\right)\left(x\right) = \begin{cases}\operatorname{U}\left(x\right)&x \in S\\\operatorname{D}\left(x\right)&\neg (x \in S)\end{cases}$$

*Formalization.* `D5/S1/Dynamics/Recurrence/VasilyevForceDivergenceRefutation.T` (`✓ std3`).

*Citation.* Oleg Vasilyev (2026). *Up or down at every integer: Collatz-type maps of arbitrary sets and the up-down graph*. URL: <https://arxiv.org/html/2611.20344v2#S7.Thmtheorem7>.

*Commentary.*

Definition 1.1 selects the up or down map by membership in the chosen set. Lean uses classical decidability for this choice and defines a natural-to-natural map.

**Definition 1.5 (Force-divergence).**

$$\forall A \in \operatorname{Set}\left(\mathbb{N}\right),\; \operatorname{ForceDivergent}\left(A\right) \Leftrightarrow \left(\forall S \in \operatorname{Set}\left(\mathbb{N}\right),\; S \subseteq P \Rightarrow \left(A \subseteq S \Rightarrow \left(\exists x \in \mathbb{N},\; x \in P \land \left(\neg \left(\exists t \in \mathbb{N},\; \operatorname{iterate}\left(\operatorname{T}\left(S\right), t, x\right) \in \operatorname{periodicPts}\left(\operatorname{T}\left(S\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S1/Dynamics/Recurrence/VasilyevForceDivergenceRefutation.ForceDivergent` (`✓ std3`).

*Citation.* Oleg Vasilyev (2026). *Up or down at every integer: Collatz-type maps of arbitrary sets and the up-down graph*. URL: <https://arxiv.org/html/2611.20344v2#S7.Thmtheorem7>.

*Commentary.*

Section 2.3 quantifies over all supersets in the positive integers. The witness starts in P and its orbit avoids Mathlib's Function.periodicPts at every natural time. This set consists of the points with a positive period.

**Definition 1.6 (Contains an all-up tail).**

$$\forall A \in \operatorname{Set}\left(\mathbb{N}\right),\; \operatorname{ContainsTail}\left(A\right) \Leftrightarrow \left(\exists y \in \mathbb{N},\; y \in P \land \left(\forall k \in \mathbb{N},\; \operatorname{iterate}\left(U, k, y\right) \in A\right)\right)$$

*Formalization.* `D5/S1/Dynamics/Recurrence/VasilyevForceDivergenceRefutation.ContainsTail` (`✓ std3`).

*Citation.* Oleg Vasilyev (2026). *Up or down at every integer: Collatz-type maps of arbitrary sets and the up-down graph*. URL: <https://arxiv.org/html/2611.20344v2#S7.Thmtheorem7>.

*Commentary.*

Section 3.2 describes the chain tail starting at a positive vertex. The forward up orbit includes that vertex at time zero.

**Definition 1.7 (Question 7.7).**

$$claim \Leftrightarrow \left(\forall A \in \operatorname{Set}\left(\mathbb{N}\right),\; A \subseteq P \Rightarrow \left(\left(\forall S \in \operatorname{Set}\left(\mathbb{N}\right),\; S \subseteq P \Rightarrow \left(A \subseteq S \Rightarrow \left(\exists x \in \mathbb{N},\; x \in P \land \left(\neg \left(\exists t \in \mathbb{N},\; \operatorname{iterate}\left(\operatorname{T}\left(S\right), t, x\right) \in \operatorname{periodicPts}\left(\operatorname{T}\left(S\right)\right)\right)\right)\right)\right)\right) \Rightarrow \left(\exists y \in \mathbb{N},\; y \in P \land \left(\forall k \in \mathbb{N},\; \operatorname{iterate}\left(U, k, y\right) \in A\right)\right)\right)\right)$$

*Formalization.* `D5/S1/Dynamics/Recurrence/VasilyevForceDivergenceRefutation.claim` (`✓ std3`).

*Citation.* Oleg Vasilyev (2026). *Up or down at every integer: Collatz-type maps of arbitrary sets and the up-down graph*. URL: <https://arxiv.org/html/2611.20344v2#S7.Thmtheorem7>.

*Commentary.*

Vasilyev, Question 7.7 (printed p. 33).

“Does every force-divergent set, that is, every $A$ such that $T_{S}$ is unbounded for all $S$ ⊇ $A$, contain a tail of a chain?”

Let P be the positive integers. At x in P the up and down steps are the ceilings of 3x/2 and x/2, respectively. Lean writes them as (3x + 1) div 2 and (x + 1) div 2 with natural-number division. The map T(S) takes the up step at members of S and the down step elsewhere.

A subset A of P is force-divergent if, for every S with A contained in S and S contained in P, some positive starting vertex has an orbit under T that never enters a periodic cycle. Here iterate(f, t, x) applies f to x exactly t times, and periodicPts(f) is the set of points of positive period. A contains a tail if the whole forward up orbit of some positive vertex lies in A, including time zero.

**Theorem 1.8 (A force-divergent set without a chain tail).**

$$\neg \left(\forall A \in \operatorname{Set}\left(\mathbb{N}\right),\; A \subseteq P \Rightarrow \left(\left(\forall S \in \operatorname{Set}\left(\mathbb{N}\right),\; S \subseteq P \Rightarrow \left(A \subseteq S \Rightarrow \left(\exists x \in \mathbb{N},\; x \in P \land \left(\neg \left(\exists t \in \mathbb{N},\; \operatorname{iterate}\left(\operatorname{T}\left(S\right), t, x\right) \in \operatorname{periodicPts}\left(\operatorname{T}\left(S\right)\right)\right)\right)\right)\right)\right) \Rightarrow \left(\exists y \in \mathbb{N},\; y \in P \land \left(\forall k \in \mathbb{N},\; \operatorname{iterate}\left(U, k, y\right) \in A\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Recurrence/VasilyevForceDivergenceRefutation.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Oleg Vasilyev (2026). *Up or down at every integer: Collatz-type maps of arbitrary sets and the up-down graph*. URL: <https://arxiv.org/html/2611.20344v2#S7.Thmtheorem7>.

*Commentary.*

Start with b(0) = 3. Define b(n + 1) to be the 2b(n)-th up iterate of n + 1. Omit exactly the values b(n + 1) from P to obtain A. Each positive vertex n + 1 then has an up iterate outside A.

Each up step increases a positive value by at least one, so b(n + 1) > 2b(n). For m = b(n + 1), the ceiling bounds put both D(m) and U(D(m)) strictly between b(n) and m. The gap contains no omitted value. Thus, for any superset S, an orbit at a positive vertex in S grows after one up step. At a vertex outside S, that vertex is an omitted m and its next three steps are down, up, up. The endpoint is at least 9m/8, which exceeds m.

Concatenating these blocks gives unbounded orbit values from every positive start under each allowed S. An eventually periodic orbit has only finitely many values. The same A therefore forces divergence and excludes every all-up tail.

## References

- Truth anchor: `D5/S1/Dynamics/Recurrence/VasilyevForceDivergenceRefutation.ContainsTail`
- Truth anchor: `D5/S1/Dynamics/Recurrence/VasilyevForceDivergenceRefutation.D`
- Truth anchor: `D5/S1/Dynamics/Recurrence/VasilyevForceDivergenceRefutation.ForceDivergent`
- Truth anchor: `D5/S1/Dynamics/Recurrence/VasilyevForceDivergenceRefutation.P`
- Truth anchor: `D5/S1/Dynamics/Recurrence/VasilyevForceDivergenceRefutation.T`
- Truth anchor: `D5/S1/Dynamics/Recurrence/VasilyevForceDivergenceRefutation.U`
- Truth anchor: `D5/S1/Dynamics/Recurrence/VasilyevForceDivergenceRefutation.claim`
- Truth anchor: `D5/S1/Dynamics/Recurrence/VasilyevForceDivergenceRefutation.result`
