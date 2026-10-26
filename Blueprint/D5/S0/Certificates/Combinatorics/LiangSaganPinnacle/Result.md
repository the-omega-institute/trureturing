# Pinnacle fibres need not be lattices

## Abstract

For every n at least six, an ordered pinnacle class contains two permutations without a common upper bound in the middle order.

**Definition 1.1 (An internal strict peak).**

$$\forall n \in \operatorname {Nat},\; \forall p \in \operatorname {Equiv.Perm}\left(\operatorname {Fin}\left(n\right)\right),\; \forall j \in \operatorname {Fin}\left(n\right),\; (\operatorname {Peak}\left(p, j\right)) \Leftrightarrow (\exists l \in \operatorname {Fin}\left(n\right),\; \exists r \in \operatorname {Fin}\left(n\right),\; (\operatorname {Fin.val}\left(l\right) + 1 = \operatorname {Fin.val}\left(j\right)) \land ((\operatorname {Fin.val}\left(j\right) + 1 = \operatorname {Fin.val}\left(r\right)) \land ((p\left(l\right) < p\left(j\right)) \land (p\left(r\right) < p\left(j\right)))))$$

*Formalization.* `D5/S0/Certificates/Combinatorics/LiangSaganPinnacle/Result.Peak` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The predecessor and successor are actual positions in Fin n. Their index equations force 0<j<n−1, and both neighbouring values are strictly smaller.

**Definition 1.2 (Pinnacles in positional order).**

$$\forall n \in \operatorname {Nat},\; \forall p \in \operatorname {Equiv.Perm}\left(\operatorname {Fin}\left(n\right)\right),\; \operatorname {pinnacleWord}\left(p\right) = \operatorname {List.map}\left(p, \operatorname {List.filter}\left(j: \operatorname {Fin}\left(n\right)\mapsto \operatorname {decide}\left(\operatorname {Peak}\left(p, j\right)\right), \operatorname {List.finRange}\left(n\right)\right)\right)$$

*Formalization.* `D5/S0/Certificates/Combinatorics/LiangSaganPinnacle/Result.pinnacleWord` (`✓ std3`).

*Citation.* J. Liang and B. E. Sagan (2026). *Log-concavity and log-convexity via distributive lattices*. DOI: [10.1007/s11083-026-09735-2](https://doi.org/10.1007/s11083-026-09735-2). URL: <https://arxiv.org/abs/2408.02782v2>.

*Commentary.*

Question 8.6 defines pinnacles as values at internal positions with π(j−1)<π(j)>π(j+1), read from left to right. A permutation is the word π(0)π(1)…π(n−1); a Fin n value k represents the paper's positive value k+1. The increasing list of positions preserves the order of the pinnacle word.

**Definition 1.3 (The inversion-top table).**

$$\forall n \in \operatorname {Nat},\; \forall p \in \operatorname {Equiv.Perm}\left(\operatorname {Fin}\left(n\right)\right),\; \forall v \in \operatorname {Fin}\left(n\right),\; \operatorname {iota}\left(p, v\right) = \operatorname {Finset.card}\left(\operatorname {Finset.filter}\left(w: \operatorname {Fin}\left(n\right)\mapsto (w < v) \land (\operatorname {Equiv.symm}\left(p\right)\left(v\right) < \operatorname {Equiv.symm}\left(p\right)\left(w\right)), \operatorname {Finset.univ}\right)\right)$$

*Formalization.* `D5/S0/Certificates/Combinatorics/LiangSaganPinnacle/Result.iota` (`✓ std3`).

*Citation.* J. Liang and B. E. Sagan (2026). *Log-concavity and log-convexity via distributive lattices*. DOI: [10.1007/s11083-026-09735-2](https://doi.org/10.1007/s11083-026-09735-2). URL: <https://arxiv.org/abs/2408.02782v2>.

*Commentary.*

Section 6, Permutations, printed pages 17–18: “Given π = π1 π2 . . . πn ∈ Sn in one-line notation, its set of inversion (values) is Inv π = {(πi, πj) | i < j and πi > πj}.” “We also say that πi is an inversion top if (πi, πj) ∈ Inv π for some πj.” Printed page 18: “where ιi = # of inversions in which i is an inversion top.” The paper's example 415632 has inversion table (0,0,1,3,2,2). Inverse positions count smaller values to the right of v, with no change of order direction.

**Definition 1.4 (The middle order).**

$$\forall n \in \operatorname {Nat},\; \forall p \in \operatorname {Equiv.Perm}\left(\operatorname {Fin}\left(n\right)\right),\; \forall q \in \operatorname {Equiv.Perm}\left(\operatorname {Fin}\left(n\right)\right),\; (\operatorname {middleLe}\left(p, q\right)) \Leftrightarrow (\forall v \in \operatorname {Fin}\left(n\right),\; \operatorname {iota}\left(p, v\right) \le \operatorname {iota}\left(q, v\right))$$

*Formalization.* `D5/S0/Certificates/Combinatorics/LiangSaganPinnacle/Result.middleLe` (`✓ std3`).

*Citation.* J. Liang and B. E. Sagan (2026). *Log-concavity and log-convexity via distributive lattices*. DOI: [10.1007/s11083-026-09735-2](https://doi.org/10.1007/s11083-026-09735-2). URL: <https://arxiv.org/abs/2408.02782v2>.

*Commentary.*

Section 6, Permutations, printed page 18: “We can now use the bijection just given to define the middle order (Sn, ⪯) by π ⪯ σ if and only if ι(π) ≤ ι(σ) where the order on inversion tables is component-wise.” The comparison is pointwise in the value, rather than in the position.

**Definition 1.5 (The ordered pinnacle fibre).**

$$\forall n \in \operatorname {Nat},\; \forall s \in \operatorname {List}\left(\operatorname {Fin}\left(n\right)\right),\; \operatorname {Pin}\left(n, s\right) = \{p: \operatorname {Equiv.Perm}\left(\operatorname {Fin}\left(n\right)\right) \mid \operatorname {pinnacleWord}\left(p\right) = s\}$$

*Formalization.* `D5/S0/Certificates/Combinatorics/LiangSaganPinnacle/Result.Pin` (`✓ std3`).

*Citation.* J. Liang and B. E. Sagan (2026). *Log-concavity and log-convexity via distributive lattices*. DOI: [10.1007/s11083-026-09735-2](https://doi.org/10.1007/s11083-026-09735-2). URL: <https://arxiv.org/abs/2408.02782v2>.

*Commentary.*

Section 8, printed pages 34–35, Question 8.6: “Let σ be a permutation of distinct positive integers. Let Pin_n(σ) = {π ∈ S_n | the pinnacles of π are the elements of σ in that order}. … Computation of examples raise the following questions. Question 8.6. For all n and σ: (a) Is the restriction of the middle order to Pin_n(σ) a distributive lattice? (b) Is the sequence (pin_n(σ)) log-concave?” A repeated value cannot occur in the pinnacle word of a permutation. A positive source value outside [n] gives an empty class; such a value has no Fin n encoding. The two values used below are distinct and lie in [n].

**Definition 1.6 (The universal distributive-lattice assertion).**

$$claim = \left(\forall n \in \operatorname {Nat},\; \forall s \in \operatorname {List}\left(\operatorname {Fin}\left(n\right)\right),\; \exists L \in \operatorname {DistribLattice}\left(\operatorname {Pin}\left(n, s\right)\right),\; \forall x \in \operatorname {Pin}\left(n, s\right),\; \forall y \in \operatorname {Pin}\left(n, s\right),\; (L.le\left(x, y\right)) \Leftrightarrow (\operatorname {middleLe}\left(\operatorname {Subtype.val}\left(x\right), \operatorname {Subtype.val}\left(y\right)\right))\right)$$

*Formalization.* `D5/S0/Certificates/Combinatorics/LiangSaganPinnacle/Result.claim` (`✓ std3`).

*Citation.* J. Liang and B. E. Sagan (2026). *Log-concavity and log-convexity via distributive lattices*. DOI: [10.1007/s11083-026-09735-2](https://doi.org/10.1007/s11083-026-09735-2). URL: <https://arxiv.org/abs/2408.02782v2>.

*Commentary.*

Section 8, printed pages 34–35, Question 8.6: “Let σ be a permutation of distinct positive integers. Let Pin_n(σ) = {π ∈ S_n | the pinnacles of π are the elements of σ in that order}. … Computation of examples raise the following questions. Question 8.6. For all n and σ: (a) Is the restriction of the middle order to Pin_n(σ) a distributive lattice? (b) Is the sequence (pin_n(σ)) log-concave?” A distributive lattice is required to have exactly the order middleLe on the fibre. Requiring the assertion also for repeated Fin values introduces no counterexample here: the refutation uses the distinct ordered pair (n−2,n). Only part (a) is answered.

**Theorem 1.7 (Exactly two peak positions).**

$$\forall k \in \operatorname {Nat},\; \forall t \in \operatorname {Nat},\; \forall h \in t \le 1,\; \forall j \in \operatorname {Fin}\left(k + 6\right),\; (\operatorname {Peak}\left(\operatorname {witness}\left(k, t, h\right), j\right)) \Leftrightarrow ((\operatorname {Fin.val}\left(j\right) = t + 1) \lor (\operatorname {Fin.val}\left(j\right) = t + 3))$$

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/Combinatorics/LiangSaganPinnacle/Result.witness_peak` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Write n=k+6 and t=0 or 1. The permutation witness k t has its two peaks at t+1 and t+3. For t=0 its word is 0,k+3,1,k+5,2,…,k+2,k+4. For t=1 its word is k+4,0,k+3,1,k+5,2,…,k+2. Explicit inverse functions prove that both words are permutations. Every other internal position is on an increasing run or next to a larger value.

**Theorem 1.8 (The common ordered pinnacle word).**

$$\forall k \in \operatorname {Nat},\; \forall t \in \operatorname {Nat},\; \forall h \in t \le 1,\; \operatorname {pinnacleWord}\left(\operatorname {witness}\left(k, t, h\right)\right) = [\langle k + 3\rangle , \langle k + 5\rangle ]$$

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/Combinatorics/LiangSaganPinnacle/Result.witness_word` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The two positions t+1 and t+3 occur in that order. Their values are k+3 and k+5, namely the source's n−2 and n. Filtering the increasing position list therefore yields precisely this ordered pair.

**Theorem 1.9 (Inversions of the maximum count positions to its right).**

$$\forall n \in \operatorname {Nat},\; \forall p \in \operatorname {Equiv.Perm}\left(\operatorname {Fin}\left(n\right)\right),\; \forall v \in \operatorname {Fin}\left(n\right),\; (\operatorname {Fin.val}\left(v\right) + 1 = n) \Rightarrow (\operatorname {iota}\left(p, v\right) = n - 1 - \operatorname {Fin.val}\left(\operatorname {Equiv.symm}\left(p\right)\left(v\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/Combinatorics/LiangSaganPinnacle/Result.iota_max` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The inverse permutation bijects smaller values to the right of the maximum with all positions strictly after that maximum. The cardinality of this final Fin interval is n−1−pos(v).

**Theorem 1.10 (The maximum inversion count in the first word).**

$$\forall k \in \operatorname {Nat},\; \operatorname {iota}\left(\operatorname {witness}\left(k, 0\right), \langle k + 5\rangle \right) = k + 2$$

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/Combinatorics/LiangSaganPinnacle/Result.witness_iota_max` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In the first word the maximum is at position 3, so its inversion count is k+2=n−4.

**Theorem 1.11 (The saturated count in the second word).**

$$\forall k \in \operatorname {Nat},\; \operatorname {iota}\left(\operatorname {witness}\left(k, 1\right), \langle k + 4\rangle \right) = k + 4$$

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/Combinatorics/LiangSaganPinnacle/Result.witness_iota_second` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The value k+4, the source's n−1, starts the second word. All k+4 smaller values are to its right, so its inversion count is k+4=n−2.

**Theorem 1.12 (The word determines the two peak positions).**

$$\forall n \in \operatorname {Nat},\; \forall p \in \operatorname {Equiv.Perm}\left(\operatorname {Fin}\left(n\right)\right),\; \forall a \in \operatorname {Fin}\left(n\right),\; \forall b \in \operatorname {Fin}\left(n\right),\; (\operatorname {pinnacleWord}\left(p\right) = [a, b]) \Rightarrow ((\operatorname {Peak}\left(p, \operatorname {Equiv.symm}\left(p\right)\left(a\right)\right)) \land ((\operatorname {Peak}\left(p, \operatorname {Equiv.symm}\left(p\right)\left(b\right)\right)) \land (\operatorname {Equiv.symm}\left(p\right)\left(a\right) < \operatorname {Equiv.symm}\left(p\right)\left(b\right))))$$

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/Combinatorics/LiangSaganPinnacle/Result.word_positions` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Applying the inverse permutation to the word recovers the filtered positions. Both are peaks, and the strict ordering of the original position list orders their inverse positions.

**Theorem 1.13 (Saturation excludes a common upper bound).**

$$\forall k \in \operatorname {Nat},\; \forall u \in \operatorname {Equiv.Perm}\left(\operatorname {Fin}\left(k + 6\right)\right),\; (\operatorname {pinnacleWord}\left(u\right) = [\langle k + 3\rangle , \langle k + 5\rangle ]) \Rightarrow ((\operatorname {middleLe}\left(\operatorname {witness}\left(k, 0\right), u\right)) \Rightarrow ((\operatorname {middleLe}\left(\operatorname {witness}\left(k, 1\right), u\right)) \Rightarrow (\operatorname {False})))$$

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/Combinatorics/LiangSaganPinnacle/Result.obstruction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Saturation forces k+4 before every smaller value, including the left neighbour of the first pinnacle k+3. That pinnacle has position at least 2. Its right neighbour is smaller, so the larger pinnacle k+5 cannot occupy the next position; its position is at least 4. Its inversion count is at most k+1, whereas dominance of the first word requires at least k+2.

**Definition 1.14 (The pinnacle word for the family).**

$$\forall n \in \operatorname {Nat},\; \forall h \in 6 \le n,\; \operatorname {sigma}\left(n, h\right) = [\langle n - 3\rangle , \langle n - 1\rangle ]$$

*Formalization.* `D5/S0/Certificates/Combinatorics/LiangSaganPinnacle/Result.sigma` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

These Fin n values encode the positive values (n−2,n). They are distinct for every n≥6.

**Theorem 1.15 (A non-lattice fibre for every n at least six).**

$$\forall n \in \operatorname {Nat},\; \forall h \in 6 \le n,\; \exists A \in \operatorname {Pin}\left(n, \operatorname {sigma}\left(n, h\right)\right),\; \exists B \in \operatorname {Pin}\left(n, \operatorname {sigma}\left(n, h\right)\right),\; \forall U \in \operatorname {Pin}\left(n, \operatorname {sigma}\left(n, h\right)\right),\; \neg \left((\operatorname {middleLe}\left(\operatorname {Subtype.val}\left(A\right), \operatorname {Subtype.val}\left(U\right)\right)) \land (\operatorname {middleLe}\left(\operatorname {Subtype.val}\left(B\right), \operatorname {Subtype.val}\left(U\right)\right))\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/Combinatorics/LiangSaganPinnacle/Result.no_common_upper_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Set k=n−6. The two explicit permutations have the required ordered pinnacle word. The preceding position argument excludes every common upper bound in that same fibre. Thus every n≥6 has an ordered pinnacle class which is not even a lattice.

**Theorem 1.16 (A negative answer to Question 8.6(a)).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/Combinatorics/LiangSaganPinnacle/Result.result` (`✓ std3`). ∎

*Resolves.* `Problems/liang-sagan-2026-pinnacle-middle-order` (refuted) by `D5/S0/Certificates/Combinatorics/LiangSaganPinnacle/Result.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"liang-sagan-2026-pinnacle-middle-order","declaration_gid":"D5/S0/Certificates/Combinatorics/LiangSaganPinnacle/Result.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* J. Liang and B. E. Sagan (2026). *Log-concavity and log-convexity via distributive lattices*. DOI: [10.1007/s11083-026-09735-2](https://doi.org/10.1007/s11083-026-09735-2). URL: <https://arxiv.org/abs/2408.02782v2>.

*Commentary.*

At n=6 the two permutations are 142635 and 514263 in positive values, with pinnacle word (4,6). A distributive-lattice join would be an upper bound of both, contrary to the general family theorem. Question 8.6(b), concerning log-concavity of the class sizes, remains unanswered here.

## References

- Truth anchor: `D5/S0/Certificates/Combinatorics/LiangSaganPinnacle/Result.Peak`
- Truth anchor: `D5/S0/Certificates/Combinatorics/LiangSaganPinnacle/Result.Pin`
- Truth anchor: `D5/S0/Certificates/Combinatorics/LiangSaganPinnacle/Result.claim`
- Truth anchor: `D5/S0/Certificates/Combinatorics/LiangSaganPinnacle/Result.iota`
- Truth anchor: `D5/S0/Certificates/Combinatorics/LiangSaganPinnacle/Result.iota_max`
- Truth anchor: `D5/S0/Certificates/Combinatorics/LiangSaganPinnacle/Result.middleLe`
- Truth anchor: `D5/S0/Certificates/Combinatorics/LiangSaganPinnacle/Result.no_common_upper_bound`
- Truth anchor: `D5/S0/Certificates/Combinatorics/LiangSaganPinnacle/Result.obstruction`
- Truth anchor: `D5/S0/Certificates/Combinatorics/LiangSaganPinnacle/Result.pinnacleWord`
- Truth anchor: `D5/S0/Certificates/Combinatorics/LiangSaganPinnacle/Result.result`
- Truth anchor: `D5/S0/Certificates/Combinatorics/LiangSaganPinnacle/Result.sigma`
- Truth anchor: `D5/S0/Certificates/Combinatorics/LiangSaganPinnacle/Result.witness_iota_max`
- Truth anchor: `D5/S0/Certificates/Combinatorics/LiangSaganPinnacle/Result.witness_iota_second`
- Truth anchor: `D5/S0/Certificates/Combinatorics/LiangSaganPinnacle/Result.witness_peak`
- Truth anchor: `D5/S0/Certificates/Combinatorics/LiangSaganPinnacle/Result.witness_word`
- Truth anchor: `D5/S0/Certificates/Combinatorics/LiangSaganPinnacle/Result.word_positions`
