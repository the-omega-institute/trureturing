# Weighted enumeration of smooth multiples

## Abstract

Weighted enumeration of smooth multiples

**Definition 1.1 (Bounded multiples with prescribed quotient support).**

$$\forall s \in \operatorname{Finset}\left(\mathbb{N}\right),\; \forall X \in \mathbb{N},\; \forall c \in \mathbb{N},\; \forall m \in \mathbb{N},\; \operatorname{Mem}\left(m, \operatorname{factoredMultiples}\left(s, X, c\right)\right) \Leftrightarrow \left(1 \le m \land \left(m \le X \land \left(\operatorname{Divides}\left(c, m\right) \land \operatorname{Mem}\left(\operatorname{natDiv}\left(m, c\right), \operatorname{factoredNumbers}\left(s\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Arith/Divisors/MakowskiSchinzel/SmoothPredecessor/Enumeration.factoredMultiples` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The finite set contains the positive m at most X divisible by c for which every prime divisor of m/c belongs to s. Membership in factoredNumbers also requires the quotient to be nonzero.

**Theorem 1.2 (The truncated power fold).**

$$\forall n \in \mathbb{N},\; \forall f \in \mathbb{N} \to \mathbb{N},\; \forall p \in \mathbb{N},\; \forall X \in \mathbb{N},\; \forall c \in \mathbb{N},\; \operatorname{powSum}\left(n, f, p, X, c\right) = \sum_{e \in \operatorname{range}\left(n\right)} \operatorname{ite}\left(c \cdot p^{e} \le X, f\left(c \cdot p^{e}\right), 0\right) \Leftrightarrow \left(n \le 1 \lor \left(1 \le p \lor \left(c \le X \lor f\left(0\right) = 0\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Divisors/MakowskiSchinzel/SmoothPredecessor/Enumeration.powSum_eq_sum_range` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exactly when n is at most one, p is at least one, c is at most X, or f(0)=0, the recursive fold sums f(c p^e) for exponents below n whose multiples are at most X. For n at most one only the initial multiple is visited; otherwise the condition prevents a later multiple from returning below X after the fold has stopped, or gives zero weight to every returned zero multiple. For n=2, p=0, X=0, c=1 and constant weight 1, the fold is zero but the sum is one.

**Theorem 1.3 (Prime-power branch partition).**

$$\forall w \in \mathbb{N} \to \mathbb{N},\; \forall N \in \mathbb{N},\; \forall s \in \operatorname{Finset}\left(\mathbb{N}\right),\; \forall p \in \mathbb{N},\; \forall X \in \mathbb{N},\; \forall c \in \mathbb{N},\; \operatorname{Prime}\left(p\right) \Rightarrow \left(\operatorname{NotMem}\left(p, s\right) \Rightarrow \left(\left(c = 0 \lor X < c \cdot p^{N}\right) \Rightarrow \sum_{e \in \operatorname{range}\left(N\right)} \sum_{m \in \operatorname{factoredMultiples}\left(s, X, c \cdot p^{e}\right)} w\left(m\right) = \sum_{m \in \operatorname{factoredMultiples}\left(\operatorname{insert}\left(p, s\right), X, c\right)} w\left(m\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Divisors/MakowskiSchinzel/SmoothPredecessor/Enumeration.sum_factoredMultiples_insert` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The set factoredMultiples(s,X,c) contains the integers m from 1 through X such that c divides m and m/c has every prime factor in s. For a prime p outside s, the N power branches partition the corresponding set with p inserted when c is zero or X < c p^N. This bound excludes all later exponents. The unique factorization equivalence supplies both coverage and uniqueness. Primality gives this decomposition; excluding p from s prevents overlapping branches. Without the cutoff, a multiple requiring exponent N is omitted.

**Theorem 1.4 (Correctness of the smooth fold).**

$$\forall w \in \mathbb{N} \to \mathbb{N},\; \forall ps \in \operatorname{List}\left(\mathbb{N}\right),\; \left(\forall p \in \mathbb{N},\; \operatorname{Mem}\left(p, ps\right) \Rightarrow \operatorname{Prime}\left(p\right)\right) \Rightarrow \left(\operatorname{Nodup}\left(ps\right) \Rightarrow \left(\forall X \in \mathbb{N},\; \forall c \in \mathbb{N},\; \left(0 < c \lor w\left(0\right) = 0\right) \Rightarrow \left(\left(ps = \operatorname{nil}\left(\right) \Rightarrow \left(c \le X \lor w\left(c\right) = 0\right)\right) \Rightarrow \left(\left(c = 0 \lor \left(\forall p \in \mathbb{N},\; \operatorname{Mem}\left(p, ps\right) \Rightarrow X < c \cdot p^{64}\right)\right) \Rightarrow \operatorname{smoothSum}\left(w, ps, X, c\right) = \sum_{m \in \operatorname{factoredMultiples}\left(\operatorname{toFinset}\left(ps\right), X, c\right)} w\left(m\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Divisors/MakowskiSchinzel/SmoothPredecessor/Enumeration.smoothSum_eq_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For distinct primes, assume c is positive or w(0)=0, and either c=0 or X < c p^64 for every listed p. The smooth fold is the weighted sum of bounded multiples whose quotient has prime support in that list. The condition c <= X is needed only for the empty prime list, where the fold returns w(c); it can be dropped when w(c)=0. The weights need not be multiplicative. Repeated generators count some integers more than once. A zero start contributes zero exactly when w(0)=0, since its set of positive multiples is empty. Each primewise cutoff ensures that no omitted exponent contributes a bounded multiple.

## References

- Truth anchor: `D5/S3/Arith/Divisors/MakowskiSchinzel/SmoothPredecessor/Enumeration.factoredMultiples`
- Truth anchor: `D5/S3/Arith/Divisors/MakowskiSchinzel/SmoothPredecessor/Enumeration.powSum_eq_sum_range`
- Truth anchor: `D5/S3/Arith/Divisors/MakowskiSchinzel/SmoothPredecessor/Enumeration.smoothSum_eq_sum`
- Truth anchor: `D5/S3/Arith/Divisors/MakowskiSchinzel/SmoothPredecessor/Enumeration.sum_factoredMultiples_insert`
