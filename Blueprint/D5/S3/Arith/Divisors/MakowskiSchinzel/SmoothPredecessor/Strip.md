# Removing bounded prime powers

## Abstract

Removing bounded prime powers

**Theorem 1.1 (Repeated division removes all occurrences).**

$$\forall p \in \mathbb{N},\; \forall m \in \mathbb{N},\; \forall k \in \mathbb{N},\; \neg (p^{\operatorname{add}\left(k, 1\right)} \mid m) \Leftrightarrow \left(0 < \operatorname{strip}\left(k, p, m\right) \land \left(\operatorname{strip}\left(k, p, m\right) \le m \land \left(\neg (p \mid \operatorname{strip}\left(k, p, m\right)) \land \left(\exists e \in \mathbb{N},\; e \le k \land m = p^{e} \cdot \operatorname{strip}\left(k, p, m\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Divisors/MakowskiSchinzel/SmoothPredecessor/Strip.strip_spec` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Nondivisibility by p^(k+1) is equivalent to the following complete stripping data: the result is positive and at most m, is indivisible by p, and multiplying it by a suitable p-power recovers m. The recovered exponent is at most k; zero divisors are included. Without the fuel condition, p=2, m=2 and k=0 leave a factor of p in the result.

**Theorem 1.2 (Removing one allowed prime).**

$$\forall p \in \mathbb{N},\; \forall m \in \mathbb{N},\; \forall k \in \mathbb{N},\; \forall s \in \operatorname{Finset}\left(\mathbb{N}\right),\; \left(\operatorname{Prime}\left(p\right) \lor p \le 1\right) \Rightarrow \left(\left(p \le 1 \lor \left(p \in s \lor \left(m = 0 \lor \neg (p^{\operatorname{add}\left(k, 1\right)} \mid m)\right)\right)\right) \Rightarrow \left(\operatorname{strip}\left(k, p, m\right) \in \operatorname{factoredNumbers}\left(s\right) \Leftrightarrow m \in \operatorname{factoredNumbers}\left(\operatorname{insert}\left(p, s\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Divisors/MakowskiSchinzel/SmoothPredecessor/Strip.strip_factored_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For p prime or at most one, assume p is at most one, belongs to s, m is zero, or p^(k+1) does not divide m. Zero and one leave the input and its prime support unchanged. The stripped result has prime support in s exactly when m has support in s union {p}. The statement does not require p to be absent from s. Composite generators cannot be admitted in general: stripping 6 from 6 can return 1 although its prime support is not contained in {6}. For prime p absent from s, an unremoved p-factor prevents membership on the left.

**Theorem 1.3 (The Boolean support test).**

$$\forall l \in \operatorname{List}\left(\mathbb{N}\right),\; \forall m \in \mathbb{N},\; \left(\forall p \in \mathbb{N},\; p \in l \Rightarrow \left(\operatorname{Prime}\left(p\right) \lor p \le 1\right)\right) \Rightarrow \left(\left(m = 0 \lor \left(\forall p \in \mathbb{N},\; p \in l \Rightarrow \left(\operatorname{Prime}\left(p\right) \Rightarrow \neg (p^{65} \mid m)\right)\right)\right) \Rightarrow \left(\operatorname{isSmooth}\left(l, m\right) = \operatorname{true}\left(\right) \Leftrightarrow m \in \operatorname{factoredNumbers}\left(\operatorname{toFinset}\left(l\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Divisors/MakowskiSchinzel/SmoothPredecessor/Strip.isSmooth_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a list of primes, zeros and ones, assume m is zero or no listed prime p has p^65 dividing m. The smoothness test succeeds exactly when m is nonzero and all its prime factors occur in the list. Neither ordering nor absence of repeated primes is required. The primewise bound makes 64 divisions sufficient. Without it, the list [2] and m=2^65 leave the test false despite the permitted support. Generators above one must be prime; generators such as 6 can hide other prime factors.

## References

- Truth anchor: `D5/S3/Arith/Divisors/MakowskiSchinzel/SmoothPredecessor/Strip.isSmooth_iff`
- Truth anchor: `D5/S3/Arith/Divisors/MakowskiSchinzel/SmoothPredecessor/Strip.strip_factored_iff`
- Truth anchor: `D5/S3/Arith/Divisors/MakowskiSchinzel/SmoothPredecessor/Strip.strip_spec`
