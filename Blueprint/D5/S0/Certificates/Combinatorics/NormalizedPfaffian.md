# Normalized Pfaffian listings and counted crossing convention

## Abstract

The original normalized Pfaffian pair-listing core and its counted crossing convention bridge over arbitrary commutative rings.

**Definition 1.1 (Involutive partner maps).**

$$\forall k \in \mathbb{N},\; \operatorname{P}\left(k\right) = \{p:\operatorname{Fin}\left(2 \cdot k\right) \to \operatorname{Fin}\left(2 \cdot k\right) \mid \left(\forall x \in \operatorname{Fin}\left(2 \cdot k\right),\; \operatorname{Apply}\left(p, \operatorname{Apply}\left(p, x\right)\right) = x\right) \land \left(\forall x \in \operatorname{Fin}\left(2 \cdot k\right),\; \operatorname{Apply}\left(p, x\right) \ne x\right)\}$$

*Formalization.* `D5/S0/Certificates/Combinatorics/NormalizedPfaffian.P` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For each natural k, P(k) consists of all functions on Fin(2k) that square to the identity and have no fixed points. The two-element orbits form the unordered pairs. The empty function is included when k is zero.

**Definition 1.2 (The Pfaffian over a commutative ring).**

$$\forall R \in \operatorname{Type}\left(\right),\; [\operatorname{CommRing}\left(R\right)] \forall n \in \mathbb{N},\; \forall A \in \operatorname{Matrix}\left(\operatorname{Fin}\left(2 \cdot n\right), \operatorname{Fin}\left(2 \cdot n\right), R\right),\; \operatorname{pfaffian}\left(A\right) = \sum_{sigma \in \{sigma:\operatorname{Perm}\left(\operatorname{Fin}\left(2 \cdot n\right)\right) \mid \left(\forall i \in \operatorname{Fin}\left(n\right),\; \operatorname{Apply}\left(sigma, 2 \cdot i\right) < \operatorname{Apply}\left(sigma, 2 \cdot i + 1\right)\right) \land \left(\forall i \in \operatorname{Fin}\left(n\right),\; \forall j \in \operatorname{Fin}\left(n\right),\; i < j \Rightarrow \operatorname{Apply}\left(sigma, 2 \cdot i\right) < \operatorname{Apply}\left(sigma, 2 \cdot j\right)\right)\}} \operatorname{intCast}\left(\operatorname{sign}\left(sigma\right)\right) \cdot \prod_{i \in \operatorname{Fin}\left(n\right)} \operatorname{Apply}\left(A, \operatorname{Apply}\left(sigma, 2 \cdot i\right), \operatorname{Apply}\left(sigma, 2 \cdot i + 1\right)\right)$$

*Formalization.* `D5/S0/Certificates/Combinatorics/NormalizedPfaffian.pfaffian` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Let R be any commutative ring and A a matrix on Fin(2n). A permutation sigma is normalized when each pair sigma(2i), sigma(2i+1) is increasing and the first endpoints increase with i. The set L(n) below contains precisely these permutations. The coefficient is the integer value of the permutation sign, cast into R. Every pairing is permitted independently of any graph or weights. No division by a factorial or a power of two occurs. For n = 0 the unique empty permutation contributes the empty product, which is one. The convention agrees with the normalized partitions in Ishikawa and Koutschan, Zeilberger's holonomic ansatz for Pfaffians, arXiv:1201.5253v2.

**Theorem 1.3 (Canonical slots are partners).**

$$\forall n \in \mathbb{N},\; \forall p \in \operatorname{P}\left(n\right),\; \forall i \in \operatorname{Fin}\left(n\right),\; \operatorname{Apply}\left(p, \operatorname{Apply}\left(\operatorname{canonicalListing}\left(p\right), 2 \cdot i\right)\right) = \operatorname{Apply}\left(\operatorname{canonicalListing}\left(p\right), 2 \cdot i + 1\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/Combinatorics/NormalizedPfaffian.canonical_mate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A partner map p on Fin(2n) is involutive and has no fixed point. Choose its lower endpoints x < p(x), enumerate them increasingly, and put each x immediately before p(x). Exactly n lower endpoints occur: applying p exchanges the lower endpoints with their complement. The resulting flattening is a bijection c(p). Thus it is a genuine permutation, including when n = 0. Its increasing pairs are ordered by their first endpoints.

**Definition 1.4 (Every pairing occurs once).**

$$\forall n \in \mathbb{N},\; \operatorname{TypeOf}\left(\operatorname{listingEquiv}\left(n\right)\right) = \operatorname{Equiv}\left(\operatorname{normalizedListings}\left(n\right), \operatorname{P}\left(n\right)\right)$$

*Formalization.* `D5/S0/Certificates/Combinatorics/NormalizedPfaffian.listingEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Conjugating the consecutive partner map by a listing s gives pairingOfListing(s). The canonical listing of this partner map is s whenever s satisfies the normalized-listing inequalities. Conversely, conjugation by c(p) recovers p. These inverse constructions give a bijection from all normalized listing permutations to P(n). The enumeration is independent of a graph, edge support, orientation or weights.

**Theorem 1.5 (Signed normalization).**

$$\forall n \in \mathbb{N},\; \forall f \in \operatorname{Function}\left(\operatorname{Fin}\left(2 \cdot n\right), \operatorname{Fin}\left(2 \cdot n\right), \operatorname{IntegerUnits}\left(\right)\right),\; \forall s \in \operatorname{Perm}\left(\operatorname{Fin}\left(2 \cdot n\right)\right),\; \left(\forall x \in \operatorname{Fin}\left(2 \cdot n\right),\; \forall y \in \operatorname{Fin}\left(2 \cdot n\right),\; x \ne y \Rightarrow \operatorname{Apply}\left(f, y, x\right) = -\operatorname{Apply}\left(f, x, y\right)\right) \Rightarrow \operatorname{listingValue}\left(f, s\right) = \operatorname{listingValue}\left(f, \operatorname{canonicalListing}\left(\operatorname{pairingOfListing}\left(s\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/Combinatorics/NormalizedPfaffian.listing_value_canonical` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let f(x,y) be an integer unit for every pair of labels, with f(y,x) = -f(x,y) whenever x and y differ. Define L(f,s) as sign(s) times the product of f(s(2i),s(2i+1)) over i in Fin(n). The value uses integer units throughout.

To normalize s, sort its unordered pairs by their smaller endpoints and reverse each decreasing pair. The whole-pair permutation acts on two copies of Fin(n), so its sign is the square of a sign and equals one. Each individual reversal contributes one transposition and negates exactly its paired factor. The two signs cancel. Reindexing the finite product by the pair permutation proves the displayed equality without dividing by a ring element or excluding an empty pairing.

**Theorem 1.6 (Recognizing a partner map).**

$$\forall n \in \mathbb{N},\; \forall s \in \operatorname{Perm}\left(\operatorname{Fin}\left(2 \cdot n\right)\right),\; \forall p \in \operatorname{P}\left(n\right),\; \operatorname{pairingOfListing}\left(s\right) = p \Leftrightarrow \left(\forall i \in \operatorname{Fin}\left(n\right),\; \operatorname{Apply}\left(p, \operatorname{Apply}\left(s, 2 \cdot i\right)\right) = \operatorname{Apply}\left(s, 2 \cdot i + 1\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/Combinatorics/NormalizedPfaffian.pairing_eq_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A permutation lists a given partner map if and only if each pair of consecutive slots has that partner relation. The forward implication is conjugation of the consecutive pairing. For the reverse implication, every slot is either the first or the second slot of one pair. The first slots satisfy the stated equation, and involutivity determines the second slots. This criterion connects arbitrary listings to actual matching adjacency.

**Definition 1.7 (Listing inversion pairs).**

Lean statement: `D5/S0/Certificates/Combinatorics/NormalizedPfaffian.inversionPairs`

*Formalization.* `D5/S0/Certificates/Combinatorics/NormalizedPfaffian.inversionPairs` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a permutation of Fin(2*n), this finite set contains exactly the position pairs u<v with s(v)<s(u). It is the inversion statistic of the listing itself.

**Definition 1.8 (Lower endpoints of a pairing).**

Lean statement: `D5/S0/Certificates/Combinatorics/NormalizedPfaffian.lowerEndpoints`

*Formalization.* `D5/S0/Certificates/Combinatorics/NormalizedPfaffian.lowerEndpoints` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a fixed point free pairing p, this finite set contains every a with a<p(a), so each edge is represented exactly once by its lower endpoint.

**Definition 1.9 (Crossing edge pairs).**

Lean statement: `D5/S0/Certificates/Combinatorics/NormalizedPfaffian.crossingPairs`

*Formalization.* `D5/S0/Certificates/Combinatorics/NormalizedPfaffian.crossingPairs` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

CrossingPairs p contains ordered lower endpoints a<c satisfying a<c<p(a)<p(c).

**Definition 1.10 (Nested edge pairs).**

Lean statement: `D5/S0/Certificates/Combinatorics/NormalizedPfaffian.nestingPairs`

*Formalization.* `D5/S0/Certificates/Combinatorics/NormalizedPfaffian.nestingPairs` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

NestingPairs p contains ordered lower endpoints a<c satisfying a<c<p(c)<p(a), with each unordered nested edge pair counted once.

**Definition 1.11 (Crossing and two-way nesting equivalence).**

$$\forall n \in \mathbb{N},\; \forall sigma \in \operatorname{Perm}\left(\operatorname{Fin}\left(2 \cdot n\right)\right),\; sigma \in \operatorname{normalizedListings}\left(n\right) \Rightarrow \operatorname{Equiv}\left(\operatorname{InvType}\left(sigma\right), \operatorname{Sum}\left(\operatorname{CrossType}\left(\operatorname{pairingOfListing}\left(sigma\right)\right), \operatorname{Prod}\left(\operatorname{NestType}\left(\operatorname{pairingOfListing}\left(sigma\right)\right), \operatorname{Fin}\left(2\right)\right)\right)\right)$$

*Formalization.* `D5/S0/Certificates/Combinatorics/NormalizedPfaffian.inversionCrossNestEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every normalized listing s, with p=pairingOfListing s, the explicit inverse maps InvType s to CrossType p or to NestType p together with Fin 2. The three cases are (second i, first j) crossing, (second i, first j) nesting orientation zero, and (second i, second j) nesting orientation one; both inverse laws are proved.

**Theorem 1.12 (Inversion cardinality identity).**

$$\forall n \in \mathbb{N},\; \forall sigma \in \operatorname{Perm}\left(\operatorname{Fin}\left(2 \cdot n\right)\right),\; sigma \in \operatorname{normalizedListings}\left(n\right) \Rightarrow \operatorname{FintypeCard}\left(\operatorname{InvType}\left(sigma\right)\right) = \operatorname{FintypeCard}\left(\operatorname{CrossType}\left(\operatorname{pairingOfListing}\left(sigma\right)\right)\right) + 2 \cdot \operatorname{FintypeCard}\left(\operatorname{NestType}\left(\operatorname{pairingOfListing}\left(sigma\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/Combinatorics/NormalizedPfaffian.inversion_card_eq_cross_add_two_nesting_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The equivalence gives the exact finite identity card(Inv)=card(Cross)+2*card(Nest), including n=0 and the empty listing.

**Definition 1.13 (Crossing sign unit).**

Lean statement: `D5/S0/Certificates/Combinatorics/NormalizedPfaffian.crossingUnit`

*Formalization.* `D5/S0/Certificates/Combinatorics/NormalizedPfaffian.crossingUnit` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The crossing unit is the integer sign unit (-1) raised to the cardinality of the crossing-pair subtype.

**Definition 1.14 (Crossing coefficient in a commutative ring).**

Lean statement: `D5/S0/Certificates/Combinatorics/NormalizedPfaffian.crossingCoefficient`

*Formalization.* `D5/S0/Certificates/Combinatorics/NormalizedPfaffian.crossingCoefficient` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

CrossingCoefficient casts the integer value of crossingUnit into an arbitrary CommRing coefficient type.

**Theorem 1.15 (Original Pfaffian equals the independent crossing-signed edge-once sum).**

$$\forall n \in \mathbb{N},\; \forall R \in \operatorname{Type}\left(\right),\; [\operatorname{CommRing}\left(R\right)] \forall A \in \operatorname{Matrix}\left(\operatorname{Fin}\left(2 \cdot n\right), \operatorname{Fin}\left(2 \cdot n\right), R\right),\; \operatorname{pfaffian}\left(A\right) = \sum_{sigma \in \operatorname{normalizedListings}\left(n\right)} \operatorname{crossingCoefficient}\left(\operatorname{pairingOfListing}\left(sigma\right)\right) \cdot \prod_{x \in \operatorname{lowerEndpoints}\left(\operatorname{pairingOfListing}\left(sigma\right)\right)} \operatorname{Apply}\left(A, x, \operatorname{Apply}\left(\operatorname{pairingOfListing}\left(sigma\right), x\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/Combinatorics/NormalizedPfaffian.pfaffian_eq_crossing_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every n, every commutative ring R, and every matrix A over R, the original normalized Pfaffian sum is equal term by term to the sum over the same normalized listings whose coefficient is (-1) raised to the number of crossing edge pairs and whose product ranges over lowerEndpoints(pairingOfListing s), using each paired matrix entry once. The proof uses the pinned permutation-sign product formula, the counted equivalence, the original listing normalization, and no skew-symmetry, division, cancellation, or integer-only specialization.

## References

- Truth anchor: `D5/S0/Certificates/Combinatorics/NormalizedPfaffian.P`
- Truth anchor: `D5/S0/Certificates/Combinatorics/NormalizedPfaffian.canonical_mate`
- Truth anchor: `D5/S0/Certificates/Combinatorics/NormalizedPfaffian.crossingCoefficient`
- Truth anchor: `D5/S0/Certificates/Combinatorics/NormalizedPfaffian.crossingPairs`
- Truth anchor: `D5/S0/Certificates/Combinatorics/NormalizedPfaffian.crossingUnit`
- Truth anchor: `D5/S0/Certificates/Combinatorics/NormalizedPfaffian.inversionCrossNestEquiv`
- Truth anchor: `D5/S0/Certificates/Combinatorics/NormalizedPfaffian.inversionPairs`
- Truth anchor: `D5/S0/Certificates/Combinatorics/NormalizedPfaffian.inversion_card_eq_cross_add_two_nesting_card`
- Truth anchor: `D5/S0/Certificates/Combinatorics/NormalizedPfaffian.listingEquiv`
- Truth anchor: `D5/S0/Certificates/Combinatorics/NormalizedPfaffian.listing_value_canonical`
- Truth anchor: `D5/S0/Certificates/Combinatorics/NormalizedPfaffian.lowerEndpoints`
- Truth anchor: `D5/S0/Certificates/Combinatorics/NormalizedPfaffian.nestingPairs`
- Truth anchor: `D5/S0/Certificates/Combinatorics/NormalizedPfaffian.pairing_eq_iff`
- Truth anchor: `D5/S0/Certificates/Combinatorics/NormalizedPfaffian.pfaffian`
- Truth anchor: `D5/S0/Certificates/Combinatorics/NormalizedPfaffian.pfaffian_eq_crossing_sum`
