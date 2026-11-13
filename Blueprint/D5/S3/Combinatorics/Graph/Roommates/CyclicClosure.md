# Cyclic closure

## Abstract

Six-site cyclic closure for the exact Mertens range-two proof.

A word w of length m has a signed assignment d and Certificate(w,d). The source cycle has m+6 labelled sites, hence supplier parameter n=m+1. Assignment(m) means Fin(m) to the integers. SuccessfulProfile(n) is the subtype of SourceModel.Profile(n) admitting an acceptable stable partial matching. The matching keeps every interior old pair and old single, fulfills each actual exterior request, and uses the existing six-site buffer involution for free sites. The profile retains all first m rankings and places every nonzero buffer partner first.

**Definition 1.1 (Actual involutive source matching).**

$$\forall m \in \mathrm{Nat},\; \forall w \in \mathrm{Word}\left(m\right),\; \forall d \in \mathrm{Assignment}\left(m\right),\; \forall h \in \mathrm{Certificate}\left(w, d\right),\; \mathrm{HasType}\left(\mathrm{matching}\left(h\right), \mathrm{Matching}\left(\mathrm{Fin}\left(m + 6\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/Roommates/CyclicClosure.matching` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The sum of the old interval and the six buffer vertices is identified with the labelled source cycle. Interior reciprocity is supplied by the certificate; the existing request involution supplies all exterior and new pairs. Fixed points represent singles.

**Definition 1.2 (The extended profile).**

$$\forall m \in \mathrm{Nat},\; \forall w \in \mathrm{Word}\left(m\right),\; \forall d \in \mathrm{Assignment}\left(m\right),\; \forall h \in \mathrm{Certificate}\left(w, d\right),\; \mathrm{HasType}\left(\mathrm{profile}\left(h\right), \mathrm{Profile}\left(m + 1\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/Roommates/CyclicClosure.profile` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every old ranking is retained literally. A buffer ranking is the existing partnerFirst permutation for its actual signed assignment, including the fixed deterministic ranking at a single.

**Theorem 1.3 (Acceptable pairs and singles).**

$$\forall m \in \mathrm{Nat},\; \forall w \in \mathrm{Word}\left(m\right),\; \forall d \in \mathrm{Assignment}\left(m\right),\; \forall h \in \mathrm{Certificate}\left(w, d\right),\; \mathrm{IsAcceptable}\left(\mathrm{ring}\left(m + 1\right), \mathrm{matching}\left(h\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Roommates/CyclicClosure.acceptable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each assignment is zero or one of the four literal signed source offsets. Thus every nonfixed pair is an actual acceptable edge of the source ring.

**Theorem 1.4 (No cyclic blocking edge).**

$$\forall m \in \mathrm{Nat},\; \forall w \in \mathrm{Word}\left(m\right),\; \forall d \in \mathrm{Assignment}\left(m\right),\; \forall h \in \mathrm{Certificate}\left(w, d\right),\; \mathrm{IsStable}\left(\mathrm{ring}\left(m + 1\right), \mathrm{rank}\left(\mathrm{profile}\left(h\right)\right), \mathrm{matching}\left(h\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Roommates/CyclicClosure.stable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Old--old edges use the exact rank transport and have no new wrap edge. A matched buffer endpoint ranks its partner first and rejects any proposed improvement. A buffer single is at position 3 or 4 in one-based numbering; all four cyclic neighbors are distinct matched buffer vertices. This also excludes an edge from an old single to a new single. The argument includes m=1 and its extra edge between buffer positions 1 and 6, m=2, and odd m. There is no parity or eventual-length hypothesis.

**Definition 1.5 (Map on successful profiles).**

$$\forall m \in \mathrm{Nat},\; \forall w \in \mathrm{CertifiedWord}\left(m\right),\; \mathrm{HasType}\left(\mathrm{close}\left(w\right), \mathrm{SuccessfulProfile}\left(m + 1\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/Roommates/CyclicClosure.close` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Choose one certificate per certified word, construct its profile and stable matching, and retain only the successful profile. Certificates and matching witnesses are not counted.

**Theorem 1.6 (Recover the old ranking word).**

$$\forall m \in \mathrm{Nat},\; \mathrm{Injective}\left(\mathrm{close}\left(m\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Roommates/CyclicClosure.close_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Equality of output profiles gives equality at each first-m coordinate, recovering the input word independently of which certificate was chosen.

**Theorem 1.7 (The lower cyclic count comparison).**

$$\forall m \in \mathrm{Nat},\; \mathrm{count}\left(m\right) \le \mathrm{card}\left(\mathrm{SuccessfulProfile}\left(m + 1\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Roommates/CyclicClosure.count_le_successful_profile_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Write b(m) for the number of certified ranking words, and a(n) for the number of successful labelled source profiles with supplier parameter n and n+5 sites. The injection proves b(m) <= a(m+1), equivalently b(m) <= a_(m+6) when the subscript records sites. GrowthTransfer.result consumes this bridge for the exact d=1,r=2 probability theorem. General Conjecture 3 remains outside this scope.

**Theorem 1.8 (wrap_val).**

$$\forall n \in \mathrm{Nat},\; \forall z \in \mathrm{Int},\; \mathrm{intVal}\left(\mathrm{wrap}\left(n, z\right)\right) = \mathrm{mod}\left(z, n + 5\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Roommates/CyclicClosure.wrap_val` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The cyclic closure uses this coordinate or rank identity with the literal supplier offsets.

**Theorem 1.9 (wrap_index).**

$$\forall n \in \mathrm{Nat},\; \forall i \in \mathrm{Fin}\left(n + 5\right),\; \mathrm{wrap}\left(n, \mathrm{intVal}\left(i\right)\right) = i$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Roommates/CyclicClosure.wrap_index` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The cyclic closure uses this coordinate or rank identity with the literal supplier offsets.

**Theorem 1.10 (wrap_add).**

$$\forall n \in \mathrm{Nat},\; \forall a \in \mathrm{Int},\; \forall b \in \mathrm{Int},\; \mathrm{wrap}\left(n, a + b\right) = \mathrm{wrap}\left(n, a\right) + \mathrm{wrap}\left(n, b\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Roommates/CyclicClosure.wrap_add` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The cyclic closure uses this coordinate or rank identity with the literal supplier offsets.

**Theorem 1.11 (wrap_signed).**

$$\forall n \in \mathrm{Nat},\; \forall s \in \mathrm{Fin}\left(4\right),\; \mathrm{wrap}\left(n, \mathrm{signed}\left(s\right)\right) = \mathrm{offset}\left(n, s\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Roommates/CyclicClosure.wrap_signed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The cyclic closure uses this coordinate or rank identity with the literal supplier offsets.

**Theorem 1.12 (signed_bounds).**

$$\forall s \in \mathrm{Fin}\left(4\right),\; \mathrm{neg}\left(2\right) \le \mathrm{signed}\left(s\right) \land \left(\mathrm{signed}\left(s\right) \le 2 \land \mathrm{signed}\left(s\right) \ne 0\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Roommates/CyclicClosure.signed_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The cyclic closure uses this coordinate or rank identity with the literal supplier offsets.

**Theorem 1.13 (rank_wrap).**

$$\forall n \in \mathrm{Nat},\; \forall p \in \mathrm{Profile}\left(n\right),\; \forall i \in \mathrm{Fin}\left(n + 5\right),\; \forall a \in \mathrm{Int},\; \left(\mathrm{neg}\left(2\right) \le a \land a \le 2\right) \Rightarrow \mathrm{rank}\left(p, i, \mathrm{wrap}\left(n, \mathrm{intVal}\left(i\right) + a\right)\right) = \mathrm{offsetRank}\left(\mathrm{apply}\left(p, i\right), a\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Roommates/CyclicClosure.rank_wrap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The cyclic closure uses this coordinate or rank identity with the literal supplier offsets.

**Theorem 1.14 (closing_old_nonblocking).**

Lean statement: `D5/S3/Combinatorics/Graph/Roommates/CyclicClosure.closing_old_nonblocking`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Roommates/CyclicClosure.closing_old_nonblocking` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every old--old edge in the literal source cycle has the original certificate nonblocking test, with actual signed-offset ranks for exterior partners and rank four for singles. The complete new and mixed edge argument and closure injection are supplied by CyclicClosure.

**Theorem 1.15 (closing_request_source_target).**

Lean statement: `D5/S3/Combinatorics/Graph/Roommates/CyclicClosure.closing_request_source_target`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Roommates/CyclicClosure.closing_request_source_target` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual buffer target of every closing request is the original signed-offset neighbor in the literal source cycle of size m+6. Both left and right exterior requests preserve their cyclic destinations.

**Theorem 1.16 (closing_old_edge_local).**

Lean statement: `D5/S3/Combinatorics/Graph/Roommates/CyclicClosure.closing_old_edge_local`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Roommates/CyclicClosure.closing_old_edge_local` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A six-site closing buffer creates no wrap edge between old vertices. Every source edge with two old endpoints has integer separation at most two, including old lengths one and two.

**Definition 1.17 (signed).**

Lean statement: `D5/S3/Combinatorics/Graph/Roommates/CyclicClosure.signed`

*Formalization.* `D5/S3/Combinatorics/Graph/Roommates/CyclicClosure.signed` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The four supplier labels represent signed offsets 1,2,-1,-2 in that order.

**Definition 1.18 (wrap).**

Lean statement: `D5/S3/Combinatorics/Graph/Roommates/CyclicClosure.wrap`

*Formalization.* `D5/S3/Combinatorics/Graph/Roommates/CyclicClosure.wrap` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Integer coordinates are reduced modulo N=n+5; all four neighbors remain distinct, including N=5.

**Definition 1.19 (displacement).**

Lean statement: `D5/S3/Combinatorics/Graph/Roommates/CyclicClosure.displacement`

*Formalization.* `D5/S3/Combinatorics/Graph/Roommates/CyclicClosure.displacement` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A fixed point is a single with displacement zero. An acceptable matched vertex retains its unique signed source offset when the cycle is cut.

**Theorem 1.20 (cut_certificate).**

Lean statement: `D5/S3/Combinatorics/Graph/Roommates/CyclicClosure.cut_certificate`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Roommates/CyclicClosure.cut_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Cut every acceptable stable partial matching to a certificate on the unchanged ranking word. Reciprocity holds for integer targets that remain inside. Target injectivity includes exterior targets, by reduction to the injective cyclic partner permutation. Internal stability uses exact rank correspondence and strict rank injectivity; singles retain rank four.

**Definition 1.21 (cut).**

Lean statement: `D5/S3/Combinatorics/Graph/Roommates/CyclicClosure.cut`

*Formalization.* `D5/S3/Combinatorics/Graph/Roommates/CyclicClosure.cut` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The map preserves the ranking word exactly and changes only the existential proof. It counts profiles once, independently of the number of stable matching witnesses.

**Theorem 1.22 (source_count_le_open_count).**

Lean statement: `D5/S3/Combinatorics/Graph/Roommates/CyclicClosure.source_count_le_open_count`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Roommates/CyclicClosure.source_count_le_open_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every n>=0, hence every cycle size N=n+5>=5, the number of successful source profiles is at most the number of certified words of length N. There is no parity restriction.

**Theorem 1.23 (source_probability_eq).**

Lean statement: `D5/S3/Combinatorics/Graph/Roommates/CyclicClosure.source_probability_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Roommates/CyclicClosure.source_probability_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each of N independent uniform neighbor rankings has 24 choices. The literal supplier probability is the number of successful profiles divided by 24^N.

**Theorem 1.24 (source_probability_le_open_proportion).**

Lean statement: `D5/S3/Combinatorics/Graph/Roommates/CyclicClosure.source_probability_le_open_proportion`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Roommates/CyclicClosure.source_probability_le_open_proportion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The cyclic cut gives the upper comparison p_N<=b_N/24^N. CyclicClosure supplies the inverse closure injection. PaddedCompletion supplies supermultiplicativity, and GrowthTransfer.result combines these bounds into the exact same-q theorem.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Roommates/CyclicClosure.acceptable`
- Truth anchor: `D5/S3/Combinatorics/Graph/Roommates/CyclicClosure.close`
- Truth anchor: `D5/S3/Combinatorics/Graph/Roommates/CyclicClosure.close_injective`
- Truth anchor: `D5/S3/Combinatorics/Graph/Roommates/CyclicClosure.closing_old_edge_local`
- Truth anchor: `D5/S3/Combinatorics/Graph/Roommates/CyclicClosure.closing_old_nonblocking`
- Truth anchor: `D5/S3/Combinatorics/Graph/Roommates/CyclicClosure.closing_request_source_target`
- Truth anchor: `D5/S3/Combinatorics/Graph/Roommates/CyclicClosure.count_le_successful_profile_count`
- Truth anchor: `D5/S3/Combinatorics/Graph/Roommates/CyclicClosure.cut`
- Truth anchor: `D5/S3/Combinatorics/Graph/Roommates/CyclicClosure.cut_certificate`
- Truth anchor: `D5/S3/Combinatorics/Graph/Roommates/CyclicClosure.displacement`
- Truth anchor: `D5/S3/Combinatorics/Graph/Roommates/CyclicClosure.matching`
- Truth anchor: `D5/S3/Combinatorics/Graph/Roommates/CyclicClosure.profile`
- Truth anchor: `D5/S3/Combinatorics/Graph/Roommates/CyclicClosure.rank_wrap`
- Truth anchor: `D5/S3/Combinatorics/Graph/Roommates/CyclicClosure.signed`
- Truth anchor: `D5/S3/Combinatorics/Graph/Roommates/CyclicClosure.signed_bounds`
- Truth anchor: `D5/S3/Combinatorics/Graph/Roommates/CyclicClosure.source_count_le_open_count`
- Truth anchor: `D5/S3/Combinatorics/Graph/Roommates/CyclicClosure.source_probability_eq`
- Truth anchor: `D5/S3/Combinatorics/Graph/Roommates/CyclicClosure.source_probability_le_open_proportion`
- Truth anchor: `D5/S3/Combinatorics/Graph/Roommates/CyclicClosure.stable`
- Truth anchor: `D5/S3/Combinatorics/Graph/Roommates/CyclicClosure.wrap`
- Truth anchor: `D5/S3/Combinatorics/Graph/Roommates/CyclicClosure.wrap_add`
- Truth anchor: `D5/S3/Combinatorics/Graph/Roommates/CyclicClosure.wrap_index`
- Truth anchor: `D5/S3/Combinatorics/Graph/Roommates/CyclicClosure.wrap_signed`
- Truth anchor: `D5/S3/Combinatorics/Graph/Roommates/CyclicClosure.wrap_val`
- Dependency: [D5/S3/Combinatorics/Graph/Roommates/OpenCertificates](OpenCertificates.md)
- Dependency: [D5/S3/Combinatorics/Graph/Roommates/PaddedCompletion](PaddedCompletion.md)
- Dependency: [D5/S3/Combinatorics/Graph/Roommates/SourceModel](SourceModel.md)
