# CyclicBridge

## Abstract

Cyclic cut and rank transport for the exact Mertens range-two proof.

Declarations without a displayed formula retain explicit statement-projection gaps. Their descriptions state the model and proof roles; they do not claim a rendered formula for an unsupported projection.

**Theorem 1.1 (wrap_val).**

$$\forall n \in \mathrm{Nat},\; \forall z \in \mathrm{Int},\; \mathrm{intVal}\left(\mathrm{wrap}\left(n, z\right)\right) = \mathrm{mod}\left(z, n + 5\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Roommates/CyclicBridge.wrap_val` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The cyclic closure uses this coordinate or rank identity with the literal supplier offsets.

**Theorem 1.2 (wrap_index).**

$$\forall n \in \mathrm{Nat},\; \forall i \in \mathrm{Fin}\left(n + 5\right),\; \mathrm{wrap}\left(n, \mathrm{intVal}\left(i\right)\right) = i$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Roommates/CyclicBridge.wrap_index` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The cyclic closure uses this coordinate or rank identity with the literal supplier offsets.

**Theorem 1.3 (wrap_add).**

$$\forall n \in \mathrm{Nat},\; \forall a \in \mathrm{Int},\; \forall b \in \mathrm{Int},\; \mathrm{wrap}\left(n, a + b\right) = \mathrm{wrap}\left(n, a\right) + \mathrm{wrap}\left(n, b\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Roommates/CyclicBridge.wrap_add` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The cyclic closure uses this coordinate or rank identity with the literal supplier offsets.

**Theorem 1.4 (wrap_signed).**

$$\forall n \in \mathrm{Nat},\; \forall s \in \mathrm{Fin}\left(4\right),\; \mathrm{wrap}\left(n, \mathrm{signed}\left(s\right)\right) = \mathrm{offset}\left(n, s\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Roommates/CyclicBridge.wrap_signed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The cyclic closure uses this coordinate or rank identity with the literal supplier offsets.

**Theorem 1.5 (signed_bounds).**

$$\forall s \in \mathrm{Fin}\left(4\right),\; \mathrm{neg}\left(2\right) \le \mathrm{signed}\left(s\right) \land \left(\mathrm{signed}\left(s\right) \le 2 \land \mathrm{signed}\left(s\right) \ne 0\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Roommates/CyclicBridge.signed_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The cyclic closure uses this coordinate or rank identity with the literal supplier offsets.

**Theorem 1.6 (rank_wrap).**

$$\forall n \in \mathrm{Nat},\; \forall p \in \mathrm{Profile}\left(n\right),\; \forall i \in \mathrm{Fin}\left(n + 5\right),\; \forall a \in \mathrm{Int},\; \left(\mathrm{neg}\left(2\right) \le a \land a \le 2\right) \Rightarrow \mathrm{rank}\left(p, i, \mathrm{wrap}\left(n, \mathrm{intVal}\left(i\right) + a\right)\right) = \mathrm{offsetRank}\left(\mathrm{apply}\left(p, i\right), a\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Roommates/CyclicBridge.rank_wrap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The cyclic closure uses this coordinate or rank identity with the literal supplier offsets.

**Theorem 1.7 (closing_old_nonblocking).**

Lean statement: `D5/S3/Combinatorics/Graph/Roommates/CyclicBridge.closing_old_nonblocking`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Roommates/CyclicBridge.closing_old_nonblocking` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every old--old edge in the literal source cycle has the original certificate nonblocking test, with actual signed-offset ranks for exterior partners and rank four for singles. The complete new and mixed edge argument and closure injection are supplied by CyclicClosure.

**Theorem 1.8 (closing_request_source_target).**

Lean statement: `D5/S3/Combinatorics/Graph/Roommates/CyclicBridge.closing_request_source_target`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Roommates/CyclicBridge.closing_request_source_target` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual buffer target of every closing request is the original signed-offset neighbor in the literal source cycle of size m+6. Both left and right exterior requests preserve their cyclic destinations.

**Theorem 1.9 (closing_old_edge_local).**

Lean statement: `D5/S3/Combinatorics/Graph/Roommates/CyclicBridge.closing_old_edge_local`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Roommates/CyclicBridge.closing_old_edge_local` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A six-site closing buffer creates no wrap edge between old vertices. Every source edge with two old endpoints has integer separation at most two, including old lengths one and two.

**Definition 1.10 (signed).**

Lean statement: `D5/S3/Combinatorics/Graph/Roommates/CyclicBridge.signed`

*Formalization.* `D5/S3/Combinatorics/Graph/Roommates/CyclicBridge.signed` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The four supplier labels represent signed offsets 1,2,-1,-2 in that order.

**Definition 1.11 (wrap).**

Lean statement: `D5/S3/Combinatorics/Graph/Roommates/CyclicBridge.wrap`

*Formalization.* `D5/S3/Combinatorics/Graph/Roommates/CyclicBridge.wrap` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Integer coordinates are reduced modulo N=n+5; all four neighbors remain distinct, including N=5.

**Definition 1.12 (displacement).**

Lean statement: `D5/S3/Combinatorics/Graph/Roommates/CyclicBridge.displacement`

*Formalization.* `D5/S3/Combinatorics/Graph/Roommates/CyclicBridge.displacement` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A fixed point is a single with displacement zero. An acceptable matched vertex retains its unique signed source offset when the cycle is cut.

**Theorem 1.13 (cut_certificate).**

Lean statement: `D5/S3/Combinatorics/Graph/Roommates/CyclicBridge.cut_certificate`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Roommates/CyclicBridge.cut_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Cut every acceptable stable partial matching to a certificate on the unchanged ranking word. Reciprocity holds for integer targets that remain inside. Target injectivity includes exterior targets, by reduction to the injective cyclic partner permutation. Internal stability uses exact rank correspondence and strict rank injectivity; singles retain rank four.

**Definition 1.14 (cut).**

Lean statement: `D5/S3/Combinatorics/Graph/Roommates/CyclicBridge.cut`

*Formalization.* `D5/S3/Combinatorics/Graph/Roommates/CyclicBridge.cut` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The map preserves the ranking word exactly and changes only the existential proof. It counts profiles once, independently of the number of stable matching witnesses.

**Theorem 1.15 (source_count_le_open_count).**

Lean statement: `D5/S3/Combinatorics/Graph/Roommates/CyclicBridge.source_count_le_open_count`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Roommates/CyclicBridge.source_count_le_open_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every n>=0, hence every cycle size N=n+5>=5, the number of successful source profiles is at most the number of certified words of length N. There is no parity restriction.

**Theorem 1.16 (source_probability_eq).**

Lean statement: `D5/S3/Combinatorics/Graph/Roommates/CyclicBridge.source_probability_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Roommates/CyclicBridge.source_probability_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each of N independent uniform neighbor rankings has 24 choices. The literal supplier probability is the number of successful profiles divided by 24^N.

**Theorem 1.17 (source_probability_le_open_proportion).**

Lean statement: `D5/S3/Combinatorics/Graph/Roommates/CyclicBridge.source_probability_le_open_proportion`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Roommates/CyclicBridge.source_probability_le_open_proportion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The cyclic cut gives the upper comparison p_N<=b_N/24^N. CyclicClosure supplies the inverse closure injection. Padded supermultiplicativity and the exact same-q theorem remain separate obligations.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Roommates/CyclicBridge.closing_old_edge_local`
- Truth anchor: `D5/S3/Combinatorics/Graph/Roommates/CyclicBridge.closing_old_nonblocking`
- Truth anchor: `D5/S3/Combinatorics/Graph/Roommates/CyclicBridge.closing_request_source_target`
- Truth anchor: `D5/S3/Combinatorics/Graph/Roommates/CyclicBridge.cut`
- Truth anchor: `D5/S3/Combinatorics/Graph/Roommates/CyclicBridge.cut_certificate`
- Truth anchor: `D5/S3/Combinatorics/Graph/Roommates/CyclicBridge.displacement`
- Truth anchor: `D5/S3/Combinatorics/Graph/Roommates/CyclicBridge.rank_wrap`
- Truth anchor: `D5/S3/Combinatorics/Graph/Roommates/CyclicBridge.signed`
- Truth anchor: `D5/S3/Combinatorics/Graph/Roommates/CyclicBridge.signed_bounds`
- Truth anchor: `D5/S3/Combinatorics/Graph/Roommates/CyclicBridge.source_count_le_open_count`
- Truth anchor: `D5/S3/Combinatorics/Graph/Roommates/CyclicBridge.source_probability_eq`
- Truth anchor: `D5/S3/Combinatorics/Graph/Roommates/CyclicBridge.source_probability_le_open_proportion`
- Truth anchor: `D5/S3/Combinatorics/Graph/Roommates/CyclicBridge.wrap`
- Truth anchor: `D5/S3/Combinatorics/Graph/Roommates/CyclicBridge.wrap_add`
- Truth anchor: `D5/S3/Combinatorics/Graph/Roommates/CyclicBridge.wrap_index`
- Truth anchor: `D5/S3/Combinatorics/Graph/Roommates/CyclicBridge.wrap_signed`
- Truth anchor: `D5/S3/Combinatorics/Graph/Roommates/CyclicBridge.wrap_val`
- Dependency: [D5/S3/Combinatorics/Graph/Roommates/OpenCertificates](OpenCertificates.md)
- Dependency: [D5/S3/Combinatorics/Graph/Roommates/PaddedCompletion](PaddedCompletion.md)
- Dependency: [D5/S3/Combinatorics/Graph/Roommates/SourceModel](SourceModel.md)
