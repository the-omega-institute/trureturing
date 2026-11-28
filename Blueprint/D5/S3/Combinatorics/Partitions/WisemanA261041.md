# Wiseman A261041 and the swap scan

## Abstract

A reversible swap scan matches the two partition classes in OEIS A261041.

**Definition 1.1 (Partial partitions).**

$$\forall (n: \mathbb{N}), \operatorname{PartialPartition}\left(n\right) : \{ carrier: \operatorname{Set}\left(\operatorname{Fin}\left(n\right)\right), blocks: \operatorname{Setoid}\left(carrier\right) \}$$

*Formalization.* `D5/S3/Combinatorics/Partitions/WisemanA261041.PartialPartition` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A partial partition is a dependent structure. Its carrier is an arbitrary subset of the interval and its blocks are a setoid on the subtype of points in that carrier. Position i represents the integer i+1.

**Definition 1.2 (Sharing a block).**

$$\forall (n: \mathbb{N}), \forall (p: \operatorname{PartialPartition}\left(n\right)), \forall (i: \operatorname{Fin}\left(n\right)), \forall (j: \operatorname{Fin}\left(n\right)), \operatorname{SameBlock}\left(p, i, j\right) \iff \exists (hi: i \in p.carrier), \exists (hj: j \in p.carrier), p.blocks\left(\langle i, hi\rangle, \langle j, hj\rangle\right)$$

*Formalization.* `D5/S3/Combinatorics/Partitions/WisemanA261041.SameBlock` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Both points must belong to the carrier. The setoid compares the corresponding subtype elements.

**Definition 1.3 (Adjacent positions).**

$$\forall (n: \mathbb{N}), \forall (p: \operatorname{PartialPartition}\left(n\right)), \operatorname{NoConsecutive}\left(p\right) \iff \forall (i: \mathbb{N}), \forall (h: i + 1 < n), \neg \operatorname{SameBlock}\left(p, i_{0}, i_{1}\right)$$

*Formalization.* `D5/S3/Combinatorics/Partitions/WisemanA261041.NoConsecutive` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The condition forbids each consecutive pair in the ambient interval from sharing a block. Here and below, a subscript j on i denotes the finite index with value i+j and the bound inferred from h.

**Definition 1.4 (Consecutive triples).**

$$\forall (n: \mathbb{N}), \forall (s: \operatorname{Setoid}\left(\operatorname{Fin}\left(n + 1\right)\right)), \operatorname{TripleCondition}\left(s\right) \iff \forall (i: \mathbb{N}), \forall (h: i + 2 < n + 1), s\left(i_{0}, i_{2}\right) \implies s\left(i_{0}, i_{1}\right)$$

*Formalization.* `D5/S3/Combinatorics/Partitions/WisemanA261041.TripleCondition` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

When the endpoints of a valid consecutive triple share a block, the middle is in their block.

**Definition 1.5 (The partial partition class).**

$$\forall (n: \mathbb{N}), \operatorname{Left}\left(n\right) = \{ p: \operatorname{PartialPartition}\left(n\right) \mid \operatorname{NoConsecutive}\left(p\right) \}$$

*Formalization.* `D5/S3/Combinatorics/Partitions/WisemanA261041.Left` (`✓ std3`).

*Citation.* Gus Wiseman (2019). *OEIS A261041, comment on partial and full set partitions*. URL: <https://oeis.org/A261041/internal>.

*Commentary.*

The carrier may be any subset, including the empty subset. This is the class counted by the OEIS entry.

**Definition 1.6 (The full partition class).**

$$\forall (n: \mathbb{N}), \operatorname{Right}\left(n\right) = \{ s: \operatorname{Setoid}\left(\operatorname{Fin}\left(n + 1\right)\right) \mid \operatorname{TripleCondition}\left(s\right) \}$$

*Formalization.* `D5/S3/Combinatorics/Partitions/WisemanA261041.Right` (`✓ std3`).

*Citation.* Gus Wiseman (2019). *OEIS A261041, comment on partial and full set partitions*. URL: <https://oeis.org/A261041/internal>.

*Commentary.*

The setoid partitions all n+1 positions. The consecutive-triple implication is the condition in the OEIS comment.

**Definition 1.7 (The reversible bijection).**

$$\forall (n: \mathbb{N}), \operatorname{wisemanBijection}\left(n\right) : \operatorname{Left}\left(n\right) \equiv \operatorname{Right}\left(n\right)$$

*Formalization.* `D5/S3/Combinatorics/Partitions/WisemanA261041.wisemanBijection` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The value is the restriction of the composite of padding and the swap scan on full partitions. Padding adds a first point whose block contains the omitted points and the new point. Label each padded block by its least position. Starting from the identity permutation and output zero, emit the current input label under the current permutation, then compose on the right with its swap with zero. The inverse recovers each input label using the inverse current permutation before making the same update. Relabelings fixing zero commute with the scan, so the maps descend to literal partitions. Equal output endpoints with a different middle occur exactly at two successive equal nonzero input labels. The scan preserves the set of labels. The same construction has a pointwise one-block shift under the quotient cardinalities, which is retained here as explanatory refinement. The formal result below uses the reversible equivalence itself. In the formula below, restriction is the proved equivalence of the adjacent-pair and consecutive-triple conditions under the composite.

$\forall (n: \mathbb{N}), \operatorname{wisemanBijection}\left(n\right) = \operatorname{subtypeEquiv}\left(\operatorname{trans}\left(\operatorname{padEquiv}\left(n\right), \operatorname{partitionEquiv}\left(n\right)\right), \operatorname{restriction}\left(n\right)\right)$

**Theorem 1.8 (The counting identity).**

$$\forall (n: \mathbb{N}), \operatorname{Nat.card}\left(\operatorname{Left}\left(n\right)\right) = \operatorname{Nat.card}\left(\operatorname{Right}\left(n\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/WisemanA261041.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gus Wiseman (2019). *OEIS A261041, comment on partial and full set partitions*. URL: <https://oeis.org/A261041/internal>.

*Commentary.*

Taking natural cardinalities gives equality for every natural n. At zero the empty partial partition corresponds to the one-block partition of the singleton interval.

## References

- Truth anchor: `D5/S3/Combinatorics/Partitions/WisemanA261041.Left`
- Truth anchor: `D5/S3/Combinatorics/Partitions/WisemanA261041.NoConsecutive`
- Truth anchor: `D5/S3/Combinatorics/Partitions/WisemanA261041.PartialPartition`
- Truth anchor: `D5/S3/Combinatorics/Partitions/WisemanA261041.Right`
- Truth anchor: `D5/S3/Combinatorics/Partitions/WisemanA261041.SameBlock`
- Truth anchor: `D5/S3/Combinatorics/Partitions/WisemanA261041.TripleCondition`
- Truth anchor: `D5/S3/Combinatorics/Partitions/WisemanA261041.result`
- Truth anchor: `D5/S3/Combinatorics/Partitions/WisemanA261041.wisemanBijection`
