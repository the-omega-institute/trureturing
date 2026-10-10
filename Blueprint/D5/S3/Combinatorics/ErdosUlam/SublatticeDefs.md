# Boolean sublattices and prefix chains

## Abstract

Finite Boolean sublattices are represented by subsets or by bitmasks.

**Definition 1.1 (Nonempty sublattices).**

$$\forall n \in \mathrm{Nat},\; \forall L \in \operatorname{Finset}\left(\operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right)\right),\; \operatorname{IsSublattice}\left(L\right) \Leftrightarrow \left(\operatorname{Nonempty}\left(L\right) \land \left(\forall A \in \operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right),\; A \in L \Rightarrow \left(\forall B \in \operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right),\; B \in L \Rightarrow \left(\operatorname{union}\left(A, B\right) \in L \land \operatorname{inter}\left(A, B\right) \in L\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/ErdosUlam/SublatticeDefs.IsSublattice` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A sublattice is a nonempty finite family closed under union and intersection.

**Definition 1.2 (Constant colour).**

$$\forall n \in \mathrm{Nat},\; \forall chi \in \operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right) \to \mathrm{Bool},\; \forall L \in \operatorname{Finset}\left(\operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right)\right),\; \operatorname{Monochromatic}\left(chi, L\right) \Leftrightarrow \left(\exists b \in \mathrm{Bool},\; \forall A \in \operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right),\; A \in L \Rightarrow \operatorname{chi}\left(A\right) = b\right)$$

*Formalization.* `D5/S3/Combinatorics/ErdosUlam/SublatticeDefs.Monochromatic` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

All members of a monochromatic family have one common Boolean colour.

**Theorem 1.3 (Cardinality of a prefix).**

$$\forall n \in \mathrm{Nat},\; \forall r \in \mathrm{Nat},\; r \le n \Rightarrow \operatorname{card}\left(\operatorname{initialSegment}\left(n, r\right)\right) = r$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ErdosUlam/SublatticeDefs.prefix_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The prefix of rank r consists of the first r elements when r is at most n. Prefixes are nested by rank. Bitmask decoding sends bitwise union and intersection to the corresponding subset operations.

## References

- Truth anchor: `D5/S3/Combinatorics/ErdosUlam/SublatticeDefs.IsSublattice`
- Truth anchor: `D5/S3/Combinatorics/ErdosUlam/SublatticeDefs.Monochromatic`
- Truth anchor: `D5/S3/Combinatorics/ErdosUlam/SublatticeDefs.prefix_card`
