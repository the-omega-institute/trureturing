# Equal pair differences and unequal disjoint triple collisions

## Abstract

Two nine-point spectra share every directed difference count and have different disjoint triple counts.

**Definition 1.1 (Determination by the signed difference profile).**

$$\begin{aligned}&Determination \iff \forall A,B: \operatorname{Fin}\left(9\right) \Rightarrow \mathbb{N},\\&(\operatorname{Injective}\left(A\right) \land \operatorname{Injective}\left(B\right) \land (\forall k \in \mathbb{Z}, \operatorname{D}\left(A, k\right) = \operatorname{D}\left(B, k\right)))\\&\quad\longrightarrow \operatorname{R}\left(A\right) = \operatorname{R}\left(B\right).\end{aligned}$$

*Formalization.* `D5/S3/Fourier/Concentration/HomometricTripleCollision.differencesDetermineTripleMass` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The maps A and B are injective. For any integer k, D(A,k) counts all ordered pairs of indices in A whose frequency difference is k. R(A) counts ordered pairs of ordered triples in A of equal sum with disjoint index supports. Repeated indices within a triple are allowed.

**Theorem 1.2 (The determination claim is false).**

$$\neg Determination$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Concentration/HomometricTripleCollision.differences_do_not_determine_triple_mass` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Take the nine pair sums of {0,1,3} and {0,4,9} for A. For B, take the nine pair differences and shift each by 9. Both sets lie in [0,12]. For each ordered pair of grid indices, exchange the two coordinates from the second factor. This is an involution that preserves the signed gap when transferring from A to B.

Counting the admissible right triples for every left triple gives 5976 for A and 5952 for B. The count uses exact integral sums, so it also gives the unit-weight near-collision mass for each real resolution from zero inclusive to one exclusive.

## References

- Truth anchor: `D5/S3/Fourier/Concentration/HomometricTripleCollision.differencesDetermineTripleMass`
- Truth anchor: `D5/S3/Fourier/Concentration/HomometricTripleCollision.differences_do_not_determine_triple_mass`
