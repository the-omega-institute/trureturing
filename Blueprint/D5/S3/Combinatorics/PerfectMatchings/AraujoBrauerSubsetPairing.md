# AraujoBrauerSubsetPairing

## Abstract

Constructive results for complete mappings of diagram monoids.

**Definition 1.1 (SubsetPairing).**

$$structure SubsetPairing (X : Type *) [DecidableEq X] (r : \mathbb{N}) (triangle : Finset (Finset X)) where pair : Finset X \to Finset X involutive : Function . Involutive pair card : \forall s , (pair s) . card = s . card fixed : \forall s , s . card = r \to (pair s = s \iff s \in triangle) adjacent : \forall s , s . card = r \to s \neg \in triangle \to (Finset . inter s (pair s)) . card + 1 = r$$

*Formalization.* `D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerSubsetPairing.SubsetPairing` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The formula gives the quantified defining expression.

**Definition 1.2 (baseTwoTriangle).**

$$baseTwoTriangle = (\{\{0 , 1\} , \{0 , 2\} , \{1 , 2\}\})$$

*Formalization.* `D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerSubsetPairing.baseTwoTriangle` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The formula gives the quantified defining expression.

**Definition 1.3 (baseThreeTriangle).**

$$baseThreeTriangle = (\{\{0 , 1 , 3\} , \{0 , 2 , 3\} , \{1 , 2 , 3\}\})$$

*Formalization.* `D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerSubsetPairing.baseThreeTriangle` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The formula gives the quantified defining expression.

**Theorem 1.4 (rank_two_subset_pairing).**

$$\forall (k : \mathbb{N}) , \exists e : Function . Embedding (Fin 6) (Fin (6 + 4 * k)) , Nonempty (SubsetPairing (Fin (6 + 4 * k)) 2 (baseTwoTriangle . image (\lambda s \mapsto s . map e)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerSubsetPairing.rank_two_subset_pairing` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The formula gives the quantified statement.

**Theorem 1.5 (rank_three_subset_pairing).**

$$\forall (k : \mathbb{N}) , \exists e : Function . Embedding (Fin 7) (Fin (7 + 4 * k)) , Nonempty (SubsetPairing (Fin (7 + 4 * k)) 3 (baseThreeTriangle . image (\lambda s \mapsto s . map e)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerSubsetPairing.rank_three_subset_pairing` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The formula gives the quantified statement.

## References

- Truth anchor: `D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerSubsetPairing.SubsetPairing`
- Truth anchor: `D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerSubsetPairing.baseThreeTriangle`
- Truth anchor: `D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerSubsetPairing.baseTwoTriangle`
- Truth anchor: `D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerSubsetPairing.rank_three_subset_pairing`
- Truth anchor: `D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerSubsetPairing.rank_two_subset_pairing`
