# A quantale unit from prime residue rings

## Abstract

A ring without a multiplicative identity whose additive-submonoid quantale is unital.

**Theorem 1.1 (Existence in Mesyan's Question 36).**

$$\exists (A: Type), \exists (s: NonUnitalRing A), (\exists (a: A), a \neq 0) \land ((\forall (e: A), \exists (a: A), e \cdot a \neq a \lor a \cdot e \neq a) \land (\exists (E: AddSubmonoid A), \forall (M: AddSubmonoid A), E \cdot M = M \land M \cdot E = M))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/ResidueRings/MesyanQuantaleUnit.question36_exists` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Zachary Mesyan (2026). *Quantales Arising From Rings*. URL: <https://arxiv.org/abs/2611.31109v1>.

*Commentary.*

There is a nonzero associative ring A with no two-sided multiplicative identity and an additive submonoid E that is a two-sided unit for multiplication with every additive submonoid M of A. The ring structure on the carrier A is denoted by s. In the displayed statement, multiplication of submonoids takes all sums of a positive finite number of pairwise products, with the first factor from the left submonoid and the second from the right. The proof identifies this product from Definition 4 with Mathlib's multiplication.

Take A to be the ring of finitely supported tuples of residues modulo the primes, with coordinatewise operations. The tuple supported at 2 with value one there is nonzero. For each candidate identity e, a prime outside its support gives a singleton-supported tuple on which left multiplication by e vanishes.

Take E to be the whole ring as an additive submonoid. For any r in the ring and a in M, the Chinese remainder theorem gives one natural number agreeing with the residues of r at all primes in the support of a. Multiplication by r on a therefore agrees with repeated addition, so every product summand lies in M. In the other direction the tuple equal to one on the support of a and zero elsewhere gives a one-term product for a. Commutativity supplies the right unit law. This settles the existence clause of Question 36. The classification clause is a separate question.

## References

- Truth anchor: `D5/S3/Arith/ResidueRings/MesyanQuantaleUnit.question36_exists`
