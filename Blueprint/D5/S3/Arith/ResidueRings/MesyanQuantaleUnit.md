# A quantale unit from prime residue rings

## Abstract

A ring without a multiplicative identity whose additive-submonoid quantale is unital.

**Definition 1.1 (The prime-residue direct sum).**

Lean statement: `D5/S3/Arith/ResidueRings/MesyanQuantaleUnit.finiteSupportSubring`

*Formalization.* `D5/S3/Arith/ResidueRings/MesyanQuantaleUnit.finiteSupportSubring` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The declaration `finiteSupportSubring` has type `NonUnitalSubring ((p : Nat.Primes) → ZMod (p : ℕ))`. Its carrier consists of tuples with only finitely many nonzero coordinates. Zero, addition, negation, and multiplication are inherited coordinatewise.

**Theorem 1.2 (Identity laws for the prime-residue direct sum).**

$$(\exists (a: R), a \neq 0) \land (\forall (e: R), \exists (a: R), e \cdot a \neq a \lor a \cdot e \neq a) \land (\forall (M: AddSubmonoid R), T \cdot M = M \land M \cdot T = M)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/ResidueRings/MesyanQuantaleUnit.finiteSupportSubring_properties` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Zachary Mesyan (2026). *Quantales Arising From Rings*. DOI: [10.48550/arXiv.2611.31109](https://doi.org/10.48550/arXiv.2611.31109). URL: <https://arxiv.org/abs/2611.31109v1>.

*Commentary.*

R is the carrier of `D5/S3/Arith/ResidueRings/MesyanQuantaleUnit.finiteSupportSubring`. The tuple supported at 2 with value one there is nonzero. For each candidate identity e, a prime outside its support gives a singleton-supported tuple on which left multiplication by e vanishes.

The proof identifies Mathlib's additive-submonoid product with Definition 4 in Mesyan's paper. The product takes all sums of a positive finite number of pairwise products, with the first factor from the left submonoid and the second from the right.

T denotes the top additive submonoid, which is the whole ring. For any r in the ring and a in M, the Chinese remainder theorem gives one natural number agreeing with the residues of r at all primes in the support of a. Multiplication by r on a therefore agrees with repeated addition, so every product summand lies in M. In the other direction the tuple equal to one on the support of a and zero elsewhere gives a one-term product for a. Commutativity supplies the right unit law.

## References

- Truth anchor: `D5/S3/Arith/ResidueRings/MesyanQuantaleUnit.finiteSupportSubring`
- Truth anchor: `D5/S3/Arith/ResidueRings/MesyanQuantaleUnit.finiteSupportSubring`
- Truth anchor: `D5/S3/Arith/ResidueRings/MesyanQuantaleUnit.finiteSupportSubring_properties`
