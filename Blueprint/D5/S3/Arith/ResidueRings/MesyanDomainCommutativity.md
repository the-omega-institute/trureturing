# The domain equivalence in Mesyan's Question 34

## Abstract

A domain in Mesyan's sense can be noncommutative while its additive-submonoid quantale is commutative.

**Definition 1.1 (The domain clause of Question 34).**

$$\forall (R : Type) [NonUnitalSemiring R] [Nontrivial R] [NoZeroDivisors R], (\forall (x y : R), x \cdot y = y \cdot x) \Leftrightarrow (\forall (A B : AddSubmonoid R), A \cdot B = B \cdot A)$$

*Formalization.* `D5/S3/Arith/ResidueRings/MesyanDomainCommutativity.claim` (`✓ std3`).

*Citation.* Zachary Mesyan (2026). *Quantales Arising From Rings*. DOI: [10.48550/arXiv.2611.31109](https://doi.org/10.48550/arXiv.2611.31109). URL: <https://arxiv.org/abs/2611.31109v1>.

*Commentary.*

On page 24 of the first arXiv revision, Mesyan asks, “For a domain R, is R being commutative equivalent to ℳ(R) being commutative?” Remark 14 uses domain for a nonzero semiring in which a product of two nonzero elements is nonzero. The semiring convention allows multiplication without an identity.

Both submonoids range over all additive submonoids of R. Mathlib's pointwise product is the least additive submonoid containing all pairwise products. This is the product in Definition 4. Each generator is a one-term sum, sums of positive length are closed under addition, and the zero has a one-term representation as the product of two zero elements.

**Theorem 1.2 (A noncommutative domain with commuting submonoids).**

$$\neg (\forall (R : Type) [NonUnitalSemiring R] [Nontrivial R] [NoZeroDivisors R], (\forall (x y : R), x \cdot y = y \cdot x) \Leftrightarrow (\forall (A B : AddSubmonoid R), A \cdot B = B \cdot A))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/ResidueRings/MesyanDomainCommutativity.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Zachary Mesyan (2026). *Quantales Arising From Rings*. DOI: [10.48550/arXiv.2611.31109](https://doi.org/10.48550/arXiv.2611.31109). URL: <https://arxiv.org/abs/2611.31109v1>.

*Commentary.*

Use the basis x, y, xy of Mesyan's Example 6 over the field of three elements. In coordinates the product of (a, b, c) and (d, e, f) is (0, 0, ae − bd). Both bracketings of a triple product give the zero of this algebra.

Adjoin a fresh additive identity that absorbs multiplication. Keep both operations on pairs of original elements. The original zero is distinct from the new zero, and two original elements always multiply to another original element. The generators (1, 0, 0) and (0, 1, 0) give (0, 0, 1) and (0, 0, 2) in opposite orders.

In the extension, reversing any pairwise product gives its double. For any additive submonoids A and B, every generator of A times B is the double of a generator of B times A. Closure under addition gives one containment, and exchanging A and B gives the other.

## References

- Truth anchor: `D5/S3/Arith/ResidueRings/MesyanDomainCommutativity.claim`
- Truth anchor: `D5/S3/Arith/ResidueRings/MesyanDomainCommutativity.result`
