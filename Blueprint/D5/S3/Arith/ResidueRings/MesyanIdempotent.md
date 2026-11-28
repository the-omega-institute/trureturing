# Units of additive-submonoid products with idempotent addition

## Abstract

The additively idempotent case of Mesyan's Question 36.

Use the product from Definition 4, so elements of the product are positive finite sums of pairwise products with factors in the specified submonoids. The theorem uses two-sided identity laws for this binary operation, which are meaningful even when multiplication is nonassociative. `D5/L/ArithUnits/mesyan2026quantales`.

**Theorem 1.1 (Classification for additively idempotent semirings).**

$$\forall (R: Type), [NonUnitalNonAssocSemiring R], (\forall (a: R), a + a = a) \Rightarrow ((\exists (E: AddSubmonoid R), \forall (M: AddSubmonoid R), E \cdot M = M \land M \cdot E = M) \Leftrightarrow (\exists (u: R), \forall (x: R), u \cdot x = x \land x \cdot u = x))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/ResidueRings/MesyanIdempotent.product_unit_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Zachary Mesyan (2026). *Quantales Arising From Rings*. DOI: [10.48550/arXiv.2611.31109](https://doi.org/10.48550/arXiv.2611.31109). URL: <https://arxiv.org/abs/2611.31109v1>.

*Commentary.*

Idempotent addition reduces the cyclic additive submonoid of x to {0, x}. By the `D5/S3/Arith/ResidueRings/MesyanCancellative.product_unit_iff_eq_cyclicPreservingMultipliers`, a product unit is the submonoid C of cyclic-preserving multipliers, and each element has a left and right fixer in C. For e and f in C, a nonzero product ef must equal both e and f. Applying this to a left fixer of a nonzero e in C gives e² = e.

If distinct nonzero elements e and f belong to C, then ef and fe are zero. Distributivity gives (e + f)e = e and (e + f)f = f. Both products are nonzero, forcing e + f to equal e and f. Thus C has at most one nonzero element. If the semiring has a nonzero element, its fixer supplies that unique multiplier. Every nonzero element has this same fixer on each side, and it fixes zero by the zero multiplication laws. In the zero semiring, zero is a two-sided identity.

Conversely, a global two-sided identity belongs to C and fixes every element on both sides. The criterion then gives a unit for the binary product.

## References

- Truth anchor: `D5/S3/Arith/ResidueRings/MesyanCancellative.product_unit_iff_eq_cyclicPreservingMultipliers`
- Truth anchor: `D5/S3/Arith/ResidueRings/MesyanIdempotent.product_unit_iff`
- Dependency: [D5/S3/Arith/ResidueRings/MesyanCancellative](MesyanCancellative.md)
