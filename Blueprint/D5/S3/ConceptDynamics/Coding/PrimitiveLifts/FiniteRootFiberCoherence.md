# Finite Root Fiber Coherence

## Abstract

Under finite positive-degree root fibers, independent roots at every positive degree are equivalent to a genuine monoid homomorphism from Multiplicative Q to H with phi(Multiplicative.ofAdd(1:Q))=h.

**Theorem 1.1 (Under finite positive-degree root fibers, independent roots at every positive degree are equivalent to rational coherence).**

$$\forall H \in Typeu,\; Group\left(H\right) \to \left(\forall h \in H,\; finiteRootFibers\left(H, h\right) \to \left(positiveRootExistence\left(H, h\right) \Leftrightarrow \left(\exists phi \in MonoidHom\left(Multiplicative\left(\mathbb{Q}\right), H\right),\; value\left(phi, ofAdd\left(1\right)\right) = h\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/PrimitiveLifts/FiniteRootFiberCoherence.finite_root_fibers_rational_coherence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For an arbitrary group H, fix h and assume that every positive-degree fiber {b | b^n=h} is finite. The existence of a root in every positive degree is equivalent to a monoid homomorphism from Multiplicative Q to H with phi(Multiplicative.ofAdd(1:Q))=h. In the formula, ofAdd(q) denotes Multiplicative.ofAdd(q:Q), so ofAdd(1) is additive rational one; the multiplicative identity is ofAdd(0). No commutativity, divisibility, uniqueness, surjectivity, or topology hypothesis is used.

The forward implication is the compactness step. Positive degrees are ordered by divisibility, with common upper bound given by multiplication. The fiber at m maps to the fiber at n for n dividing m by b -> b^(m/n). Mathlib's finite inverse-system section theorem supplies compatible roots without requiring any bonding map to be onto.

For q=a/d define F(q)=b_d^a, with integer exponent. To prove F(q+r)=F(q)F(r), use the single root at d*e*f, where d,e,f are the denominators of q, r, and q+r. Every term is then an integer power of that same group element. Rat.add_num_den' supplies the exponent identity, so no commutation between different group elements is needed. The reverse implication evaluates the homomorphism at Multiplicative.ofAdd(1/n:Q) and uses map_pow.

The theorem asserts existence only. Finite fibers do not imply uniqueness of the resulting homomorphism.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Coding/PrimitiveLifts/FiniteRootFiberCoherence.finite_root_fibers_rational_coherence`
