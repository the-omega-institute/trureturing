# Finite and Compact Root Fiber Coherence

## Abstract

Finite root fibers in a group, or compact root fibers in a Hausdorff topological group, turn independent positive roots into a monoid homomorphism from Multiplicative Q to H with phi(Multiplicative.ofAdd(1:Q))=h.

**Theorem 1.1 (Under finite positive-degree root fibers, independent roots at every positive degree are equivalent to rational coherence).**

$$\forall H \in Typeu,\; Group\left(H\right) \to \left(\forall h \in H,\; finiteRootFibers\left(H, h\right) \to \left(positiveRootExistence\left(H, h\right) \Leftrightarrow \left(\exists phi \in MonoidHom\left(Multiplicative\left(\mathbb{Q}\right), H\right),\; value\left(phi, ofAdd\left(1\right)\right) = h\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/PrimitiveLifts/FiniteRootFiberCoherence.finite_root_fibers_rational_coherence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For an arbitrary group H, fix h and assume that every positive-degree fiber {b | b^n=h} is finite. The existence of a root in every positive degree is equivalent to a monoid homomorphism from Multiplicative Q to H with phi(Multiplicative.ofAdd(1:Q))=h. In the formula, ofAdd(q) denotes Multiplicative.ofAdd(q:Q), so ofAdd(1) is additive rational one; the multiplicative identity is ofAdd(0). No commutativity, divisibility, uniqueness, surjectivity, or topology hypothesis is used.

The forward implication is the compactness step. Positive degrees are ordered by divisibility, with common upper bound given by multiplication. The fiber at m maps to the fiber at n for n dividing m by b -> b^(m/n). Mathlib's finite inverse-system section theorem supplies compatible roots without requiring any bonding map to be onto.

For q=a/d define F(q)=b_d^a, with integer exponent. To prove F(q+r)=F(q)F(r), use the single root at d*e*f, where d,e,f are the denominators of q, r, and q+r. Every term is then an integer power of that same group element. Rat.add_num_den' supplies the exponent identity, so no commutation between different group elements is needed. The reverse implication evaluates the homomorphism at Multiplicative.ofAdd(1/n:Q) and uses map_pow.

The theorem asserts existence only. Finite fibers do not imply uniqueness of the resulting homomorphism.

**Theorem 1.2 (Compact root spaces suffice for rational coherence).**

$$\forall H \in Typeu,\; [Group\left(H\right)][TopologicalSpace\left(H\right)][IsTopologicalGroup\left(H\right)][T2Space\left(H\right)]\forall h \in H,\; \left(\forall n \in \mathbb{N},\; \left(0 < n\right) \to IsCompact\left(rootFiber\left(H, h, n\right)\right)\right) \to \left(\left(\forall n \in \mathbb{N},\; \left(0 < n\right) \to \left(\exists x \in H,\; x^{n} = h\right)\right) \Leftrightarrow \left(\exists phi \in MonoidHom\left(Multiplicative\left(\mathbb{Q}\right), H\right),\; value\left(phi, ofAdd\left(1\right)\right) = h\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/PrimitiveLifts/FiniteRootFiberCoherence.compact_root_fibers_rational_coherence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let H be a group with a topology making multiplication and inversion continuous, and assume that this topology is Hausdorff. Fix h in H. For every natural n>0 assume IsCompact {x in H | x^n=h}, using the actual topology of H. In the formula rootFiber(H,h,n) denotes exactly this set. Then roots in every positive degree exist if and only if there is an algebraic monoid homomorphism phi:Multiplicative Q -> H with phi(Multiplicative.ofAdd(1:Q))=h. The value is at additive rational one; ofAdd(0) is the multiplicative identity. All positive degrees, including n=1, are covered. The degree-one root space is the singleton {h}. The ambient group need not be compact, the root spaces need not be finite, and H need not be commutative.

Use the same positive degrees ordered by divisibility and the same maps R_m(h) -> R_n(h), x -> x^(m/n), for n dividing m. Positive powers are continuous, so these actual root subspaces form a cofiltered system of nonempty compact Hausdorff spaces. Mathlib's TopCat.nonempty_limitCone_of_compact_t2_cofiltered_system gives a compatible root in each degree. No transition map is required to be onto. The rational construction is the same as above: pass to a common cyclic denominator to prove the full homomorphism law. Conversely, phi(ofAdd(1/n)) is an n-th root of h by map_pow.

The finite-root-fiber theorem is recovered by assigning the discrete topology to its arbitrary group: this is a Hausdorff group topology and finite root sets are compact. The compact ambient-group theorem CompactRootCoherence.exists_all_positive_roots_iff_exists_rat_hom is also a specialization: each root set is the inverse image of the closed singleton {h} under a continuous power map, hence is closed and compact. Thus compact root spaces connect both existing results. This uses the classical compact inverse-limit principle and makes no literature novelty claim.

The conclusion supplies existence of an algebraic homomorphism. It asserts neither continuity nor uniqueness, does not extend every prescribed root, and does not assert that compactness of the root spaces is necessary. The dyadic-solenoid rational-time application is already described in DyadicRootFiberArithmetic.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Coding/PrimitiveLifts/FiniteRootFiberCoherence.compact_root_fibers_rational_coherence`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PrimitiveLifts/FiniteRootFiberCoherence.finite_root_fibers_rational_coherence`
