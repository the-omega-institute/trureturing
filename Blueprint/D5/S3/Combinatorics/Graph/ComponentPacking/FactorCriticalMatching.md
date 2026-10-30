# FactorCriticalMatching

## Abstract

Finite graph structure, degree counting, and perfect matchings.

**Definition 1.1 (IsAlmostRegular).**

$$\forall (n: \mathbb{N}), \forall (G: \operatorname{SimpleGraph} (\operatorname{Fin} n)), \forall [\operatorname{DecidableRel} G . \operatorname{Adj}], \forall (d: \mathbb{N}), (\operatorname{IsAlmostRegular} G d)\iff((\exists (w: \operatorname{Fin} n), (G . \operatorname{degree} w = d - 1)\land((\forall (v: \operatorname{Fin} n), (v \neq w)\to(G . \operatorname{degree} v = d)))))$$

*Formalization.* `D5/S3/Combinatorics/Graph/ComponentPacking/FactorCriticalMatching.IsAlmostRegular` (`✓ std3`).

*Citation.* M. Ahanjideh; T. Ekim; M. A. Yıldız (2022). *Maximum size of a triangle-free graph with bounded maximum degree and matching number*. DOI: [10.1007/s10878-024-01123-z](https://doi.org/10.1007/s10878-024-01123-z). URL: <https://arxiv.org/abs/2207.02271v1>.

*Commentary.*

Section 2, page 3: “if d(w) = d − 1 for some w ∈ V(G) and d(v) = d for all v ∈ V(G) − w, then G is said to be almost d-regular.” The carrier is Fin n and the natural subtraction d − 1 follows this expression.

**Definition 1.2 (IsFactorCritical).**

$$\forall (n: \mathbb{N}), \forall (G: \operatorname{SimpleGraph} (\operatorname{Fin} n)), (\operatorname{IsFactorCritical} G)\iff((\forall (v: \operatorname{Fin} n), \exists (M: (G . \operatorname{induce} (\ \{v\ \}^{c}: \operatorname{Set} (\operatorname{Fin} n))) . \operatorname{Subgraph}), M . \operatorname{IsPerfectMatching}))$$

*Formalization.* `D5/S3/Combinatorics/Graph/ComponentPacking/FactorCriticalMatching.IsFactorCritical` (`✓ std3`).

*Citation.* M. Ahanjideh; T. Ekim; M. A. Yıldız (2022). *Maximum size of a triangle-free graph with bounded maximum degree and matching number*. DOI: [10.1007/s10878-024-01123-z](https://doi.org/10.1007/s10878-024-01123-z). URL: <https://arxiv.org/abs/2207.02271v1>.

*Commentary.*

Section 2, page 4: “A graph G is said to be factor-critical if G \ v has a perfect matching for all v ∈ V(G).” Deletion is the induced graph on the complement of the singleton.

**Theorem 1.3 (odd order).**

$$\forall (N: \mathbb{N}), \forall (G: \operatorname{SimpleGraph} (\operatorname{Fin} N)), ((\operatorname{IsFactorCritical} G))\to((((0 < N))\to((\operatorname{Odd} N))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/ComponentPacking/FactorCriticalMatching.odd_order` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* M. Ahanjideh; T. Ekim; M. A. Yıldız (2022). *Maximum size of a triangle-free graph with bounded maximum degree and matching number*. DOI: [10.1007/s10878-024-01123-z](https://doi.org/10.1007/s10878-024-01123-z). URL: <https://arxiv.org/abs/2207.02271v1>.

*Commentary.*

A perfect matching after one vertex deletion forces the remaining order to be even.

**Theorem 1.4 (almost regular order eq).**

$$\forall (N: \mathbb{N}), \forall (d: \mathbb{N}), \forall (G: \operatorname{SimpleGraph} (\operatorname{Fin} N)), \forall [\operatorname{DecidableRel} G . \operatorname{Adj}], ((\operatorname{IsFactorCritical} G))\to((((\operatorname{IsAlmostRegular} G d))\to((N = 2 \cdot \operatorname{matchingNumber} G + 1))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/ComponentPacking/FactorCriticalMatching.almost_regular_order_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* M. Ahanjideh; T. Ekim; M. A. Yıldız (2022). *Maximum size of a triangle-free graph with bounded maximum degree and matching number*. DOI: [10.1007/s10878-024-01123-z](https://doi.org/10.1007/s10878-024-01123-z). URL: <https://arxiv.org/abs/2207.02271v1>.

*Commentary.*

A nonempty factor-critical graph has one more vertex than twice its matching number. Almost regularity supplies nonemptiness.

**Theorem 1.5 (exists equiv of omission bound).**

$$\forall (A: \operatorname{Type}), \forall (B: \operatorname{Type}), \forall [\operatorname{Fintype} A], \forall [\operatorname{Fintype} B], \forall (R: (A)\to((B)\to(\operatorname{Prop}))), \forall [\operatorname{DecidableRel} R], \forall (r: \mathbb{N}), ((\operatorname{Fintype} . \operatorname{card} A = \operatorname{Fintype} . \operatorname{card} B))\to((((2 \cdot r \leq \operatorname{Fintype} . \operatorname{card} B))\to(((\forall (a: A), (\operatorname{Finset} . \operatorname{univ} . \operatorname{filter} (fun (b: B)\mapsto \neg R a b)) . \operatorname{card} \leq r) \to ((\forall (b: B), (\operatorname{Finset} . \operatorname{univ} . \operatorname{filter} (fun (a: A)\mapsto \neg R a b)) . \operatorname{card} \leq r) \to (\exists (f: \operatorname{Equiv}\left(A, B\right)), \forall (a: A), R a (f a)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/ComponentPacking/FactorCriticalMatching.exists_equiv_of_omission_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* M. Ahanjideh; T. Ekim; M. A. Yıldız (2022). *Maximum size of a triangle-free graph with bounded maximum degree and matching number*. DOI: [10.1007/s10878-024-01123-z](https://doi.org/10.1007/s10878-024-01123-z). URL: <https://arxiv.org/abs/2207.02271v1>.

*Commentary.*

Two finite sets of equal size admit a compatible bijection when each element omits at most r partners in the other set and both sets have at least 2r elements. The proof verifies Hall’s condition.

**Theorem 1.6 (color balance).**

$$\forall (V: \operatorname{Type}), \forall [\operatorname{Fintype} V], \forall (G: \operatorname{SimpleGraph} V), \forall (M: G . \operatorname{Subgraph}), ((M . \operatorname{IsPerfectMatching}))\to((\forall (c: (V)\to(\operatorname{Fin} 2)), (\forall (x y: V), (G . \operatorname{Adj} x y)\to(c x \neq c y)) \to (\operatorname{Fintype} . \operatorname{card} \ \{x: V \mid c x = 0\ \} = \operatorname{Fintype} . \operatorname{card} \ \{x: V \mid c x = 1\ \})))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/ComponentPacking/FactorCriticalMatching.color_balance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* M. Ahanjideh; T. Ekim; M. A. Yıldız (2022). *Maximum size of a triangle-free graph with bounded maximum degree and matching number*. DOI: [10.1007/s10878-024-01123-z](https://doi.org/10.1007/s10878-024-01123-z). URL: <https://arxiv.org/abs/2207.02271v1>.

*Commentary.*

Every perfect matching exchanges the two classes of a proper two-coloring, so the classes have the same cardinality.

**Theorem 1.7 (deleted color count).**

$$\forall (V: \operatorname{Type}), \forall [\operatorname{Fintype} V], \forall [\operatorname{DecidableEq} V], \forall (C: \operatorname{Type}), \forall [\operatorname{DecidableEq} C], \forall (c: (V)\to(C)), \forall (i: C), \forall (v: V), \operatorname{Fintype} . \operatorname{card} \ \{x: (\ \{v\ \}^{c}: \operatorname{Set} V) \mid c (\operatorname{Subtype} . \operatorname{val} x) = i\ \} = (\operatorname{Finset} . \operatorname{univ} . \operatorname{filter} (fun (x: V)\mapsto c x = i)) . \operatorname{card} - (if c v = i then 1 else 0)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/ComponentPacking/FactorCriticalMatching.deleted_color_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* M. Ahanjideh; T. Ekim; M. A. Yıldız (2022). *Maximum size of a triangle-free graph with bounded maximum degree and matching number*. DOI: [10.1007/s10878-024-01123-z](https://doi.org/10.1007/s10878-024-01123-z). URL: <https://arxiv.org/abs/2207.02271v1>.

*Commentary.*

Deleting a vertex removes one member of its color class and leaves every other color count unchanged.

**Theorem 1.8 (no two color).**

$$\forall (N: \mathbb{N}), \forall (G: \operatorname{SimpleGraph} (\operatorname{Fin} N)), ((\operatorname{IsFactorCritical} G))\to(((\exists (a b: \operatorname{Fin} N), G . \operatorname{Adj} a b) \to (\neg (\exists (c: (\operatorname{Fin} N)\to(\operatorname{Fin} 2)), \forall (x y: \operatorname{Fin} N), (G . \operatorname{Adj} x y)\to(c x \neq c y)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/ComponentPacking/FactorCriticalMatching.no_two_color` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* M. Ahanjideh; T. Ekim; M. A. Yıldız (2022). *Maximum size of a triangle-free graph with bounded maximum degree and matching number*. DOI: [10.1007/s10878-024-01123-z](https://doi.org/10.1007/s10878-024-01123-z). URL: <https://arxiv.org/abs/2207.02271v1>.

*Commentary.*

A factor-critical graph containing an edge has no proper two-coloring: deleting vertices of opposite colors would force incompatible color-class balances.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/ComponentPacking/FactorCriticalMatching.IsAlmostRegular`
- Truth anchor: `D5/S3/Combinatorics/Graph/ComponentPacking/FactorCriticalMatching.IsFactorCritical`
- Truth anchor: `D5/S3/Combinatorics/Graph/ComponentPacking/FactorCriticalMatching.almost_regular_order_eq`
- Truth anchor: `D5/S3/Combinatorics/Graph/ComponentPacking/FactorCriticalMatching.color_balance`
- Truth anchor: `D5/S3/Combinatorics/Graph/ComponentPacking/FactorCriticalMatching.deleted_color_count`
- Truth anchor: `D5/S3/Combinatorics/Graph/ComponentPacking/FactorCriticalMatching.exists_equiv_of_omission_bound`
- Truth anchor: `D5/S3/Combinatorics/Graph/ComponentPacking/FactorCriticalMatching.no_two_color`
- Truth anchor: `D5/S3/Combinatorics/Graph/ComponentPacking/FactorCriticalMatching.odd_order`
- Dependency: [D5/S3/StatisticalMechanics/DimerVirialFourthDifferenceRefutation](../../../StatisticalMechanics/DimerVirialFourthDifferenceRefutation.md)
- Dependency: [D5/S3/Zeros/Convolution/MatchingFiber](../../../Zeros/Convolution/MatchingFiber.md)
