# PentagonMissingEdgeObstruction

## Abstract

Finite graph structure, degree counting, and perfect matchings.

**Theorem 1.1 (threshold or exception).**

$$\forall (d: \mathbb{N}), \forall (N: \mathbb{N}), ((21 \leq d))\to((((\operatorname{Odd} d))\to((((N \leq 2 \cdot (\operatorname{Nat} . \operatorname{div} (5 \cdot (d + 1)) 4) - 1))\to(((3 \cdot N < 8 \cdot (d - 1))\lor((d = 23)\land(N = 59))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/ComponentPacking/PentagonMissingEdgeObstruction.threshold_or_exception` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* M. Ahanjideh; T. Ekim; M. A. Yıldız (2022). *Maximum size of a triangle-free graph with bounded maximum degree and matching number*. DOI: [10.1007/s10878-024-01123-z](https://doi.org/10.1007/s10878-024-01123-z). URL: <https://arxiv.org/abs/2207.02271v1>.

*Commentary.*

For odd degrees at least twenty-one, every order below the proposed extremal order satisfies the strict three-eighths density inequality except degree twenty-three and order fifty-nine. Natural division denotes floor division.

**Theorem 1.2 (cycle five adjacency).**

$$\forall (i j: \operatorname{Fin} 5), ((\operatorname{SimpleGraph} . \operatorname{cycleGraph} 5) . \operatorname{Adj} i j)\iff(((j = i + 4)\lor(j = i + 1)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/ComponentPacking/PentagonMissingEdgeObstruction.cycle_five_adjacency` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* M. Ahanjideh; T. Ekim; M. A. Yıldız (2022). *Maximum size of a triangle-free graph with bounded maximum degree and matching number*. DOI: [10.1007/s10878-024-01123-z](https://doi.org/10.1007/s10878-024-01123-z). URL: <https://arxiv.org/abs/2207.02271v1>.

*Commentary.*

The two neighbors of a vertex of the standard five-cycle are its predecessor and successor.

**Definition 1.3 (ClassSize).**

$$\forall (V: \operatorname{Type}), \forall [\operatorname{Fintype} V], \forall (f: (V)\to(\operatorname{Fin} 5)), \forall (i: \operatorname{Fin} 5), \operatorname{ClassSize} f i = ((\operatorname{Finset} . \operatorname{univ} . \operatorname{filter} (fun (x: V)\mapsto f x = i)) . \operatorname{card})$$

*Formalization.* `D5/S3/Combinatorics/Graph/ComponentPacking/PentagonMissingEdgeObstruction.ClassSize` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* M. Ahanjideh; T. Ekim; M. A. Yıldız (2022). *Maximum size of a triangle-free graph with bounded maximum degree and matching number*. DOI: [10.1007/s10878-024-01123-z](https://doi.org/10.1007/s10878-024-01123-z). URL: <https://arxiv.org/abs/2207.02271v1>.

*Commentary.*

Each class size is the cardinality of the fiber of the five-valued map.

**Definition 1.4 (DefectWeight).**

$$\forall (V: \operatorname{Type}), \forall (G: \operatorname{SimpleGraph} V), \forall [\operatorname{DecidableRel} G . \operatorname{Adj}], \forall (f: (V)\to(\operatorname{Fin} 5)), \forall (x: V), \forall (y: V), \operatorname{DefectWeight} G f x y = (if (((\operatorname{SimpleGraph} . \operatorname{cycleGraph} 5) . \operatorname{Adj} (f x) (f y))\land(\neg G . \operatorname{Adj} x y)) then (1: \mathbb{Z}) else 0)$$

*Formalization.* `D5/S3/Combinatorics/Graph/ComponentPacking/PentagonMissingEdgeObstruction.DefectWeight` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* M. Ahanjideh; T. Ekim; M. A. Yıldız (2022). *Maximum size of a triangle-free graph with bounded maximum degree and matching number*. DOI: [10.1007/s10878-024-01123-z](https://doi.org/10.1007/s10878-024-01123-z). URL: <https://arxiv.org/abs/2207.02271v1>.

*Commentary.*

The integer weight is one exactly at a permitted but absent edge of the cyclic blow-up, and zero otherwise.

**Theorem 1.5 (defect row).**

$$\forall (V: \operatorname{Type}), \forall [\operatorname{Fintype} V], \forall [\operatorname{DecidableEq} V], \forall (G: \operatorname{SimpleGraph} V), \forall [\operatorname{DecidableRel} G . \operatorname{Adj}], \forall (f: (V)\to(\operatorname{Fin} 5)), (\forall (x y: V), (G . \operatorname{Adj} x y)\to((\operatorname{SimpleGraph} . \operatorname{cycleGraph} 5) . \operatorname{Adj} (f x) (f y))) \to (\forall (x: V), \sum (y: V) , \operatorname{DefectWeight} G f x y = \operatorname{Int} . \operatorname{ofNat} (\operatorname{ClassSize} f (f x + 4)) + \operatorname{Int} . \operatorname{ofNat} (\operatorname{ClassSize} f (f x + 1)) - \operatorname{Int} . \operatorname{ofNat} (G . \operatorname{degree} x))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/ComponentPacking/PentagonMissingEdgeObstruction.defect_row` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* M. Ahanjideh; T. Ekim; M. A. Yıldız (2022). *Maximum size of a triangle-free graph with bounded maximum degree and matching number*. DOI: [10.1007/s10878-024-01123-z](https://doi.org/10.1007/s10878-024-01123-z). URL: <https://arxiv.org/abs/2207.02271v1>.

*Commentary.*

The sum of the missing-edge weights is the total size of the two permitted classes minus the vertex degree.

**Theorem 1.6 (sum class sizes).**

$$\forall (V: \operatorname{Type}), \forall [\operatorname{Fintype} V], \forall [\operatorname{DecidableEq} V], \forall (f: (V)\to(\operatorname{Fin} 5)), \sum (i: \operatorname{Fin} 5) , \operatorname{ClassSize} f i = \operatorname{Fintype} . \operatorname{card} V$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/ComponentPacking/PentagonMissingEdgeObstruction.sum_class_sizes` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* M. Ahanjideh; T. Ekim; M. A. Yıldız (2022). *Maximum size of a triangle-free graph with bounded maximum degree and matching number*. DOI: [10.1007/s10878-024-01123-z](https://doi.org/10.1007/s10878-024-01123-z). URL: <https://arxiv.org/abs/2207.02271v1>.

*Commentary.*

The five fibers partition the vertex type, so their sizes sum to its cardinality.

**Theorem 1.7 (degree le permitted).**

$$\forall (V: \operatorname{Type}), \forall [\operatorname{Fintype} V], \forall [\operatorname{DecidableEq} V], \forall (G: \operatorname{SimpleGraph} V), \forall [\operatorname{DecidableRel} G . \operatorname{Adj}], \forall (f: (V)\to(\operatorname{Fin} 5)), (\forall (x y: V), (G . \operatorname{Adj} x y)\to((\operatorname{SimpleGraph} . \operatorname{cycleGraph} 5) . \operatorname{Adj} (f x) (f y))) \to (\forall (x: V), G . \operatorname{degree} x \leq \operatorname{ClassSize} f (f x + 4) + \operatorname{ClassSize} f (f x + 1))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/ComponentPacking/PentagonMissingEdgeObstruction.degree_le_permitted` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* M. Ahanjideh; T. Ekim; M. A. Yıldız (2022). *Maximum size of a triangle-free graph with bounded maximum degree and matching number*. DOI: [10.1007/s10878-024-01123-z](https://doi.org/10.1007/s10878-024-01123-z). URL: <https://arxiv.org/abs/2207.02271v1>.

*Commentary.*

Every neighbor belongs to one of the two permitted pentagon classes, bounding the degree by their total size.

**Definition 1.8 (NeighborTotal).**

$$\forall (s: (\operatorname{Fin} 5)\to(\mathbb{N})), \forall (i: \operatorname{Fin} 5), \operatorname{NeighborTotal} s i = (s (i + 4) + s (i + 1))$$

*Formalization.* `D5/S3/Combinatorics/Graph/ComponentPacking/PentagonMissingEdgeObstruction.NeighborTotal` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* M. Ahanjideh; T. Ekim; M. A. Yıldız (2022). *Maximum size of a triangle-free graph with bounded maximum degree and matching number*. DOI: [10.1007/s10878-024-01123-z](https://doi.org/10.1007/s10878-024-01123-z). URL: <https://arxiv.org/abs/2207.02271v1>.

*Commentary.*

The permitted-neighbor total is the sum of the predecessor and successor class sizes.

**Theorem 1.9 (no small surjective map).**

$$\forall (V: \operatorname{Type}), \forall [\operatorname{Fintype} V], \forall [\operatorname{DecidableEq} V], \forall (G: \operatorname{SimpleGraph} V), \forall [\operatorname{DecidableRel} G . \operatorname{Adj}], \forall (f: (V)\to(\operatorname{Fin} 5)), (\forall (x y: V), (G . \operatorname{Adj} x y)\to((\operatorname{SimpleGraph} . \operatorname{cycleGraph} 5) . \operatorname{Adj} (f x) (f y))) \to (((\operatorname{Function} . \operatorname{Surjective} f))\to((\forall (d: \mathbb{N}), ((21 \leq d))\to((((\operatorname{Odd} d))\to((((\operatorname{Odd} (\operatorname{Fintype} . \operatorname{card} V)))\to((((\operatorname{Fintype} . \operatorname{card} V \leq 2 \cdot (\operatorname{Nat} . \operatorname{div} (5 \cdot (d + 1)) 4) - 1))\to((\forall (w: V), (\forall (x: V), \operatorname{Int} . \operatorname{ofNat} (G . \operatorname{degree} x) = \operatorname{Int} . \operatorname{ofNat} d - if x = w then 1 else 0) \to (\operatorname{False}))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/ComponentPacking/PentagonMissingEdgeObstruction.no_small_surjective_map` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* M. Ahanjideh; T. Ekim; M. A. Yıldız (2022). *Maximum size of a triangle-free graph with bounded maximum degree and matching number*. DOI: [10.1007/s10878-024-01123-z](https://doi.org/10.1007/s10878-024-01123-z). URL: <https://arxiv.org/abs/2207.02271v1>.

*Commentary.*

An almost regular graph mapped onto the five-cycle cannot have order below twice the proposed matching number plus one. The missing-edge incidence relations contradict total cyclic slack one or three.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/ComponentPacking/PentagonMissingEdgeObstruction.ClassSize`
- Truth anchor: `D5/S3/Combinatorics/Graph/ComponentPacking/PentagonMissingEdgeObstruction.DefectWeight`
- Truth anchor: `D5/S3/Combinatorics/Graph/ComponentPacking/PentagonMissingEdgeObstruction.NeighborTotal`
- Truth anchor: `D5/S3/Combinatorics/Graph/ComponentPacking/PentagonMissingEdgeObstruction.cycle_five_adjacency`
- Truth anchor: `D5/S3/Combinatorics/Graph/ComponentPacking/PentagonMissingEdgeObstruction.defect_row`
- Truth anchor: `D5/S3/Combinatorics/Graph/ComponentPacking/PentagonMissingEdgeObstruction.degree_le_permitted`
- Truth anchor: `D5/S3/Combinatorics/Graph/ComponentPacking/PentagonMissingEdgeObstruction.no_small_surjective_map`
- Truth anchor: `D5/S3/Combinatorics/Graph/ComponentPacking/PentagonMissingEdgeObstruction.sum_class_sizes`
- Truth anchor: `D5/S3/Combinatorics/Graph/ComponentPacking/PentagonMissingEdgeObstruction.threshold_or_exception`
