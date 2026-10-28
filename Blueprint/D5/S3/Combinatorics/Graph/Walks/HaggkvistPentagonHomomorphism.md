# HaggkvistPentagonHomomorphism

## Abstract

Finite graph structure, degree counting, and perfect matchings.

**Theorem 1.1 (surjective of not two color).**

$$\forall (V: \operatorname{Type}), \forall (G: \operatorname{SimpleGraph} V), \forall (f: (V)\to(\operatorname{Fin} 5)), (\forall (x y: V), (G . \operatorname{Adj} x y)\to(((\operatorname{SimpleGraph} . \operatorname{cycleGraph} 5) . \operatorname{comap} (fun (i: \operatorname{Fin} 5)\mapsto 3 \cdot i)) . \operatorname{Adj} (f x) (f y))) \to ((\neg(\exists (g: (V)\to(\operatorname{Fin} 2)), \forall (x y: V), (G . \operatorname{Adj} x y)\to(g x \neq g y))) \to (\operatorname{Function} . \operatorname{Surjective} f))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/HaggkvistPentagonHomomorphism.surjective_of_not_two_color` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* M. Ahanjideh; T. Ekim; M. A. Yıldız (2022). *Maximum size of a triangle-free graph with bounded maximum degree and matching number*. DOI: [10.1007/s10878-024-01123-z](https://doi.org/10.1007/s10878-024-01123-z). URL: <https://arxiv.org/abs/2207.02271v1>.

*Commentary.*

A graph map into a five-cycle that omits a vertex gives a proper two-coloring. A graph without such a coloring therefore maps onto all five vertices.

**Theorem 1.2 (pentagon hom).**

$$\forall (V: \operatorname{Type}), \forall [\operatorname{Fintype} V], \forall [\operatorname{DecidableEq} V], \forall (G: \operatorname{SimpleGraph} V), \forall [\operatorname{DecidableRel} G . \operatorname{Adj}], ((G . \operatorname{CliqueFree} 3))\to((((3 \cdot \operatorname{Fintype} . \operatorname{card} V < 8 \cdot G . \operatorname{minDegree}))\to((\exists (f: (V)\to(\operatorname{Fin} 5)), \forall (x y: V), (G . \operatorname{Adj} x y)\to(((\operatorname{SimpleGraph} . \operatorname{cycleGraph} 5) . \operatorname{comap} (fun (i: \operatorname{Fin} 5)\mapsto 3 \cdot i)) . \operatorname{Adj} (f x) (f y))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/HaggkvistPentagonHomomorphism.pentagon_hom` (`✓ std3`). ∎

*Citation.* Roland Häggkvist (1982). *Odd Cycles of Specified Length in Non-Bipartite Graphs*. DOI: [10.1016/S0304-0208(08)73552-7](https://doi.org/10.1016/S0304-0208(08)73552-7). URL: <https://doi.org/10.1016/S0304-0208(08)73552-7>.

*Commentary.*

Häggkvist’s strict three-eighths theorem: every finite triangle-free graph whose minimum degree exceeds three-eighths of its order has a homomorphism to the five-cycle. The target is written in the cyclic ordering obtained by multiplying the indices by three. Bipartite graphs are included.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/HaggkvistPentagonHomomorphism.pentagon_hom`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/HaggkvistPentagonHomomorphism.surjective_of_not_two_color`
- Dependency: [D5/S3/Combinatorics/Graph/Walks/DenseTriangleFreeConfigurations](DenseTriangleFreeConfigurations.md)
