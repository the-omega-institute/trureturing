# Central elements and Frobenius complements

## Abstract

A nontrivial proper malnormal subgroup forces every central element to be one.

**Theorem 1.1 (A central element is the identity).**

$$\forall G \in Type*,\; [Group\left(G\right)], \forall H \in Subgroup\left(G\right),\; (H \ne \operatorname{Bot}.\operatorname{bot}) \Rightarrow ((H \ne \operatorname{Top}.\operatorname{top}) \Rightarrow ((\forall g \in G,\; (\neg g \in H) \Rightarrow (\operatorname{Min}.\operatorname{min}\left(H, \operatorname{Subgroup}.\operatorname{map}\left(\operatorname{MulAut}.\operatorname{conj}\left(g\right), H\right)\right) = \operatorname{Bot}.\operatorname{bot})) \Rightarrow (\forall z \in G,\; (\forall g \in G,\; g \cdot z = z \cdot g) \Rightarrow (z = 1))))$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/FrobeniusCentralObstruction.central_eq_one_of_frobenius` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let H be a nontrivial proper subgroup whose intersection with every conjugate by an element outside H is trivial. A central element z belongs to H: otherwise conjugation by z leaves H unchanged and contradicts nontriviality. Choose an element outside H. Centrality puts z in the intersection with that element's conjugate of H, so z is the identity.

## References

- Truth anchor: `D5/S3/FiniteGroups/FrobeniusCentralObstruction.central_eq_one_of_frobenius`
