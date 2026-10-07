# Gaschutz Lifting with an Arbitrary Fixed Set

## Abstract

A quotient-generating ordered tuple can be corrected inside a normal subgroup to generate any finite group while keeping an arbitrary set fixed.

**Theorem 1.1 (Lifting an ordered tuple).**

$$\forall G \in Typeu,\; \left(Group\left(G\right) \land Finite\left(G\right)\right) \Rightarrow \left(\forall n \in Nat,\; \forall N \in Subgroup\left(G\right),\; Normal\left(N\right) \Rightarrow \left(\forall X \in Set\left(G\right),\; \forall y \in Tuple\left(n, G\right),\; \left(\left(\exists z \in Tuple\left(n, G\right),\; closure\left(range\left(z\right)\right) = top\right) \land join\left(N, closure\left(union\left(X, range\left(y\right)\right)\right)\right) = top\right) \Rightarrow \left(\exists a \in Tuple\left(n, N\right),\; closure\left(union\left(X, range\left(leftCorrect\left(a, y\right)\right)\right)\right) = top\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/GaschutzFixed.gaschutz_fixed` (`✓ std3`). ∎

*Citation.* Nikolay Nikolov and Dan Segal (2011). *Powers in finite groups*. DOI: [10.4171/GGD/136](https://doi.org/10.4171/GGD/136). URL: <https://doi.org/10.4171/GGD/136>.

*Commentary.*

G is any finite group in any universe, N is a normal subgroup, X is any subset, and y is an ordered tuple indexed by Fin(n). The closure notation denotes the generated subgroup, top is the whole group, and join is the subgroup join. The hypothesis hgen asks for an ordered tuple z of the same length generating G. The hypothesis hquot says that N together with X and y generates G.

There is an ordered tuple a of elements of N for which X and the products a(i)y(i) generate G. These are left corrections and the set X stays fixed. The statement includes zero-length tuples, and imposes no commutativity, solvability or Frattini condition.

In the displayed formulas, Tuple(n,H) is the function type from Fin(n) to H, and leftCorrect(a,y) is the tuple with coordinate a(i)y(i), using the inclusion of N in G. The symbol goodCorrections denotes the finite set of tuples a in Tuple(n,N) whose corrected coordinates generate G together with X.

For a subgroup H containing X, a correction can place all coordinates in H only when the join of N and H is G. In that case normality gives a point in every correction fiber, and translation identifies each fiber with the intersection of N and H. The constrained count is therefore the size of that intersection raised to n.

A corrected tuple generates together with X exactly when it avoids every proper subgroup containing X. Inclusion-exclusion expresses the number of these tuples through the constrained intersection counts. Each constrained intersection count depends only on N, the intersection subgroup, and n, and is independent of y; therefore the total number of generating corrections depends only on G, N, X, and n. The generating tuple z has the identity correction, giving positivity and hence the required correction for y.

**Theorem 1.2 (The generating-correction count is invariant).**

$$\forall G \in Typeu,\; \left(Group\left(G\right) \land Fintype\left(G\right)\right) \Rightarrow \left(\forall n \in Nat,\; \forall N \in Subgroup\left(G\right),\; Normal\left(N\right) \Rightarrow \left(\forall X \in Set\left(G\right),\; \forall y \in Tuple\left(n, G\right),\; \forall z \in Tuple\left(n, G\right),\; \left(join\left(N, closure\left(union\left(X, range\left(y\right)\right)\right)\right) = top \land join\left(N, closure\left(union\left(X, range\left(z\right)\right)\right)\right) = top\right) \Rightarrow card\left(goodCorrections\left(N, X, y\right)\right) = card\left(goodCorrections\left(N, X, z\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/GaschutzFixed.good_correction_card_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For two tuples of the same length satisfying the quotient-generation hypothesis with the same N and X, the finite sets of generating corrections have equal cardinality. Mathlib's finite inclusion-exclusion identity applies also to the empty intersection, so the argument does not exclude n equal to zero.

**Theorem 1.3 (Tuple generation and generator rank).**

$$\forall G \in Typeu,\; \left(Group\left(G\right) \land Finite\left(G\right)\right) \Rightarrow \left(\forall n \in Nat,\; \left(\exists z \in Tuple\left(n, G\right),\; closure\left(range\left(z\right)\right) = top\right) \Leftrightarrow rank\left(G\right) \le n\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/GaschutzFixed.tuple_generation_iff_rank_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An ordered n-tuple generates G exactly when Group.rank(G) is at most n. One direction bounds the cardinality of the tuple's image. For the other, enumerate a minimum generating set, place its entries in the first positions of Fin(n), and fill unused positions with the identity. The construction works even when both the minimum set and Fin(n) are empty. This equivalence gives the rank hypothesis of the Nikolov-Segal formulation without adding a positive-length premise.

## References

- Truth anchor: `D5/S3/FiniteGroups/GaschutzFixed.gaschutz_fixed`
- Truth anchor: `D5/S3/FiniteGroups/GaschutzFixed.good_correction_card_eq`
- Truth anchor: `D5/S3/FiniteGroups/GaschutzFixed.tuple_generation_iff_rank_le`
