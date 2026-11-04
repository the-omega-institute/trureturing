# SolidResolvingTournamentBase

## Abstract

SolidResolvingTournamentBase

**Definition 1.1 (directedDistance).**

$$\forall V \in Type,\; \forall R \in \left(V\right) \to \left(\left(V\right) \to \left(Prop\right)\right),\; \forall u \in V,\; \forall v \in V,\; \operatorname{directedDistance}\left(R, u, v\right) = letI : \operatorname{Quiver}\left(V\right) := \langle fun \left(a: V\right) \mapsto fun \left(b: V\right) \mapsto \operatorname{PLift}\left(\left(R\right)\left(a, b\right)\right)\rangle; \operatorname{iInf}\left(fun \left(p: \operatorname{Quiver}.\operatorname{Path}\left(u, v\right)\right) \mapsto \left(\operatorname{Quiver}.\operatorname{Path}.\operatorname{length}\left(p\right) : \operatorname{ENat}\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentBase.directedDistance` (`✓ std3`).

*Citation.* Anni Hakanen and Pavan P D (2026). *Solid-Resolving Sets on Directed Graphs*. URL: <https://arxiv.org/abs/2610.35041v1>.

*Commentary.*

The distance from u to v is defined as the number of arcs in a shortest directed path from u to v, and is denoted by d_D(u, v) (where the subscript D may be omitted if the context is clear). If no such directed path exists, then v is not reachable from u, and d(u, v) = ∞. (Page 3.) The infimum of directed walk lengths has this value, with the empty infimum equal to infinity.

**Definition 1.2 (distanceToSet).**

$$\forall V \in Type,\; \forall R \in \left(V\right) \to \left(\left(V\right) \to \left(Prop\right)\right),\; \forall u \in V,\; \forall X \in \operatorname{Set}\left(V\right),\; \operatorname{distanceToSet}\left(R, u, X\right) = \operatorname{iInf}\left(fun \left(v: X\right) \mapsto \operatorname{directedDistance}\left(R, u, \operatorname{val}\left(v\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentBase.distanceToSet` (`✓ std3`).

*Citation.* Anni Hakanen and Pavan P D (2026). *Solid-Resolving Sets on Directed Graphs*. URL: <https://arxiv.org/abs/2610.35041v1>.

*Commentary.*

The distance from a vertex u to a vertex set X ⊆ V(D) is defined as d(u, X) = min_{x ∈ X} d(u, x). If no directed path exists from u to any vertex in X, then d(u, X) = ∞. (Page 3.) The displayed infimum uses the subtype of vertices in X.

**Definition 1.3 (IsSolidResolving).**

$$\forall V \in Type,\; \forall R \in \left(V\right) \to \left(\left(V\right) \to \left(Prop\right)\right),\; \forall S \in \operatorname{Set}\left(V\right),\; \operatorname{IsSolidResolving}\left(R, S\right) = \left(\forall v \in V,\; \forall X \in \operatorname{Set}\left(V\right),\; \operatorname{Set}.\operatorname{Nonempty}\left(X\right) \Rightarrow \left(X \ne \{v\} \Rightarrow \left(\exists w \in V,\; w \in S \land \operatorname{directedDistance}\left(R, w, v\right) \ne \operatorname{distanceToSet}\left(R, w, X\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentBase.IsSolidResolving` (`✓ std3`).

*Citation.* Anni Hakanen and Pavan P D (2026). *Solid-Resolving Sets on Directed Graphs*. URL: <https://arxiv.org/abs/2610.35041v1>.

*Commentary.*

Let D be a digraph. A set S ⊆ V(D) is a solid-resolving set of D if for every vertex v ∈ V(D) and every non-empty subset X ⊆ V(D) with X ≠ {v}, there exists w ∈ S such that d(w, v) ≠ d(w, X). The minimum cardinality of a solid-resolving set is called the solid-metric dimension of D, and is denoted by βₛ(D). (Definition 1.1, page 3.) Vertices range over V; R is the arc relation; X and S are vertex sets. Every nonempty X other than the singleton is retained.

**Definition 1.4 (solidMetricDimension).**

$$\forall V \in Type,\; [\operatorname{Fintype}\left(V\right)] \forall R \in \left(V\right) \to \left(\left(V\right) \to \left(Prop\right)\right),\; \operatorname{solidMetricDimension}\left(R\right) = \operatorname{sInf}\left(\{k: \operatorname{Nat} | \exists S \in \operatorname{Finset}\left(V\right),\; \operatorname{IsSolidResolving}\left(R, \left(S : \operatorname{Set}\left(V\right)\right)\right) \land \operatorname{Finset}.\operatorname{card}\left(S\right) = k\}\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentBase.solidMetricDimension` (`✓ std3`).

*Citation.* Anni Hakanen and Pavan P D (2026). *Solid-Resolving Sets on Directed Graphs*. URL: <https://arxiv.org/abs/2610.35041v1>.

*Commentary.*

Let D be a digraph. A set S ⊆ V(D) is a solid-resolving set of D if for every vertex v ∈ V(D) and every non-empty subset X ⊆ V(D) with X ≠ {v}, there exists w ∈ S such that d(w, v) ≠ d(w, X). The minimum cardinality of a solid-resolving set is called the solid-metric dimension of D, and is denoted by βₛ(D). (Definition 1.1, page 3.) The minimum is the natural infimum of cardinalities of finite solid sets. The full vertex set is solid.

**Theorem 1.5 (solid iff ordered).**

$$\forall V \in Type,\; \forall R \in \left(V\right) \to \left(\left(V\right) \to \left(Prop\right)\right),\; \forall S \in \operatorname{Set}\left(V\right),\; \operatorname{IsSolidResolving}\left(R, S\right) \Leftrightarrow \left(\forall u \in V,\; \forall v \in V,\; u \ne v \Rightarrow \left(\exists w \in V,\; w \in S \land \operatorname{directedDistance}\left(R, w, u\right) < \operatorname{directedDistance}\left(R, w, v\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentBase.solid_iff_ordered` (`✓ std3`). ∎

*Citation.* Anni Hakanen and Pavan P D (2026). *Solid-Resolving Sets on Directed Graphs*. URL: <https://arxiv.org/abs/2610.35041v1>.

*Commentary.*

Let D be a nontrivial digraph. A set S ⊆ V(D) is a solid-resolving set of D if and only if for all distinct u, v ∈ V(D), there is an element s ∈ S such that d(s, u) < d(s, v). (Theorem 2.1, page 3.)

**Theorem 1.6 (profile constraints).**

$$\forall V \in Type,\; \forall k \in \operatorname{Nat},\; \forall R \in \left(V\right) \to \left(\left(V\right) \to \left(Prop\right)\right),\; \forall L \in \left(\operatorname{Fin}\left(k\right)\right) \to \left(V\right),\; \operatorname{IsSolidResolving}\left(R, \operatorname{Set}.\operatorname{range}\left(L\right)\right) \Rightarrow \left(\forall u \in V,\; \neg \left(u \in \operatorname{Set}.\operatorname{range}\left(L\right)\right) \Rightarrow \left(\forall D \in \left(\operatorname{Fin}\left(k\right)\right) \to \left(\left(\operatorname{Fin}\left(k\right)\right) \to \left(\operatorname{ENat}\right)\right),\; \left(\forall i \in \operatorname{Fin}\left(k\right),\; \forall j \in \operatorname{Fin}\left(k\right),\; \operatorname{directedDistance}\left(R, \left(L\right)\left(i\right), \left(L\right)\left(j\right)\right) \le \left(D\right)\left(i, j\right)\right) \Rightarrow \left(\left(\forall i \in \operatorname{Fin}\left(k\right),\; 1 \le \left(fun \left(a: \operatorname{Fin}\left(k\right)\right) \mapsto \operatorname{directedDistance}\left(R, \left(L\right)\left(a\right), u\right)\right)\left(i\right)\right) \land \left(\left(\forall j \in \operatorname{Fin}\left(k\right),\; \exists i \in \operatorname{Fin}\left(k\right),\; \left(fun \left(a: \operatorname{Fin}\left(k\right)\right) \mapsto \operatorname{directedDistance}\left(R, \left(L\right)\left(a\right), u\right)\right)\left(i\right) < \left(D\right)\left(i, j\right)\right) \land \left(\forall i \in \operatorname{Fin}\left(k\right),\; \forall j \in \operatorname{Fin}\left(k\right),\; \left(fun \left(a: \operatorname{Fin}\left(k\right)\right) \mapsto \operatorname{directedDistance}\left(R, \left(L\right)\left(a\right), u\right)\right)\left(i\right) \le \left(D\right)\left(i, j\right) + \left(fun \left(a: \operatorname{Fin}\left(k\right)\right) \mapsto \operatorname{directedDistance}\left(R, \left(L\right)\left(a\right), u\right)\right)\left(j\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentBase.profile_constraints` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The distance profile of a vertex outside the landmarks is positive, lies below some landmark distance in each column, and satisfies every triangle upper bound.

**Definition 1.7 (pairIndex).**

$$\forall k \in \operatorname{Nat},\; \forall i \in \operatorname{Nat},\; \forall j \in \operatorname{Nat},\; \operatorname{pairIndex}\left(k, i, j\right) = \operatorname{Nat}.\operatorname{div}\left(i \cdot \left(2 \cdot k - i - 1\right), 2\right) + \left(j - i - 1\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentBase.pairIndex` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The index of the unordered pair with i less than j in the row-major upper triangle. Nat.div is truncated natural-number division, and natural subtraction truncates at zero.

**Definition 1.8 (maskArc).**

$$\forall k \in \operatorname{Nat},\; \forall m \in \operatorname{Nat},\; \forall i \in \operatorname{Fin}\left(k\right),\; \forall j \in \operatorname{Fin}\left(k\right),\; \operatorname{maskArc}\left(m, i, j\right) = \operatorname{ite}\left(\operatorname{val}\left(i\right) < \operatorname{val}\left(j\right), \operatorname{Nat}.\operatorname{testBit}\left(m, \operatorname{pairIndex}\left(k, \operatorname{val}\left(i\right), \operatorname{val}\left(j\right)\right)\right), \operatorname{ite}\left(\operatorname{val}\left(j\right) < \operatorname{val}\left(i\right), \operatorname{Bool}.\operatorname{not}\left(\operatorname{Nat}.\operatorname{testBit}\left(m, \operatorname{pairIndex}\left(k, \operatorname{val}\left(j\right), \operatorname{val}\left(i\right)\right)\right)\right), false\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentBase.maskArc` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A mask bit directs the arc from the smaller index to the larger index; the reverse arc uses its Boolean negation and diagonal entries are false.

**Definition 1.9 (walkBound).**

$$\forall k \in \operatorname{Nat},\; \forall m \in \operatorname{Nat},\; \left(\forall i \in \operatorname{Fin}\left(k\right),\; \forall j \in \operatorname{Fin}\left(k\right),\; \operatorname{walkBound}\left(m, 0, i, j\right) = \operatorname{BEq}.\operatorname{beq}\left(i, j\right)\right) \land \left(\forall n \in \operatorname{Nat},\; \forall i \in \operatorname{Fin}\left(k\right),\; \forall j \in \operatorname{Fin}\left(k\right),\; \operatorname{walkBound}\left(m, n + 1, i, j\right) = \operatorname{Bool}.\operatorname{or}\left(\operatorname{walkBound}\left(m, n, i, j\right), \operatorname{List}.\operatorname{any}\left(\operatorname{List}.\operatorname{finRange}\left(k\right), fun \left(z: \operatorname{Fin}\left(k\right)\right) \mapsto \operatorname{Bool}.\operatorname{and}\left(\operatorname{walkBound}\left(m, n, i, z\right), \operatorname{maskArc}\left(m, z, j\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentBase.walkBound` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The Boolean recurrence tests reachability by at most n arcs, allowing an empty walk when its two endpoints coincide.

**Theorem 1.10 (directedDistance le walkBound).**

$$\forall V \in Type,\; \forall k \in \operatorname{Nat},\; \forall R \in \left(V\right) \to \left(\left(V\right) \to \left(Prop\right)\right),\; \forall L \in \left(\operatorname{Fin}\left(k\right)\right) \to \left(V\right),\; \forall m \in \operatorname{Nat},\; \left(\forall i \in \operatorname{Fin}\left(k\right),\; \forall j \in \operatorname{Fin}\left(k\right),\; \operatorname{maskArc}\left(m, i, j\right) = true \Rightarrow \left(R\right)\left(\left(L\right)\left(i\right), \left(L\right)\left(j\right)\right)\right) \Rightarrow \left(\forall n \in \operatorname{Nat},\; \forall i \in \operatorname{Fin}\left(k\right),\; \forall j \in \operatorname{Fin}\left(k\right),\; \operatorname{walkBound}\left(m, n, i, j\right) = true \Rightarrow \operatorname{directedDistance}\left(R, \left(L\right)\left(i\right), \left(L\right)\left(j\right)\right) \le \left(n : \operatorname{ENat}\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentBase.directedDistance_le_walkBound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed formula specifies the object and all of its parameters.

**Theorem 1.11 (dimension lower of fixed card bound).**

$$\forall V \in Type,\; [\operatorname{Fintype}\left(V\right)] \forall R \in \left(V\right) \to \left(\left(V\right) \to \left(Prop\right)\right),\; \forall k \in \operatorname{Nat},\; \forall c \in \operatorname{Nat},\; k \le \operatorname{Fintype}.\operatorname{card}\left(V\right) \Rightarrow \left(c < \operatorname{Fintype}.\operatorname{card}\left(V\right) \Rightarrow \left(\left(\forall S \in \operatorname{Finset}\left(V\right),\; \operatorname{Finset}.\operatorname{card}\left(S\right) = k \Rightarrow \left(\operatorname{IsSolidResolving}\left(R, \left(S : \operatorname{Set}\left(V\right)\right)\right) \Rightarrow \operatorname{Fintype}.\operatorname{card}\left(V\right) \le c\right)\right) \Rightarrow k + 1 \le \operatorname{solidMetricDimension}\left(R\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentBase.dimension_lower_of_fixed_card_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A smaller solid set can be enlarged to cardinality k. If every solid set of that cardinality forces an ambient order at most c, an ambient order greater than c has solid-metric dimension at least k plus one.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentBase.IsSolidResolving`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentBase.dimension_lower_of_fixed_card_bound`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentBase.directedDistance`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentBase.directedDistance_le_walkBound`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentBase.distanceToSet`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentBase.maskArc`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentBase.pairIndex`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentBase.profile_constraints`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentBase.solidMetricDimension`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentBase.solid_iff_ordered`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentBase.walkBound`
