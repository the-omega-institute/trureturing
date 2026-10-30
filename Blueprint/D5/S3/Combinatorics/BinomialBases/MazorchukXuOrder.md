# Expansion and cutoff structure of ordered closure

## Abstract

Ordered clique fibers, exceptional incidence cutoffs and monotone threshold edges supply structural ingredients for finite order-pattern counting.

**Definition 1.1 (Clique-fiber expansion).**

$$\forall A \in \operatorname{Type}\left(\right),\; \forall B \in \operatorname{Type}\left(\right),\; [\operatorname{LinearOrder}\left(B\right)] \forall E \in A \to \left(A \to \operatorname{Prop}\left(\right)\right),\; \forall f \in B \to A,\; \forall a \in B,\; \forall b \in B,\; (\operatorname{cliqueLift}\left(E, f, a, b\right)) \Leftrightarrow ((a < b) \land ((\operatorname{f}\left(a\right) = \operatorname{f}\left(b\right)) \lor (\operatorname{E}\left(\operatorname{f}\left(a\right), \operatorname{f}\left(b\right)\right))))$$

*Formalization.* `D5/S3/Combinatorics/BinomialBases/MazorchukXuOrder.cliqueLift` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Volodymyr Mazorchuk, Shuoyang Xu (2026). *On the number of cokernel-closed additive subcategories for uniformly oriented A_n quivers*. DOI: [10.48550/arXiv.2610.07999](https://doi.org/10.48550/arXiv.2610.07999). URL: <https://arxiv.org/html/2610.07999v2>.

*Commentary.*

The map f collapses consecutive ordered fibers. Each fiber becomes a clique; between different fibers adjacency is read from E. No surjectivity, finiteness or two-element-fiber hypothesis is needed for forward preservation.

**Theorem 1.2 (Preservation under monotone expansion).**

$$\forall A \in \operatorname{Type}\left(\right),\; [\operatorname{LinearOrder}\left(A\right)] \forall B \in \operatorname{Type}\left(\right),\; [\operatorname{LinearOrder}\left(B\right)] \forall E \in A \to \left(A \to \operatorname{Prop}\left(\right)\right),\; \forall f \in B \to A,\; ((\operatorname{Rules}\left(E\right)) \land (\operatorname{Monotone}\left(f\right))) \Rightarrow (\operatorname{Rules}\left(\operatorname{cliqueLift}\left(E, f\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/BinomialBases/MazorchukXuOrder.rules_cliqueLift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Volodymyr Mazorchuk, Shuoyang Xu (2026). *On the number of cokernel-closed additive subcategories for uniformly oriented A_n quivers*. DOI: [10.48550/arXiv.2610.07999](https://doi.org/10.48550/arXiv.2610.07999). URL: <https://arxiv.org/html/2610.07999v2>.

*Commentary.*

For P, a collapsed middle endpoint uses the selected upper edge, and a collapsed upper pair uses its fiber clique. For J, either the original J applies below the collapsed middle fiber, or a premise ending at the largest upper endpoint and P supply the required edge. These cases include every repetition and every collapsed inequality.

**Theorem 1.3 (Two-way compression with an increasing section).**

$$\forall A \in \operatorname{Type}\left(\right),\; [\operatorname{LinearOrder}\left(A\right)] \forall B \in \operatorname{Type}\left(\right),\; [\operatorname{LinearOrder}\left(B\right)] \forall E \in A \to \left(A \to \operatorname{Prop}\left(\right)\right),\; \forall f \in B \to A,\; \forall s \in A \to B,\; ((((\forall a \in A,\; \forall b \in A,\; (\operatorname{E}\left(a, b\right)) \Rightarrow (a < b)) \land (\operatorname{Monotone}\left(f\right))) \land (\operatorname{StrictMono}\left(s\right))) \land (\forall a \in A,\; \operatorname{f}\left(\operatorname{s}\left(a\right)\right) = a)) \Rightarrow ((\operatorname{Rules}\left(\operatorname{cliqueLift}\left(E, f\right)\right)) \Leftrightarrow (\operatorname{Rules}\left(E\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/BinomialBases/MazorchukXuOrder.rules_cliqueLift_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Volodymyr Mazorchuk, Shuoyang Xu (2026). *On the number of cokernel-closed additive subcategories for uniformly oriented A_n quivers*. DOI: [10.48550/arXiv.2610.07999](https://doi.org/10.48550/arXiv.2610.07999). URL: <https://arxiv.org/html/2610.07999v2>.

*Commentary.*

Forward expansion is complemented by restriction along an increasing section s of f. This establishes both directions of admissibility for the clique-fiber construction. It does not by itself identify the position/cutoff fibers of an arbitrary source graph or count their patterns.

**Definition 1.4 (Unordered incidence).**

$$\forall A \in \operatorname{Type}\left(\right),\; \forall E \in A \to \left(A \to \operatorname{Prop}\left(\right)\right),\; \forall a \in A,\; \forall b \in A,\; (\operatorname{Incident}\left(E, a, b\right)) \Leftrightarrow ((\operatorname{E}\left(a, b\right)) \lor (\operatorname{E}\left(b, a\right)))$$

*Formalization.* `D5/S3/Combinatorics/BinomialBases/MazorchukXuOrder.Incident` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Volodymyr Mazorchuk, Shuoyang Xu (2026). *On the number of cokernel-closed additive subcategories for uniformly oriented A_n quivers*. DOI: [10.48550/arXiv.2610.07999](https://doi.org/10.48550/arXiv.2610.07999). URL: <https://arxiv.org/html/2610.07999v2>.

*Commentary.*

The predicate asks for an edge in either order. The strict-order axiom prevents loops when E satisfies Rules.

**Theorem 1.5 (Exceptional incidence increases with ordinary rank).**

$$\forall E \in \operatorname{Nat}\left(\right) \to \left(\operatorname{Nat}\left(\right) \to \operatorname{Prop}\left(\right)\right),\; \forall s \in \operatorname{Nat}\left(\right),\; \forall g \in \operatorname{Nat}\left(\right),\; \forall k \in \operatorname{Nat}\left(\right),\; ((((((\operatorname{Rules}\left(E\right)) \land (\neg (\operatorname{E}\left(0, s\right)))) \land (\operatorname{E}\left(0, g\right))) \land (\operatorname{E}\left(0, k\right))) \land (g < k)) \land (\operatorname{Incident}\left(E, s, g\right))) \Rightarrow (\operatorname{Incident}\left(E, s, k\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/BinomialBases/MazorchukXuOrder.incident_ordinary_mono` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Volodymyr Mazorchuk, Shuoyang Xu (2026). *On the number of cokernel-closed additive subcategories for uniformly oriented A_n quivers*. DOI: [10.48550/arXiv.2610.07999](https://doi.org/10.48550/arXiv.2610.07999). URL: <https://arxiv.org/html/2610.07999v2>.

*Commentary.*

An ordinary positive vertex has an edge from zero. For an exceptional vertex s, propagation handles the placements g<k<s and g<s<k; the maximum rule handles s<g<k. Hence incidence with ordinary vertices is a final segment.

**Theorem 1.6 (The unique cutoff, including no ordinary vertices).**

$$\forall E \in \operatorname{Nat}\left(\right) \to \left(\operatorname{Nat}\left(\right) \to \operatorname{Prop}\left(\right)\right),\; \forall s \in \operatorname{Nat}\left(\right),\; \forall M \in \operatorname{Nat}\left(\right),\; \forall g \in \operatorname{Fin}\left(M\right) \to \operatorname{Nat}\left(\right),\; ((((\operatorname{Rules}\left(E\right)) \land (\neg (\operatorname{E}\left(0, s\right)))) \land (\operatorname{StrictMono}\left(g\right))) \land (\forall r \in \operatorname{Fin}\left(M\right),\; \operatorname{E}\left(0, \operatorname{g}\left(r\right)\right))) \Rightarrow (\exists c \in \operatorname{Nat}\left(\right),\; ((c \le M) \land (\forall r \in \operatorname{Fin}\left(M\right),\; (\operatorname{Incident}\left(E, s, \operatorname{g}\left(r\right)\right)) \Leftrightarrow (c \le \operatorname{val}\left(r\right)))) \land (\forall d \in \operatorname{Nat}\left(\right),\; ((d \le M) \land (\forall r \in \operatorname{Fin}\left(M\right),\; (\operatorname{Incident}\left(E, s, \operatorname{g}\left(r\right)\right)) \Leftrightarrow (d \le \operatorname{val}\left(r\right)))) \Rightarrow (d = c)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/BinomialBases/MazorchukXuOrder.exists_unique_ordinary_cutoff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Volodymyr Mazorchuk, Shuoyang Xu (2026). *On the number of cokernel-closed additive subcategories for uniformly oriented A_n quivers*. DOI: [10.48550/arXiv.2610.07999](https://doi.org/10.48550/arXiv.2610.07999). URL: <https://arxiv.org/html/2610.07999v2>.

*Commentary.*

The increasing list g contains M positive ordinary vertices and is indexed from zero. The unique cutoff c lies from zero through M; incidence holds exactly at indices at least c. Thus c=0 means full incidence and c=M means empty incidence. For M=0 the unique cutoff is zero.

**Definition 1.7 (Symmetric threshold edges).**

$$\forall A \in \operatorname{Type}\left(\right),\; [\operatorname{LinearOrder}\left(A\right)] \forall x \in A \to \operatorname{Rat}\left(\right),\; \forall y \in A \to \operatorname{Rat}\left(\right),\; \forall a \in A,\; \forall b \in A,\; (\operatorname{thresholdEdges}\left(x, y, a, b\right)) \Leftrightarrow (((a < b) \land (\operatorname{y}\left(a\right) < \operatorname{x}\left(b\right))) \land (\operatorname{y}\left(b\right) < \operatorname{x}\left(a\right)))$$

*Formalization.* `D5/S3/Combinatorics/BinomialBases/MazorchukXuOrder.thresholdEdges` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Volodymyr Mazorchuk, Shuoyang Xu (2026). *On the number of cokernel-closed additive subcategories for uniformly oriented A_n quivers*. DOI: [10.48550/arXiv.2610.07999](https://doi.org/10.48550/arXiv.2610.07999). URL: <https://arxiv.org/html/2610.07999v2>.

*Commentary.*

Horizontal coordinates x respect the vertex order; the vertical thresholds y need not be monotone.

**Theorem 1.8 (Threshold graphs satisfy both closure rules).**

$$\forall A \in \operatorname{Type}\left(\right),\; [\operatorname{LinearOrder}\left(A\right)] \forall x \in A \to \operatorname{Rat}\left(\right),\; \forall y \in A \to \operatorname{Rat}\left(\right),\; (\operatorname{Monotone}\left(x\right)) \Rightarrow (\operatorname{Rules}\left(\operatorname{thresholdEdges}\left(x, y\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/BinomialBases/MazorchukXuOrder.rules_thresholdEdges` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Volodymyr Mazorchuk, Shuoyang Xu (2026). *On the number of cokernel-closed additive subcategories for uniformly oriented A_n quivers*. DOI: [10.48550/arXiv.2610.07999](https://doi.org/10.48550/arXiv.2610.07999). URL: <https://arxiv.org/html/2610.07999v2>.

*Commentary.*

For P the two cross inequalities follow by horizontal monotonicity. For J, the premise beginning at the larger lower endpoint gives one inequality and the premise ending at the larger upper endpoint gives the other. Only monotonicity, rather than strict monotonicity, of x is required.

**Definition 1.9 (A greatest universal vertex).**

$$\forall A \in \operatorname{Type}\left(\right),\; [\operatorname{LinearOrder}\left(A\right)] \forall E \in A \to \left(A \to \operatorname{Prop}\left(\right)\right),\; \forall t \in A,\; \forall a \in A,\; \forall b \in A,\; (\operatorname{adjoinGreatest}\left(E, t, a, b\right)) \Leftrightarrow (((a < b) \land (b \le t)) \land ((b = t) \lor (\operatorname{E}\left(a, b\right))))$$

*Formalization.* `D5/S3/Combinatorics/BinomialBases/MazorchukXuOrder.adjoinGreatest` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Volodymyr Mazorchuk, Shuoyang Xu (2026). *On the number of cokernel-closed additive subcategories for uniformly oriented A_n quivers*. DOI: [10.48550/arXiv.2610.07999](https://doi.org/10.48550/arXiv.2610.07999). URL: <https://arxiv.org/html/2610.07999v2>.

*Commentary.*

Keep old edges below t and connect t to every smaller vertex.

**Theorem 1.10 (Adjoining and deleting a universal greatest vertex).**

$$\forall A \in \operatorname{Type}\left(\right),\; [\operatorname{LinearOrder}\left(A\right)] \forall E \in A \to \left(A \to \operatorname{Prop}\left(\right)\right),\; \forall t \in A,\; (\forall a \in A,\; \forall b \in A,\; (\operatorname{E}\left(a, b\right)) \Rightarrow ((a < b) \land (b < t))) \Rightarrow ((\operatorname{Rules}\left(\operatorname{adjoinGreatest}\left(E, t\right)\right)) \Leftrightarrow (\operatorname{Rules}\left(E\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/BinomialBases/MazorchukXuOrder.rules_adjoinGreatest_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Volodymyr Mazorchuk, Shuoyang Xu (2026). *On the number of cokernel-closed additive subcategories for uniformly oriented A_n quivers*. DOI: [10.48550/arXiv.2610.07999](https://doi.org/10.48550/arXiv.2610.07999). URL: <https://arxiv.org/html/2610.07999v2>.

*Commentary.*

If all old edges have strictly increasing endpoints below t, adjoining t is equivalent to the old closure rules. A forced edge ending at t is present by universality; every other instance uses the old rules. Repeated application permits a finite universal tail.

## References

- Truth anchor: `D5/S3/Combinatorics/BinomialBases/MazorchukXuOrder.Incident`
- Truth anchor: `D5/S3/Combinatorics/BinomialBases/MazorchukXuOrder.adjoinGreatest`
- Truth anchor: `D5/S3/Combinatorics/BinomialBases/MazorchukXuOrder.cliqueLift`
- Truth anchor: `D5/S3/Combinatorics/BinomialBases/MazorchukXuOrder.exists_unique_ordinary_cutoff`
- Truth anchor: `D5/S3/Combinatorics/BinomialBases/MazorchukXuOrder.incident_ordinary_mono`
- Truth anchor: `D5/S3/Combinatorics/BinomialBases/MazorchukXuOrder.rules_adjoinGreatest_iff`
- Truth anchor: `D5/S3/Combinatorics/BinomialBases/MazorchukXuOrder.rules_cliqueLift`
- Truth anchor: `D5/S3/Combinatorics/BinomialBases/MazorchukXuOrder.rules_cliqueLift_iff`
- Truth anchor: `D5/S3/Combinatorics/BinomialBases/MazorchukXuOrder.rules_thresholdEdges`
- Truth anchor: `D5/S3/Combinatorics/BinomialBases/MazorchukXuOrder.thresholdEdges`
- Dependency: [D5/S3/Combinatorics/BinomialBases/MazorchukXuClosure](MazorchukXuClosure.md)
