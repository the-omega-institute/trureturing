# Weak coordinate patterns and literal graph realization

## Abstract

Coordinate graphs keep zero, repeated positions and cutoffs, arbitrary exceptional edges, and an ordinary clique. Their admissibility is unchanged by increasing coordinate refinements or by a universal ordinary tail.

**Definition 1.1 (Ordinary ranks and labelled exceptions).**

$$\forall i \in \operatorname{Nat}\left(\right),\; \forall p \in \operatorname{Fin}\left(i\right) \to \operatorname{Nat}\left(\right),\; \operatorname{Equiv}\left(\operatorname{CoordinateVertex}\left(p\right), \operatorname{Sum}\left(\operatorname{Nat}\left(\right), \operatorname{Fin}\left(i\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/BinomialBases/MazorchukXuPatterns.CoordinateVertex` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Volodymyr Mazorchuk, Shuoyang Xu (2026). *On the number of cokernel-closed additive subcategories for uniformly oriented A_n quivers*. DOI: [10.48550/arXiv.2610.07999](https://doi.org/10.48550/arXiv.2610.07999). URL: <https://arxiv.org/html/2610.07999v2>.

*Commentary.*

The two constructors are ordinary(r) for every natural rank r, including the anchor zero, and exceptional(j) for j in Fin i. The position list is a type parameter, so each graph has its own order. The displayed equivalence describes the two constructors; it does not identify their order with a sum order.

**Definition 1.2 (Lexicographic vertex keys).**

$$\forall i \in \operatorname{Nat}\left(\right),\; \forall p \in \operatorname{Fin}\left(i\right) \to \operatorname{Nat}\left(\right),\; (\forall r \in \operatorname{Nat}\left(\right),\; \operatorname{coordinateKey}\left(p, \operatorname{ordinary}\left(r\right)\right) = (r, \operatorname{zero}\left(\right))) \land (\forall j \in \operatorname{Fin}\left(i\right),\; \operatorname{coordinateKey}\left(p, \operatorname{exceptional}\left(j\right)\right) = (p(j), \operatorname{val}\left(j\right) + \operatorname{one}\left(\right)))$$

*Formalization.* `D5/S3/Combinatorics/BinomialBases/MazorchukXuPatterns.coordinateKey` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Volodymyr Mazorchuk, Shuoyang Xu (2026). *On the number of cokernel-closed additive subcategories for uniformly oriented A_n quivers*. DOI: [10.48550/arXiv.2610.07999](https://doi.org/10.48550/arXiv.2610.07999). URL: <https://arxiv.org/html/2610.07999v2>.

*Commentary.*

Keys are ordered lexicographically. Ordinary r precedes every exception in position r, and the exceptional index breaks position ties. Distinct vertices have distinct keys. The coordinate linear order is pulled back along this injection.

**Definition 1.3 (Edges with every tie and exceptional bit retained).**

$$\forall i \in \operatorname{Nat}\left(\right),\; \forall p \in \operatorname{Fin}\left(i\right) \to \operatorname{Nat}\left(\right),\; \forall c \in \operatorname{Fin}\left(i\right) \to \operatorname{Nat}\left(\right),\; \forall B \in \operatorname{Fin}\left(i\right) \to \left(\operatorname{Fin}\left(i\right) \to \operatorname{Prop}\left(\right)\right),\; (((\forall r \in \operatorname{Nat}\left(\right),\; \forall s \in \operatorname{Nat}\left(\right),\; (\operatorname{coordinateEdges}\left(p, c, B\right)(\operatorname{ordinary}\left(r\right), \operatorname{ordinary}\left(s\right))) \Leftrightarrow (r < s)) \land (\forall r \in \operatorname{Nat}\left(\right),\; \forall j \in \operatorname{Fin}\left(i\right),\; (\operatorname{coordinateEdges}\left(p, c, B\right)(\operatorname{ordinary}\left(r\right), \operatorname{exceptional}\left(j\right))) \Leftrightarrow ((r \le p(j)) \land (c(j) < r)))) \land (\forall r \in \operatorname{Nat}\left(\right),\; \forall j \in \operatorname{Fin}\left(i\right),\; (\operatorname{coordinateEdges}\left(p, c, B\right)(\operatorname{exceptional}\left(j\right), \operatorname{ordinary}\left(r\right))) \Leftrightarrow ((p(j) < r) \land (c(j) < r)))) \land (\forall j \in \operatorname{Fin}\left(i\right),\; \forall k \in \operatorname{Fin}\left(i\right),\; (\operatorname{coordinateEdges}\left(p, c, B\right)(\operatorname{exceptional}\left(j\right), \operatorname{exceptional}\left(k\right))) \Leftrightarrow ((\operatorname{exceptional}\left(j\right) < \operatorname{exceptional}\left(k\right)) \land (\operatorname{B}\left(j, k\right))))$$

*Formalization.* `D5/S3/Combinatorics/BinomialBases/MazorchukXuPatterns.coordinateEdges` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Volodymyr Mazorchuk, Shuoyang Xu (2026). *On the number of cokernel-closed additive subcategories for uniformly oriented A_n quivers*. DOI: [10.48550/arXiv.2610.07999](https://doi.org/10.48550/arXiv.2610.07999). URL: <https://arxiv.org/html/2610.07999v2>.

*Commentary.*

Only increasing endpoint pairs are edges. All ordinary pairs are adjacent. The pair involving exceptional j and ordinary rank r is adjacent exactly when c(j)<r, in either possible endpoint order. The ordered exceptional pair j,k is adjacent exactly when B(j,k). No condition on B, positivity, distinctness or monotonicity of p or c is built into this definition.

**Theorem 1.4 (Increasing refinements preserve all weak patterns).**

$$\forall i \in \operatorname{Nat}\left(\right),\; \forall p \in \operatorname{Fin}\left(i\right) \to \operatorname{Nat}\left(\right),\; \forall c \in \operatorname{Fin}\left(i\right) \to \operatorname{Nat}\left(\right),\; \forall B \in \operatorname{Fin}\left(i\right) \to \left(\operatorname{Fin}\left(i\right) \to \operatorname{Prop}\left(\right)\right),\; \forall e \in \operatorname{Nat}\left(\right) \to \operatorname{Nat}\left(\right),\; ((\operatorname{StrictMono}\left(e\right)) \land (\operatorname{e}\left(\operatorname{zero}\left(\right)\right) = \operatorname{zero}\left(\right))) \Rightarrow ((\operatorname{Rules}\left(\operatorname{coordinateEdges}\left(\operatorname{comp}\left(e, p\right), \operatorname{comp}\left(e, c\right), B\right)\right)) \Leftrightarrow (\operatorname{Rules}\left(\operatorname{coordinateEdges}\left(p, c, B\right)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/BinomialBases/MazorchukXuPatterns.coordinate_rules_refinement_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Volodymyr Mazorchuk, Shuoyang Xu (2026). *On the number of cokernel-closed additive subcategories for uniformly oriented A_n quivers*. DOI: [10.48550/arXiv.2610.07999](https://doi.org/10.48550/arXiv.2610.07999). URL: <https://arxiv.org/html/2610.07999v2>.

*Commentary.*

For an increasing map e, send ordinary rank r to the least k with r<=e(k), and leave each exceptional label fixed. This collapse is monotone. Its increasing section sends ordinary k to e(k), again fixing exceptional labels. Incidence transforms because e(c)<r is equivalent to c<ceil_e(r). Hence the expanded graph is exactly the clique lift of the original graph, including all collapsed ordinary fibers and every equality between coordinate entries. The clique-lift equivalence proves both directions of Rules. The hypothesis e(0)=0 retains the distinguished zero used for source patterns.

**Definition 1.5 (A universal tail above an initial segment).**

$$\forall A \in \operatorname{Type}\left(\right),\; [\operatorname{LinearOrder}\left(A\right)] \forall E \in A \to \left(A \to \operatorname{Prop}\left(\right)\right),\; \forall S \in A \to \operatorname{Prop}\left(\right),\; \forall a \in A,\; \forall b \in A,\; (\operatorname{universalTail}\left(E, S, a, b\right)) \Leftrightarrow ((a < b) \land ((\neg (S(b))) \lor (\operatorname{E}\left(a, b\right))))$$

*Formalization.* `D5/S3/Combinatorics/BinomialBases/MazorchukXuPatterns.universalTail` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Volodymyr Mazorchuk, Shuoyang Xu (2026). *On the number of cokernel-closed additive subcategories for uniformly oriented A_n quivers*. DOI: [10.48550/arXiv.2610.07999](https://doi.org/10.48550/arXiv.2610.07999). URL: <https://arxiv.org/html/2610.07999v2>.

*Commentary.*

Every increasing pair ending outside S is added; edges within S are read from E. When S is downward closed and E is supported there, this operation preserves and reflects both ordered closure rules, even for an infinite tail.

**Definition 1.6 (The finite coordinate segment).**

$$\forall i \in \operatorname{Nat}\left(\right),\; \forall p \in \operatorname{Fin}\left(i\right) \to \operatorname{Nat}\left(\right),\; \forall M \in \operatorname{Nat}\left(\right),\; (\forall r \in \operatorname{Nat}\left(\right),\; (\operatorname{coordinateInside}\left(M, \operatorname{ordinary}\left(r\right)\right)) \Leftrightarrow (r \le M)) \land (\forall j \in \operatorname{Fin}\left(i\right),\; \operatorname{coordinateInside}\left(M, \operatorname{exceptional}\left(j\right)\right))$$

*Formalization.* `D5/S3/Combinatorics/BinomialBases/MazorchukXuPatterns.coordinateInside` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Volodymyr Mazorchuk, Shuoyang Xu (2026). *On the number of cokernel-closed additive subcategories for uniformly oriented A_n quivers*. DOI: [10.48550/arXiv.2610.07999](https://doi.org/10.48550/arXiv.2610.07999). URL: <https://arxiv.org/html/2610.07999v2>.

*Commentary.*

The segment contains ordinary ranks zero through M and every exceptional vertex. Under p(j)<=M it is an initial segment in the coordinate order.

**Definition 1.7 (Edges on the finite coordinate segment).**

$$\forall i \in \operatorname{Nat}\left(\right),\; \forall p \in \operatorname{Fin}\left(i\right) \to \operatorname{Nat}\left(\right),\; \forall c \in \operatorname{Fin}\left(i\right) \to \operatorname{Nat}\left(\right),\; \forall B \in \operatorname{Fin}\left(i\right) \to \left(\operatorname{Fin}\left(i\right) \to \operatorname{Prop}\left(\right)\right),\; \forall M \in \operatorname{Nat}\left(\right),\; \forall u \in \operatorname{CoordinateVertex}\left(p\right),\; \forall v \in \operatorname{CoordinateVertex}\left(p\right),\; (\operatorname{boundedCoordinateEdges}\left(M, p, c, B, u, v\right)) \Leftrightarrow ((\operatorname{coordinateEdges}\left(p, c, B\right)(u, v)) \land (\operatorname{coordinateInside}\left(M, v\right)))$$

*Formalization.* `D5/S3/Combinatorics/BinomialBases/MazorchukXuPatterns.boundedCoordinateEdges` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Volodymyr Mazorchuk, Shuoyang Xu (2026). *On the number of cokernel-closed additive subcategories for uniformly oriented A_n quivers*. DOI: [10.48550/arXiv.2610.07999](https://doi.org/10.48550/arXiv.2610.07999). URL: <https://arxiv.org/html/2610.07999v2>.

*Commentary.*

Retain coordinate edges whose upper endpoint belongs to the finite segment. When positions are bounded by M the lower endpoint belongs to the segment as well.

**Theorem 1.8 (Coordinate segments are initial segments).**

$$\forall i \in \operatorname{Nat}\left(\right),\; \forall M \in \operatorname{Nat}\left(\right),\; \forall p \in \operatorname{Fin}\left(i\right) \to \operatorname{Nat}\left(\right),\; (\forall j \in \operatorname{Fin}\left(i\right),\; p(j) \le M) \Rightarrow (\forall u \in \operatorname{CoordinateVertex}\left(p\right),\; \forall v \in \operatorname{CoordinateVertex}\left(p\right),\; ((u \le v) \land (\operatorname{coordinateInside}\left(M, v\right))) \Rightarrow (\operatorname{coordinateInside}\left(M, u\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/BinomialBases/MazorchukXuPatterns.coordinateInside_downward` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Volodymyr Mazorchuk, Shuoyang Xu (2026). *On the number of cokernel-closed additive subcategories for uniformly oriented A_n quivers*. DOI: [10.48550/arXiv.2610.07999](https://doi.org/10.48550/arXiv.2610.07999). URL: <https://arxiv.org/html/2610.07999v2>.

*Commentary.*

If every exceptional position is at most M, every vertex preceding a vertex in the segment is also in the segment. An ordinary vertex before exception j has rank at most p(j); all exceptions belong to the segment.

**Theorem 1.9 (Deleting every universal ordinary tail).**

$$\forall i \in \operatorname{Nat}\left(\right),\; \forall p \in \operatorname{Fin}\left(i\right) \to \operatorname{Nat}\left(\right),\; \forall c \in \operatorname{Fin}\left(i\right) \to \operatorname{Nat}\left(\right),\; \forall B \in \operatorname{Fin}\left(i\right) \to \left(\operatorname{Fin}\left(i\right) \to \operatorname{Prop}\left(\right)\right),\; \forall M \in \operatorname{Nat}\left(\right),\; ((\forall j \in \operatorname{Fin}\left(i\right),\; p(j) \le M) \land (\forall j \in \operatorname{Fin}\left(i\right),\; c(j) \le M)) \Rightarrow ((\operatorname{Rules}\left(\operatorname{boundedCoordinateEdges}\left(M, p, c, B\right)\right)) \Leftrightarrow (\operatorname{Rules}\left(\operatorname{coordinateEdges}\left(p, c, B\right)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/BinomialBases/MazorchukXuPatterns.coordinate_rules_bounded_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Volodymyr Mazorchuk, Shuoyang Xu (2026). *On the number of cokernel-closed additive subcategories for uniformly oriented A_n quivers*. DOI: [10.48550/arXiv.2610.07999](https://doi.org/10.48550/arXiv.2610.07999). URL: <https://arxiv.org/html/2610.07999v2>.

*Commentary.*

When positions and cutoffs are at most M, each ordinary vertex of rank greater than M follows every exception and is adjacent to every earlier vertex. The infinite graph is exactly the universal-tail extension of the bounded graph. The universal-tail argument gives equivalence, including M=0 and tied or zero entries.

**Definition 1.10 (The finite vertex subtype).**

$$\forall i \in \operatorname{Nat}\left(\right),\; \forall M \in \operatorname{Nat}\left(\right),\; \forall p \in \operatorname{Fin}\left(i\right) \to \operatorname{Nat}\left(\right),\; \operatorname{BoundedCoordinateVertex}\left(M, p\right) = \{u \in \operatorname{CoordinateVertex}\left(p\right)| \operatorname{coordinateInside}\left(M, u\right)\}$$

*Formalization.* `D5/S3/Combinatorics/BinomialBases/MazorchukXuPatterns.BoundedCoordinateVertex` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Volodymyr Mazorchuk, Shuoyang Xu (2026). *On the number of cokernel-closed additive subcategories for uniformly oriented A_n quivers*. DOI: [10.48550/arXiv.2610.07999](https://doi.org/10.48550/arXiv.2610.07999). URL: <https://arxiv.org/html/2610.07999v2>.

*Commentary.*

This subtype inherits the coordinate order. It includes the anchor even when there are no positive ordinary vertices.

**Definition 1.11 (Canonical natural labels).**

$$\forall i \in \operatorname{Nat}\left(\right),\; \forall p \in \operatorname{Fin}\left(i\right) \to \operatorname{Nat}\left(\right),\; (\forall r \in \operatorname{Nat}\left(\right),\; \operatorname{coordinateLabel}\left(p, \operatorname{ordinary}\left(r\right)\right) = r + \operatorname{card}\left(\{j \in \operatorname{Fin}\left(i\right)| p(j) < r\}\right)) \land (\forall j \in \operatorname{Fin}\left(i\right),\; \operatorname{coordinateLabel}\left(p, \operatorname{exceptional}\left(j\right)\right) = p(j) + \operatorname{val}\left(j\right) + \operatorname{one}\left(\right))$$

*Formalization.* `D5/S3/Combinatorics/BinomialBases/MazorchukXuPatterns.coordinateLabel` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Volodymyr Mazorchuk, Shuoyang Xu (2026). *On the number of cokernel-closed additive subcategories for uniformly oriented A_n quivers*. DOI: [10.48550/arXiv.2610.07999](https://doi.org/10.48550/arXiv.2610.07999). URL: <https://arxiv.org/html/2610.07999v2>.

*Commentary.*

An ordinary vertex of rank r has r earlier ordinary vertices and one earlier exceptional vertex for each p(j)<r. Exception j has p(j) earlier positive ordinary vertices, the anchor, and j earlier exceptions. These formulas include every zero and tied position.

**Theorem 1.12 (Labels preserve the coordinate order).**

$$\forall i \in \operatorname{Nat}\left(\right),\; \forall p \in \operatorname{Fin}\left(i\right) \to \operatorname{Nat}\left(\right),\; (\operatorname{Monotone}\left(p\right)) \Rightarrow (\operatorname{StrictMono}\left(\operatorname{coordinateLabel}\left(p\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/BinomialBases/MazorchukXuPatterns.coordinateLabel_strictMono` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Volodymyr Mazorchuk, Shuoyang Xu (2026). *On the number of cokernel-closed additive subcategories for uniformly oriented A_n quivers*. DOI: [10.48550/arXiv.2610.07999](https://doi.org/10.48550/arXiv.2610.07999). URL: <https://arxiv.org/html/2610.07999v2>.

*Commentary.*

For an increasing position list, the number of positions below r is a nondecreasing function of r. Its value is at most j when r<=p(j), and exceeds j when p(j)<r. These inequalities prove the two mixed vertex comparisons; ordinary and exceptional comparisons follow from the rank and index increments.

**Theorem 1.13 (Labels stay in the full finite interval).**

$$\forall i \in \operatorname{Nat}\left(\right),\; \forall M \in \operatorname{Nat}\left(\right),\; \forall p \in \operatorname{Fin}\left(i\right) \to \operatorname{Nat}\left(\right),\; (\forall j \in \operatorname{Fin}\left(i\right),\; p(j) \le M) \Rightarrow (\forall u \in \operatorname{BoundedCoordinateVertex}\left(M, p\right),\; \operatorname{coordinateLabel}\left(p, \operatorname{val}\left(u\right)\right) \le M + i)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/BinomialBases/MazorchukXuPatterns.coordinateLabel_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Volodymyr Mazorchuk, Shuoyang Xu (2026). *On the number of cokernel-closed additive subcategories for uniformly oriented A_n quivers*. DOI: [10.48550/arXiv.2610.07999](https://doi.org/10.48550/arXiv.2610.07999). URL: <https://arxiv.org/html/2610.07999v2>.

*Commentary.*

There are i exceptional positions in total. Ordinary rank r<=M therefore has label at most M+i. The j-th exception has p(j)<=M and j<i, giving the same bound. Monotonicity is not needed for this bound.

**Theorem 1.14 (Every finite label occurs exactly once).**

$$\forall i \in \operatorname{Nat}\left(\right),\; \forall M \in \operatorname{Nat}\left(\right),\; \forall p \in \operatorname{Fin}\left(i\right) \to \operatorname{Nat}\left(\right),\; ((\operatorname{Monotone}\left(p\right)) \land (\forall j \in \operatorname{Fin}\left(i\right),\; p(j) \le M)) \Rightarrow ((\forall u \in \operatorname{BoundedCoordinateVertex}\left(M, p\right),\; \forall v \in \operatorname{BoundedCoordinateVertex}\left(M, p\right),\; (\operatorname{coordinateLabel}\left(p, \operatorname{val}\left(u\right)\right) = \operatorname{coordinateLabel}\left(p, \operatorname{val}\left(v\right)\right)) \Rightarrow (u = v)) \land (\forall a \in \operatorname{Nat}\left(\right),\; (a \le M + i) \Rightarrow (\exists u \in \operatorname{BoundedCoordinateVertex}\left(M, p\right),\; \operatorname{coordinateLabel}\left(p, \operatorname{val}\left(u\right)\right) = a)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/BinomialBases/MazorchukXuPatterns.coordinateLabel_bijective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Volodymyr Mazorchuk, Shuoyang Xu (2026). *On the number of cokernel-closed additive subcategories for uniformly oriented A_n quivers*. DOI: [10.48550/arXiv.2610.07999](https://doi.org/10.48550/arXiv.2610.07999). URL: <https://arxiv.org/html/2610.07999v2>.

*Commentary.*

The finite vertex set has M+1 ordinary vertices and i exceptions. The strict label map injects it into the M+i+1 labels zero through M+i, so equal finite cardinalities give bijectivity. This includes the single anchor when M=i=0. The theorem states bijectivity of the map into Fin(M+i+1); the display gives its equivalent uniqueness and full natural-interval surjectivity clauses.

**Theorem 1.15 (An exact increasing realization of every source graph).**

$$\forall n \in \operatorname{Nat}\left(\right),\; \forall i \in \operatorname{Nat}\left(\right),\; (i \le n + \operatorname{one}\left(\right)) \Rightarrow (\forall A \in \operatorname{Finset}\left(\operatorname{Prod}\left(\operatorname{Nat}\left(\right), \operatorname{Nat}\left(\right)\right)\right),\; (A \in \operatorname{edgeFamily}\left(n, n + \operatorname{one}\left(\right) - i\right)) \Rightarrow (\exists p \in \operatorname{Fin}\left(i\right) \to \operatorname{Nat}\left(\right),\; \exists c \in \operatorname{Fin}\left(i\right) \to \operatorname{Nat}\left(\right),\; \exists B \in \operatorname{Fin}\left(i\right) \to \left(\operatorname{Fin}\left(i\right) \to \operatorname{Prop}\left(\right)\right),\; \exists f \in \operatorname{BoundedCoordinateVertex}\left(n + \operatorname{one}\left(\right) - i, p\right) \to \operatorname{Nat}\left(\right),\; (((((((\operatorname{Monotone}\left(p\right)) \land (\forall j \in \operatorname{Fin}\left(i\right),\; p(j) \le n + \operatorname{one}\left(\right) - i)) \land (\forall j \in \operatorname{Fin}\left(i\right),\; c(j) \le n + \operatorname{one}\left(\right) - i)) \land (\forall j \in \operatorname{Fin}\left(i\right),\; \forall k \in \operatorname{Fin}\left(i\right),\; (\operatorname{B}\left(j, k\right)) \Rightarrow (j < k))) \land (\operatorname{StrictMono}\left(f\right))) \land (\forall u \in \operatorname{BoundedCoordinateVertex}\left(n + \operatorname{one}\left(\right) - i, p\right),\; f(u) \le n + \operatorname{one}\left(\right))) \land (\forall a \in \operatorname{Nat}\left(\right),\; (a \le n + \operatorname{one}\left(\right)) \Rightarrow (\exists u \in \operatorname{BoundedCoordinateVertex}\left(n + \operatorname{one}\left(\right) - i, p\right),\; f(u) = a))) \land (\forall u \in \operatorname{BoundedCoordinateVertex}\left(n + \operatorname{one}\left(\right) - i, p\right),\; \forall v \in \operatorname{BoundedCoordinateVertex}\left(n + \operatorname{one}\left(\right) - i, p\right),\; ((f(u), f(v)) \in A) \Leftrightarrow (\operatorname{coordinateEdges}\left(p, c, B\right)(\operatorname{val}\left(u\right), \operatorname{val}\left(v\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/BinomialBases/MazorchukXuPatterns.edgeFamily_coordinate_realization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Volodymyr Mazorchuk, Shuoyang Xu (2026). *On the number of cokernel-closed additive subcategories for uniformly oriented A_n quivers*. DOI: [10.48550/arXiv.2610.07999](https://doi.org/10.48550/arXiv.2610.07999). URL: <https://arxiv.org/html/2610.07999v2>.

*Commentary.*

Extract the ordinary and exceptional lists from the literal edge family. Ordinary rank zero maps to the anchor; positive ordinary rank r maps to entry r-1 of the ordered ordinary list; exceptional j maps to the j-th missing anchor neighbor. Position and cutoff laws give the mixed edges, the ordinary vertices form a clique, and B retains each actual exceptional edge. The map is increasing and bijects onto every natural vertex from zero through n+1. Thus this is an exact edge correspondence, including zero positions, coinciding coordinates and an empty positive ordinary list. It does not count coordinate patterns or assert polynomiality.

## References

- Truth anchor: `D5/S3/Combinatorics/BinomialBases/MazorchukXuPatterns.BoundedCoordinateVertex`
- Truth anchor: `D5/S3/Combinatorics/BinomialBases/MazorchukXuPatterns.CoordinateVertex`
- Truth anchor: `D5/S3/Combinatorics/BinomialBases/MazorchukXuPatterns.boundedCoordinateEdges`
- Truth anchor: `D5/S3/Combinatorics/BinomialBases/MazorchukXuPatterns.coordinateEdges`
- Truth anchor: `D5/S3/Combinatorics/BinomialBases/MazorchukXuPatterns.coordinateInside`
- Truth anchor: `D5/S3/Combinatorics/BinomialBases/MazorchukXuPatterns.coordinateInside_downward`
- Truth anchor: `D5/S3/Combinatorics/BinomialBases/MazorchukXuPatterns.coordinateKey`
- Truth anchor: `D5/S3/Combinatorics/BinomialBases/MazorchukXuPatterns.coordinateLabel`
- Truth anchor: `D5/S3/Combinatorics/BinomialBases/MazorchukXuPatterns.coordinateLabel_bijective`
- Truth anchor: `D5/S3/Combinatorics/BinomialBases/MazorchukXuPatterns.coordinateLabel_bound`
- Truth anchor: `D5/S3/Combinatorics/BinomialBases/MazorchukXuPatterns.coordinateLabel_strictMono`
- Truth anchor: `D5/S3/Combinatorics/BinomialBases/MazorchukXuPatterns.coordinate_rules_bounded_iff`
- Truth anchor: `D5/S3/Combinatorics/BinomialBases/MazorchukXuPatterns.coordinate_rules_refinement_iff`
- Truth anchor: `D5/S3/Combinatorics/BinomialBases/MazorchukXuPatterns.edgeFamily_coordinate_realization`
- Truth anchor: `D5/S3/Combinatorics/BinomialBases/MazorchukXuPatterns.universalTail`
- Dependency: [D5/S3/Combinatorics/BinomialBases/MazorchukXuGeneric](MazorchukXuGeneric.md)
