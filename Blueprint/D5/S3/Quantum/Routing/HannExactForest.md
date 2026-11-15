# Exact signed node lift

## Abstract

The actual signed loaded-record relation has the prescribed fixed-coordinate forest lift at every height.

**Definition 1.1 (Original words and independent coordinates).**

Lean statement: `D5/S3/Quantum/Routing/HannExactForest.Node`

*Formalization.* `D5/S3/Quantum/Routing/HannExactForest.Node` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Node 0 is Unit; Node(n+1) is Option(Bool times Node n). The root is Unit at zero and none at positive height. some(b,v) prepends the literal first bit. Thus Node n indexes all words of length at most n. Address n remains the original head-first address type, and Router n indexes words of length strictly less than n. Variable n is Address n disjoint-union Node n: even at height zero the address and the leaf/root are different coordinates. Every address is retained, regardless of coincidences between records. No columns are rescaled or repeated.

**Definition 1.2 (All node clauses).**

Lean statement: `D5/S3/Quantum/Routing/HannExactForest.Equations`

*Formalization.* `D5/S3/Quantum/Routing/HannExactForest.Equations` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

At height zero impose c(root)-x(empty)=0. At positive height impose Local at the root and recurse in each child using childCoeff n x b and childValues n c b. The child's rate is exactly HannSignedCertificate.restrict n q b; every descendant therefore uses the restriction of the same heterogeneous q. Local(t,z,l,r) is z-l-r=0 at t=1, the two equations l+z=0 and r+z=0 at t=-1/2, and the three equations z=0,l=0,r=0 elsewhere. The rate hypothesis puts this last case strictly between the endpoints. There is no additional root equation.

**Definition 1.3 (Distinct node and clause identities).**

Lean statement: `D5/S3/Quantum/Routing/HannExactForest.Row`

*Formalization.* `D5/S3/Quantum/Routing/HannExactForest.Row` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Clause t uses labels in Fin 3: only label 0 at t=1; labels 0 and 1 at t=-1/2; all three labels otherwise. Row 0 q is Unit. Row(n+1,q) is the disjoint union of root clauses and the sigma type of a child bit and one of that child's rows. Rows with identical numerical coefficients remain distinct vertices.

**Definition 1.4 (The literal real homogeneous matrix).**

Lean statement: `D5/S3/Quantum/Routing/HannExactForest.matrix`

*Formalization.* `D5/S3/Quantum/Routing/HannExactForest.matrix` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The leaf row has coefficient -1 on its original address and +1 on its leaf node. An upper root row has +1 at the root and -1 at each child root. A lower root row with label 0 has +1 at the root and left child; label 1 has +1 at the root and right child. In the remaining case labels 0,1,2 select respectively the root,left child,right child, with coefficient +1. All other root-row entries are zero. Child rows insert their exact child matrix with zeros outside that child's address and node coordinates. complexMatrix casts these real entries entrywise to Complex. coordinates n x c is the disjoint-union vector (x,c).

**Definition 1.5 (Forget only nonroot node variables).**

Lean statement: `D5/S3/Quantum/Routing/HannExactForest.Projected`

*Formalization.* `D5/S3/Quantum/Routing/HannExactForest.Projected` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Projected n q x z means there is a node assignment c with c(root)=z satisfying all Equations. Every x coordinate survives the projection. The matrix theorem identifies these equations with complexMatrix.mulVec(coordinates x c)=0, equivalently membership in the complex linear kernel. The actual source synthesis is the sum of x(a) record(n,q,bus,a), and vacuumRecord is the source vacuum tensor.

**Theorem 1.6 (Bidirectional actual-record relation).**

$$\forall n \in Nat,\; \forall q \in \operatorname{Router}\left(n\right) \to Real,\; \forall bus \in Qutrit,\; \left(\forall v \in \operatorname{Router}\left(n\right),\; \operatorname{neg}\left(\frac{1}{2}\right) \le q\left(v\right) \land q\left(v\right) \le 1\right) \Rightarrow \left(\forall x \in \operatorname{Address}\left(n\right) \to Complex,\; \forall z \in Complex,\; \operatorname{synthesis}\left(n, q, bus\right)\left(x\right) = \operatorname{smul}\left(z, \operatorname{vacuumRecord}\left(n, q\right)\right) \Leftrightarrow \left(\exists c \in \operatorname{Node}\left(n\right) \to Complex,\; c\left(\operatorname{root}\left(n\right)\right) = z \land \operatorname{mulVec}\left(\operatorname{complexMatrix}\left(n, q\right), \operatorname{coordinates}\left(n, x, c\right)\right) = 0\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Routing/HannExactForest.relation_iff_matrix_kernel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Both directions hold for every height including zero, every q in the closed signed interval, every qutrit bus, and all complex x and z. The forward construction uses the original upper_relation and below_upper_relation suppliers and recursively assembles one global node assignment. The reverse direction uses the original synthesis_split, vacuum_split, local_upper and local_lower suppliers and the actual child equations. No child realization is chosen independently. At height zero the source record and vacuum are one, and the one row equates the distinct x and c coordinates.

**Theorem 1.7 (Exact row-variable support is a forest).**

$$\forall n \in Nat,\; \forall q \in \operatorname{Router}\left(n\right) \to Real,\; \operatorname{IsAcyclic}\left(\operatorname{support}\left(n, q\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Routing/HannExactForest.support_is_acyclic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

support has one vertex for each Row and one for each Variable, with an edge exactly when the real matrix entry is nonzero. The assertion holds even without the rate-interval hypothesis. Give addresses rank zero, a node of remaining height h rank 3h+2, and a row owned by that node rank 3h+1. Each row has at most one later variable; each variable has at most one later row. The existing chronological pruning supplier then excludes cycles. Separate unary rows and both lower-endpoint rows are included in this argument.

This is a repository-derived exact relation and support theorem. It asserts no equal-weight or nonnegative certificate, probability-normalized total unimodularity, minimum, U0/U1 conclusion, physical signed continuation, Schur or Choi statement, resource bound, hardware claim, or claim of originality.

## References

- Truth anchor: `D5/S3/Quantum/Routing/HannExactForest.Equations`
- Truth anchor: `D5/S3/Quantum/Routing/HannExactForest.Node`
- Truth anchor: `D5/S3/Quantum/Routing/HannExactForest.Projected`
- Truth anchor: `D5/S3/Quantum/Routing/HannExactForest.Row`
- Truth anchor: `D5/S3/Quantum/Routing/HannExactForest.matrix`
- Truth anchor: `D5/S3/Quantum/Routing/HannExactForest.relation_iff_matrix_kernel`
- Truth anchor: `D5/S3/Quantum/Routing/HannExactForest.support_is_acyclic`
- Dependency: [D5/S3/Combinatorics/Graph/Jacobi/LeafPruningRanks](../../Combinatorics/Graph/Jacobi/LeafPruningRanks.md)
- Dependency: [D5/S3/Quantum/Routing/HannSignedCertificate](HannSignedCertificate.md)
