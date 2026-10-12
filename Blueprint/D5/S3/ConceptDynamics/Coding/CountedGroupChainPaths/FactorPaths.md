# Actual ordered factor paths and reversible peeling

## Abstract

Actual ordered factor paths and reversible peeling. All numbered edges, ordered labels and source conditions are retained.

**Definition 1.1 (The ordered list of actual rectangular factors).**

$$\forall H \in Type,\; [\operatorname{Group}\left(H\right)]\forall n \in Nat, m \in Nat, L \in Nat,\; \operatorname{Factors}\left(H, n, m, L\right):Type$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/FactorPaths.Factors` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Factors H n m L stores L actual natural group-ring matrices with composable finite dimensions, beginning at n and ending at m. The zero-length constructor has the same initial and terminal dimension. A cons constructor stores its first rectangular matrix and the entire remaining sequence; dimensions may vary and may be zero.

**Definition 1.2 (Multiply in the prescribed factor order).**

$$\forall H \in Type,\; [\operatorname{Group}\left(H\right)]\forall n \in Nat, m \in Nat, L \in Nat, f \in \operatorname{Factors}\left(H, n, m, L\right),\; \operatorname{factorProduct}\left(f\right):\operatorname{GroupMat}\left(H, n, m\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/FactorPaths.factorProduct` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The product of the empty sequence is the identity matrix. The product of a sequence with first matrix M and tail f is M times factorProduct(f). Thus the recursive multiplication follows the left-to-right order of all supplied factors.

**Definition 1.3 (Retain a last factor).**

$$\forall H \in Type,\; [\operatorname{Group}\left(H\right)]\forall n \in Nat, m \in Nat, L \in Nat, f \in \operatorname{Factors}\left(H, n, m, L\right), k \in Nat, M \in \operatorname{GroupMat}\left(H, m, k\right),\; \operatorname{factorSnoc}\left(f, M\right):\operatorname{Factors}\left(H, n, k, \operatorname{successor}\left(L\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/FactorPaths.factorSnoc` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

factorSnoc f M appends the actual rectangular matrix M at the right-hand end. Its product is factorProduct(f) times M. This operation expresses the decreasing order of the V factors without changing any factor data.

**Definition 1.4 (Typed paths with a named empty vertex).**

$$\forall H \in Type,\; [\operatorname{Group}\left(H\right)]\forall n \in Nat, m \in Nat, L \in Nat, f \in \operatorname{Factors}\left(H, n, m, L\right), i \in \operatorname{Fin}\left(n\right), j \in \operatorname{Fin}\left(m\right),\; \operatorname{FactorPath}\left(f, i, j\right):Type$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/FactorPaths.FactorPath` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

FactorPath f i j retains the complete ordered factor tuple between endpoints i and j. At length zero it contains a vertex v with v=i and v=j. At a nonempty layer it contains the next vertex v, a group label h, a number in Fin(coeff(M[i,v],h)), and a path in the tail from v to j. The nested sigma and product orders compare these coordinates lexicographically. No edge number is identified with another.

**Definition 1.5 (Ordered total label).**

$$\forall H \in Type,\; [\operatorname{Group}\left(H\right)]\forall n \in Nat, m \in Nat, L \in Nat, f \in \operatorname{Factors}\left(H, n, m, L\right), i \in \operatorname{Fin}\left(n\right), j \in \operatorname{Fin}\left(m\right), p \in \operatorname{FactorPath}\left(f, i, j\right),\; \operatorname{factorLabel}\left(f, p\right):H$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/FactorPaths.factorLabel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The empty path has label one. A nonempty path has label h times the tail label, where h is the first edge label. This is the ordered group product in traversal order; no commutativity assumption is used.

**Definition 1.6 (The specified zero-edge vertex).**

$$\forall H \in Type,\; [\operatorname{Group}\left(H\right)]\forall n \in Nat, i \in \operatorname{Fin}\left(n\right),\; \operatorname{nilPath}\left(i\right):\operatorname{FactorPath}\left(\operatorname{nil}\left(H, n\right), i, i\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/FactorPaths.nilPath` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

nilPath i stores the actual vertex i and both endpoint equalities. Its total label is one. At a zero-dimensional carrier there is no vertex to choose, and no extra inhabitance assumption is imposed.

**Definition 1.7 (The actual first numbered edge).**

$$\forall H \in Type,\; [\operatorname{Group}\left(H\right)]\forall n \in Nat, k \in Nat, m \in Nat, L \in Nat, M \in \operatorname{GroupMat}\left(H, n, k\right), f \in \operatorname{Factors}\left(H, k, m, L\right), e \in \operatorname{Edge}\left(M\right), j \in \operatorname{Fin}\left(m\right), p \in \operatorname{FactorPath}\left(f, \operatorname{target}\left(e\right), j\right),\; \operatorname{consPath}\left(M, f, e, p\right):\operatorname{FactorPath}\left(\operatorname{cons}\left(M, f\right), \operatorname{source}\left(e\right), j\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/FactorPaths.consPath` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

consPath stores the first edge's target, group label and copy number and the supplied typed tail. Its outside source is exactly the edge source, and the tail begins at exactly the edge target.

**Definition 1.8 (The entire endpoint and label fiber).**

$$\forall H \in Type,\; [\operatorname{Group}\left(H\right)]\forall n \in Nat, m \in Nat, L \in Nat, f \in \operatorname{Factors}\left(H, n, m, L\right), i \in \operatorname{Fin}\left(n\right), j \in \operatorname{Fin}\left(m\right), g \in H,\; \operatorname{FactorFiber}\left(f, i, j, g\right) = \operatorname{Subtype}\left(\operatorname{FactorPath}\left(f, i, j\right), \operatorname{labelEquals}\left(f, g\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/FactorPaths.FactorFiber` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The fiber contains all actual paths with the specified endpoints and total ordered group label. It includes every original coefficient number. A fiber may be empty.

**Definition 1.9 (Resolve the first factor of a whole fiber).**

$$\forall H \in Type,\; [\operatorname{Group}\left(H\right)]\forall n \in Nat, k \in Nat, m \in Nat, L \in Nat, M \in \operatorname{GroupMat}\left(H, n, k\right), f \in \operatorname{Factors}\left(H, k, m, L\right), i \in \operatorname{Fin}\left(n\right), j \in \operatorname{Fin}\left(m\right), g \in H,\; \operatorname{Equiv}\left(\operatorname{FactorFiber}\left(\operatorname{cons}\left(M, f\right), i, j, g\right), \operatorname{FirstFactorFiber}\left(M, f, i, j, g\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/FactorPaths.fiberConsEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

FirstFactorFiber is the sigma over v in Fin k and h in H of Fin(coeff(M[i,v],h)) times FactorFiber(f,v,j,h inverse times g). The equivalence retains the same first vertex, label, number and actual tail. The equation h times label(tail)=g is equivalent to label(tail)=h inverse times g.

**Theorem 1.10 (Coefficients count complete actual paths).**

$$\forall H \in Type,\; [\operatorname{Group}\left(H\right)][\operatorname{Fintype}\left(H\right)]\forall n \in Nat, m \in Nat, L \in Nat, f \in \operatorname{Factors}\left(H, n, m, L\right), i \in \operatorname{Fin}\left(n\right), j \in \operatorname{Fin}\left(m\right), g \in H,\; \operatorname{card}\left(\operatorname{FactorFiber}\left(f, i, j, g\right)\right) = \operatorname{coeff}\left(\operatorname{entry}\left(\operatorname{factorProduct}\left(f\right), i, j\right), g\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/FactorPaths.fiber_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Induction on the factor sequence reduces the count to the sum over the next vertex and first group label. Each summand is the first coefficient times the count of the actual tail fiber. Group-ring convolution and rectangular matrix multiplication give precisely the product coefficient. At length zero the only possible path has identical endpoints and label one; every other fiber is empty.

**Definition 1.11 (The increasing global rank).**

$$\forall H \in Type,\; [\operatorname{Group}\left(H\right)][\operatorname{Fintype}\left(H\right)][\operatorname{LinearOrder}\left(H\right)]\forall n \in Nat, m \in Nat, L \in Nat, f \in \operatorname{Factors}\left(H, n, m, L\right), i \in \operatorname{Fin}\left(n\right), j \in \operatorname{Fin}\left(m\right), g \in H,\; \operatorname{OrderIso}\left(\operatorname{Fin}\left(\operatorname{coeff}\left(\operatorname{entry}\left(\operatorname{factorProduct}\left(f\right), i, j\right), g\right)\right), \operatorname{FactorFiber}\left(f, i, j, g\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/FactorPaths.rankedFiberOrderIso` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The increasing finite-order enumeration ranks the complete endpoint and total-label fiber in one operation. Its order is the lexicographic order of every original factor-edge coordinate. Empty fibers have a unique empty order isomorphism. This enumeration does not identify an iterated binary rank with the whole-path rank.

**Definition 1.12 (Both directions of the global fiber rank).**

$$\forall H \in Type,\; [\operatorname{Group}\left(H\right)][\operatorname{Fintype}\left(H\right)][\operatorname{LinearOrder}\left(H\right)]\forall n \in Nat, m \in Nat, L \in Nat, f \in \operatorname{Factors}\left(H, n, m, L\right), i \in \operatorname{Fin}\left(n\right), j \in \operatorname{Fin}\left(m\right), g \in H,\; \operatorname{Equiv}\left(\operatorname{Fin}\left(\operatorname{coeff}\left(\operatorname{entry}\left(\operatorname{factorProduct}\left(f\right), i, j\right), g\right)\right), \operatorname{FactorFiber}\left(f, i, j, g\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/FactorPaths.rankedFiberEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The equivalence underlying the increasing rank sends copy c of the cumulative matrix edge to the c-th complete factor tuple. The inverse returns that same global rank and recovers all factor-edge data.

**Definition 1.13 (Transport all standard matrix edges).**

$$\forall H \in Type,\; [\operatorname{Group}\left(H\right)][\operatorname{Fintype}\left(H\right)][\operatorname{LinearOrder}\left(H\right)]\forall n \in Nat, m \in Nat, L \in Nat, f \in \operatorname{Factors}\left(H, n, m, L\right),\; \operatorname{Equiv}\left(\operatorname{Edge}\left(\operatorname{factorProduct}\left(f\right)\right), \operatorname{AllEndpointLabelFibers}\left(f\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/FactorPaths.edgePathEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

AllEndpointLabelFibers is the sigma over i in Fin n, j in Fin m and g in H of FactorFiber(f,i,j,g). The equivalence first reads the standard edge's source, target, label and copy number, then applies the global rank in that same fiber. Both outside endpoints and the total ordered label are therefore preserved, and both inverse laws recover every original copy number.

**Definition 1.14 (Prescribed factor equalities at every layer).**

$$\forall H \in Type,\; [\operatorname{Group}\left(H\right)][\operatorname{Fintype}\left(H\right)]\forall n \in Nat, m \in Nat, L \in Nat, A \in \operatorname{GroupMat}\left(H, n, n\right), B \in \operatorname{GroupMat}\left(H, m, m\right),\; \operatorname{Chain}\left(H, A, B, L\right):Type$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/FactorPaths.Chain` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Chain H A B L stores the actual length-L supplied chain in Type. A cons step retains U, V, its source matrix A, its next matrix C, the equalities A=UV and C=VU, and the entire tail. The nil step retains its matrix and has identical endpoints. The data impose neither positive dimensions nor positive coefficients.

**Definition 1.15 (Increasing U factor order).**

$$\forall H \in Type,\; [\operatorname{Group}\left(H\right)][\operatorname{Fintype}\left(H\right)]\forall n \in Nat, m \in Nat, L \in Nat, A \in \operatorname{GroupMat}\left(H, n, n\right), B \in \operatorname{GroupMat}\left(H, m, m\right), c \in \operatorname{Chain}\left(H, A, B, L\right),\; \operatorname{forwardFactors}\left(c\right):\operatorname{Factors}\left(H, n, m, L\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/FactorPaths.forwardFactors` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

forwardFactors keeps U at the first layer and recursively keeps the tail's U factors. Thus it is exactly U0 through U(L-1), with all heterogeneous dimensions retained.

**Definition 1.16 (Decreasing V factor order).**

$$\forall H \in Type,\; [\operatorname{Group}\left(H\right)][\operatorname{Fintype}\left(H\right)]\forall n \in Nat, m \in Nat, L \in Nat, A \in \operatorname{GroupMat}\left(H, n, n\right), B \in \operatorname{GroupMat}\left(H, m, m\right), c \in \operatorname{Chain}\left(H, A, B, L\right),\; \operatorname{backwardFactors}\left(c\right):\operatorname{Factors}\left(H, m, n, L\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/FactorPaths.backwardFactors` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

backwardFactors recursively keeps the tail's reversed V factors and appends the first V at the right. Thus it is exactly V(L-1) through V0.

**Definition 1.17 (The forward cumulative rectangle).**

$$\forall H \in Type,\; [\operatorname{Group}\left(H\right)][\operatorname{Fintype}\left(H\right)]\forall n \in Nat, m \in Nat, L \in Nat, A \in \operatorname{GroupMat}\left(H, n, n\right), B \in \operatorname{GroupMat}\left(H, m, m\right), c \in \operatorname{Chain}\left(H, A, B, L\right),\; \operatorname{R}\left(c\right) = \operatorname{factorProduct}\left(\operatorname{forwardFactors}\left(c\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/FactorPaths.R` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

R has size n by m and is the ordered product U0 through U(L-1). The empty chain gives the identity matrix.

**Definition 1.18 (The reverse cumulative rectangle).**

$$\forall H \in Type,\; [\operatorname{Group}\left(H\right)][\operatorname{Fintype}\left(H\right)]\forall n \in Nat, m \in Nat, L \in Nat, A \in \operatorname{GroupMat}\left(H, n, n\right), B \in \operatorname{GroupMat}\left(H, m, m\right), c \in \operatorname{Chain}\left(H, A, B, L\right),\; \operatorname{S}\left(c\right) = \operatorname{factorProduct}\left(\operatorname{backwardFactors}\left(c\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/FactorPaths.S` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

S has size m by n and is the ordered product V(L-1) through V0. The empty chain gives the identity matrix.

**Theorem 1.19 (The four equations for the same chain).**

$$\forall H \in Type,\; [\operatorname{Group}\left(H\right)][\operatorname{Fintype}\left(H\right)]\forall n \in Nat, m \in Nat, L \in Nat, A \in \operatorname{GroupMat}\left(H, n, n\right), B \in \operatorname{GroupMat}\left(H, m, m\right), c \in \operatorname{Chain}\left(H, A, B, L\right),\; (\operatorname{product}\left(A, \operatorname{R}\left(c\right)\right) = \operatorname{product}\left(\operatorname{R}\left(c\right), B\right)\land (\operatorname{product}\left(B, \operatorname{S}\left(c\right)\right) = \operatorname{product}\left(\operatorname{S}\left(c\right), A\right)\land (\operatorname{product}\left(\operatorname{R}\left(c\right), \operatorname{S}\left(c\right)\right) = \operatorname{power}\left(A, L\right)\land \operatorname{product}\left(\operatorname{S}\left(c\right), \operatorname{R}\left(c\right)\right) = \operatorname{power}\left(B, L\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/FactorPaths.cumulative_equations` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The two intertwining equations pass the source matrix through every factor using matrix associativity. For RS, induction gives U times the next matrix to the tail length times V; the rectangular exchange-power identity makes this A to the full length. For SR, the tail intertwining equation gives the terminal power. All four equations concern these same R and S. Length one reduces to the supplied U and V, and length zero reduces to the identity matrices.

**Definition 1.20 (The complete indexed source telescope).**

$$\forall H \in Type,\; [\operatorname{Group}\left(H\right)][\operatorname{Fintype}\left(H\right)]\forall L \in Nat,\; \operatorname{IndexedChain}\left(H, L\right):Type$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/FactorPaths.IndexedChain` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The indexed data have dimensions d(j) for j in Fin(L+1), matrices A(j) of size d(j) by d(j), U(j) of size d(j) by d(j+1), and V(j) of the opposite size for j in Fin L. They include both A(j)=U(j)V(j) and A(j+1)=V(j)U(j) for every layer. All original factors are supplied data.

**Definition 1.21 (The actual shifted indexed chain).**

$$\forall H \in Type,\; [\operatorname{Group}\left(H\right)][\operatorname{Fintype}\left(H\right)]\forall L \in Nat, c \in \operatorname{IndexedChain}\left(H, \operatorname{successor}\left(L\right)\right),\; \operatorname{tail}\left(c\right):\operatorname{IndexedChain}\left(H, L\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/FactorPaths.tail` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The tail replaces every layer j by j+1 in d, A, U and V and retains the corresponding original factor equalities.

**Definition 1.22 (Recursion retains the prescribed indexed data).**

$$\forall H \in Type,\; [\operatorname{Group}\left(H\right)][\operatorname{Fintype}\left(H\right)]\forall L \in Nat, c \in \operatorname{IndexedChain}\left(H, L\right),\; \operatorname{toChain}\left(c\right):\operatorname{Chain}\left(H, \operatorname{A}\left(c, 0\right), \operatorname{A}\left(c, \operatorname{last}\left(L\right)\right), L\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/FactorPaths.toChain` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

toChain starts with the actual U(0), V(0) and their two given equalities and then recurses on the indexed tail. Its source is A(0), its terminal matrix is A(L), and its length is L. It never selects another chain with the same endpoints.

**Definition 1.23 (Numbered edges at fixed endpoints).**

$$\forall H \in Type,\; [\operatorname{Group}\left(H\right)]\forall n \in Nat, m \in Nat, M \in \operatorname{GroupMat}\left(H, n, m\right), i \in \operatorname{Fin}\left(n\right), j \in \operatorname{Fin}\left(m\right),\; \operatorname{At}\left(M, i, j\right):\Sigma_{g:H}(\operatorname{Fin}\left(\operatorname{coeff}\left(\operatorname{entry}\left(M, i, j\right), g\right)\right))$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/FactorPaths.At` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

At M i j contains the group label g and the independent copy number c in Fin(coeff(M[i,j],g)). The endpoints are fixed by its type.

**Definition 1.24 (The prescribed theta and eta ranks).**

$$\forall H \in Type,\; [\operatorname{Group}\left(H\right)][\operatorname{Fintype}\left(H\right)][\operatorname{LinearOrder}\left(H\right)]\forall n \in Nat, k \in Nat, U \in \operatorname{GroupMat}\left(H, n, k\right), V \in \operatorname{GroupMat}\left(H, k, n\right), i \in \operatorname{Fin}\left(n\right), j \in \operatorname{Fin}\left(n\right),\; \operatorname{orderedAtEquiv}\left(U, V, i, j\right):\operatorname{Equiv}\left(\operatorname{At}\left(\operatorname{product}\left(U, V\right), i, j\right), \Sigma_{v:\operatorname{Fin}\left(k\right)}((\operatorname{At}\left(U, i, v\right)\times\operatorname{At}\left(V, v, j\right)))\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/FactorPaths.orderedAtEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The map uses orderedFiberEquiv with exactly the prescribed order: middle vertex, first group label, first copy, second copy. The second label is first-label inverse times total label. The inverse multiplies the labels in this order and returns the rank in the same local fiber. Empty fibers require no representative.

**Definition 1.25 (Repeated actual square matrix).**

$$\forall H \in Type,\; [\operatorname{Group}\left(H\right)]\forall n \in Nat, A \in \operatorname{GroupMat}\left(H, n, n\right), l \in Nat,\; \operatorname{wordFactors}\left(A, l\right):\operatorname{Factors}\left(H, n, n, l\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/FactorPaths.wordFactors` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

wordFactors A l stores l copies of the actual A matrix. Length zero is the nil factor sequence, and each successor prepends A.

**Definition 1.26 (Finite actual A words).**

$$\forall H \in Type,\; [\operatorname{Group}\left(H\right)]\forall n \in Nat, A \in \operatorname{GroupMat}\left(H, n, n\right), l \in Nat, i \in \operatorname{Fin}\left(n\right), j \in \operatorname{Fin}\left(n\right),\; \operatorname{Word}\left(A, l, i, j\right) = \operatorname{FactorPath}\left(\operatorname{wordFactors}\left(A, l\right), i, j\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/FactorPaths.Word` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Words retain their endpoints and every ordered label and copy number. A zero-edge word retains its specified vertex.

**Definition 1.27 (Read and restore the first factor edge).**

$$\forall H \in Type,\; [\operatorname{Group}\left(H\right)]\forall n \in Nat, k \in Nat, m \in Nat, L \in Nat, M \in \operatorname{GroupMat}\left(H, n, k\right), f \in \operatorname{Factors}\left(H, k, m, L\right), i \in \operatorname{Fin}\left(n\right), j \in \operatorname{Fin}\left(m\right),\; \operatorname{pathHeadEquiv}\left(M, f, i, j\right):\operatorname{Equiv}\left(\operatorname{FactorPath}\left(\operatorname{cons}\left(M, f\right), i, j\right), \Sigma_{v:\operatorname{Fin}\left(k\right)}((\operatorname{At}\left(M, i, v\right)\times\operatorname{FactorPath}\left(f, v, j\right)))\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/FactorPaths.pathHeadEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The first numbered edge and the complete tail are unpacked and repacked without changing their data. The two composites are identities.

**Definition 1.28 (Read an edge followed by its named nil).**

$$\forall H \in Type,\; [\operatorname{Group}\left(H\right)]\forall n \in Nat, m \in Nat, M \in \operatorname{GroupMat}\left(H, n, m\right), i \in \operatorname{Fin}\left(n\right), j \in \operatorname{Fin}\left(m\right),\; \operatorname{rightNilEquiv}\left(M, i, j\right):\operatorname{Equiv}\left(\Sigma_{v:\operatorname{Fin}\left(m\right)}((\operatorname{At}\left(M, i, v\right)\times\operatorname{FactorPath}\left(\operatorname{nil}\left(H, m\right), v, j\right))), \operatorname{At}\left(M, i, j\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/FactorPaths.rightNilEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The nil endpoint equalities identify v with j. The inverse appends the actual nilPath j, and both composites recover the edge and named vertex.

**Definition 1.29 (Split off the last actual numbered edge).**

$$\forall H \in Type,\; [\operatorname{Group}\left(H\right)]\forall n \in Nat, k \in Nat, m \in Nat, L \in Nat, f \in \operatorname{Factors}\left(H, n, k, L\right), M \in \operatorname{GroupMat}\left(H, k, m\right), i \in \operatorname{Fin}\left(n\right), j \in \operatorname{Fin}\left(m\right),\; \operatorname{pathSnocEquiv}\left(f, M, i, j\right):\operatorname{Equiv}\left(\operatorname{FactorPath}\left(\operatorname{factorSnoc}\left(f, M\right), i, j\right), \Sigma_{v:\operatorname{Fin}\left(k\right)}((\operatorname{FactorPath}\left(f, i, v\right)\times\operatorname{At}\left(M, v, j\right)))\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/FactorPaths.pathSnocEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Structural recursion separates the final actual edge from the entire preceding path. Its inverse appends that same edge. It preserves all preceding copies, the last copy, the outside endpoints and the ordered product.

**Definition 1.30 (The actual increasing and decreasing factor paths).**

$$\forall H \in Type,\; [\operatorname{Group}\left(H\right)][\operatorname{Fintype}\left(H\right)]\forall n \in Nat, m \in Nat, L \in Nat, A \in \operatorname{GroupMat}\left(H, n, n\right), B \in \operatorname{GroupMat}\left(H, m, m\right), c \in \operatorname{Chain}\left(H, A, B, L\right), i \in \operatorname{Fin}\left(n\right), j \in \operatorname{Fin}\left(n\right),\; \operatorname{ChainBoundary}\left(c, i, j\right) = \Sigma_{v:\operatorname{Fin}\left(m\right)}((\operatorname{FactorPath}\left(\operatorname{forwardFactors}\left(c\right), i, v\right)\times\operatorname{FactorPath}\left(\operatorname{backwardFactors}\left(c\right), v, j\right)))$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/FactorPaths.ChainBoundary` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The sigma vertex is the common middle endpoint. The first path is the increasing U sequence and the second path is the decreasing V sequence of the same supplied chain.

**Definition 1.31 (The source triangle).**

$$\forall H \in Type,\; [\operatorname{Group}\left(H\right)][\operatorname{Fintype}\left(H\right)][\operatorname{LinearOrder}\left(H\right)]\forall n \in Nat, m \in Nat, L \in Nat, A \in \operatorname{GroupMat}\left(H, n, n\right), B \in \operatorname{GroupMat}\left(H, m, m\right), c \in \operatorname{Chain}\left(H, A, B, L\right), i \in \operatorname{Fin}\left(n\right), j \in \operatorname{Fin}\left(n\right),\; \operatorname{psi0}\left(c, i, j\right):\operatorname{Equiv}\left(\Sigma_{v:\operatorname{Fin}\left(m\right)}((\operatorname{FactorPath}\left(\operatorname{forwardFactors}\left(c\right), i, v\right)\times\operatorname{FactorPath}\left(\operatorname{backwardFactors}\left(c\right), v, j\right))), \operatorname{Word}\left(A, L, i, j\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/FactorPaths.psi0` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The inverse peels each theta row, saves its first U edge and last V edge, and joins internal adjacent VU pairs by eta. Its forward algorithm reverses these operations from the named nil word. Both composites are identities on all typed inputs, including length zero and empty coefficient fibers. No dimension is required to be positive.

**Definition 1.32 (The terminal triangle).**

$$\forall H \in Type,\; [\operatorname{Group}\left(H\right)][\operatorname{Fintype}\left(H\right)][\operatorname{LinearOrder}\left(H\right)]\forall n \in Nat, m \in Nat, L \in Nat, A \in \operatorname{GroupMat}\left(H, n, n\right), B \in \operatorname{GroupMat}\left(H, m, m\right), c \in \operatorname{Chain}\left(H, A, B, L\right), i \in \operatorname{Fin}\left(m\right), j \in \operatorname{Fin}\left(m\right),\; \operatorname{psiL}\left(c, i, j\right):\operatorname{Equiv}\left(\Sigma_{v:\operatorname{Fin}\left(n\right)}((\operatorname{FactorPath}\left(\operatorname{backwardFactors}\left(c\right), i, v\right)\times\operatorname{FactorPath}\left(\operatorname{forwardFactors}\left(c\right), v, j\right))), \operatorname{Word}\left(B, L, i, j\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/FactorPaths.psiL` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The actual reversed chain exchanges U and V and reverses the layer order. Applying the source triangle to it defines the terminal triangle, using eta to split and theta to rejoin. Both composites are identities on all typed inputs, including length zero and empty coefficient fibers. No dimension is required to be positive.

**Definition 1.33 (The source triangle on matrix edges).**

$$\forall H \in Type,\; [\operatorname{Group}\left(H\right)][\operatorname{Fintype}\left(H\right)][\operatorname{LinearOrder}\left(H\right)]\forall n \in Nat, m \in Nat, L \in Nat, A \in \operatorname{GroupMat}\left(H, n, n\right), B \in \operatorname{GroupMat}\left(H, m, m\right), c \in \operatorname{Chain}\left(H, A, B, L\right), i \in \operatorname{Fin}\left(n\right), j \in \operatorname{Fin}\left(n\right),\; \operatorname{matrixPsi0}\left(c, i, j\right):\operatorname{Equiv}\left(\Sigma_{v:\operatorname{Fin}\left(m\right)}((\operatorname{At}\left(\operatorname{R}\left(c\right), i, v\right)\times\operatorname{At}\left(\operatorname{S}\left(c\right), v, j\right))), \operatorname{Word}\left(A, L, i, j\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/FactorPaths.matrixPsi0` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every R and S occurrence is transported by pathAtEquiv using the single increasing whole-factor fiber rank. The inverse peels each theta row, saves its first U edge and last V edge, and joins internal adjacent VU pairs by eta. Its forward algorithm reverses these operations from the named nil word. Both composites are identities on all typed inputs, including length zero and empty coefficient fibers. No dimension is required to be positive.

**Definition 1.34 (The terminal triangle on matrix edges).**

$$\forall H \in Type,\; [\operatorname{Group}\left(H\right)][\operatorname{Fintype}\left(H\right)][\operatorname{LinearOrder}\left(H\right)]\forall n \in Nat, m \in Nat, L \in Nat, A \in \operatorname{GroupMat}\left(H, n, n\right), B \in \operatorname{GroupMat}\left(H, m, m\right), c \in \operatorname{Chain}\left(H, A, B, L\right), i \in \operatorname{Fin}\left(m\right), j \in \operatorname{Fin}\left(m\right),\; \operatorname{matrixPsiL}\left(c, i, j\right):\operatorname{Equiv}\left(\Sigma_{v:\operatorname{Fin}\left(n\right)}((\operatorname{At}\left(\operatorname{S}\left(c\right), i, v\right)\times\operatorname{At}\left(\operatorname{R}\left(c\right), v, j\right))), \operatorname{Word}\left(B, L, i, j\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/FactorPaths.matrixPsiL` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every R and S occurrence is transported by pathAtEquiv using the single increasing whole-factor fiber rank. The actual reversed chain exchanges U and V and reverses the layer order. Applying the source triangle to it defines the terminal triangle, using eta to split and theta to rejoin. Both composites are identities on all typed inputs, including length zero and empty coefficient fibers. No dimension is required to be positive.

**Definition 1.35 (The phiR actual sweep).**

$$\forall H \in Type,\; [\operatorname{Group}\left(H\right)][\operatorname{Fintype}\left(H\right)][\operatorname{LinearOrder}\left(H\right)]\forall n \in Nat, m \in Nat, L \in Nat, A \in \operatorname{GroupMat}\left(H, n, n\right), B \in \operatorname{GroupMat}\left(H, m, m\right), c \in \operatorname{Chain}\left(H, A, B, L\right), i \in \operatorname{Fin}\left(n\right), j \in \operatorname{Fin}\left(m\right),\; \operatorname{phiR}\left(c, i, j\right):\operatorname{Equiv}\left(\Sigma_{x:\operatorname{Fin}\left(n\right)}((\operatorname{At}\left(A, i, x\right)\times\operatorname{FactorPath}\left(\operatorname{forwardFactors}\left(c\right), x, j\right))), \Sigma_{y:\operatorname{Fin}\left(m\right)}((\operatorname{FactorPath}\left(\operatorname{forwardFactors}\left(c\right), i, y\right)\times\operatorname{At}\left(B, y, j\right)))\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/FactorPaths.phiR` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The sweep splits theta, saves the U edge, joins eta with the incoming U edge and continues through the original layers. The inverse visits these same cells in reverse order. Both composites are identities; every endpoint and independent copy number is recovered.

**Definition 1.36 (The phiS actual sweep).**

$$\forall H \in Type,\; [\operatorname{Group}\left(H\right)][\operatorname{Fintype}\left(H\right)][\operatorname{LinearOrder}\left(H\right)]\forall n \in Nat, m \in Nat, L \in Nat, A \in \operatorname{GroupMat}\left(H, n, n\right), B \in \operatorname{GroupMat}\left(H, m, m\right), c \in \operatorname{Chain}\left(H, A, B, L\right), i \in \operatorname{Fin}\left(m\right), j \in \operatorname{Fin}\left(n\right),\; \operatorname{phiS}\left(c, i, j\right):\operatorname{Equiv}\left(\Sigma_{x:\operatorname{Fin}\left(m\right)}((\operatorname{At}\left(B, i, x\right)\times\operatorname{FactorPath}\left(\operatorname{backwardFactors}\left(c\right), x, j\right))), \Sigma_{y:\operatorname{Fin}\left(n\right)}((\operatorname{FactorPath}\left(\operatorname{backwardFactors}\left(c\right), i, y\right)\times\operatorname{At}\left(A, y, j\right)))\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/FactorPaths.phiS` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The sweep uses the actual reversed chain and its decreasing original V factors. The inverse visits these same cells in reverse order. Both composites are identities; every endpoint and independent copy number is recovered.

**Definition 1.37 (The matrixPhiR actual sweep).**

$$\forall H \in Type,\; [\operatorname{Group}\left(H\right)][\operatorname{Fintype}\left(H\right)][\operatorname{LinearOrder}\left(H\right)]\forall n \in Nat, m \in Nat, L \in Nat, A \in \operatorname{GroupMat}\left(H, n, n\right), B \in \operatorname{GroupMat}\left(H, m, m\right), c \in \operatorname{Chain}\left(H, A, B, L\right), i \in \operatorname{Fin}\left(n\right), j \in \operatorname{Fin}\left(m\right),\; \operatorname{matrixPhiR}\left(c, i, j\right):\operatorname{Equiv}\left(\Sigma_{x:\operatorname{Fin}\left(n\right)}((\operatorname{At}\left(A, i, x\right)\times\operatorname{At}\left(\operatorname{R}\left(c\right), x, j\right))), \Sigma_{y:\operatorname{Fin}\left(m\right)}((\operatorname{At}\left(\operatorname{R}\left(c\right), i, y\right)\times\operatorname{At}\left(B, y, j\right)))\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/FactorPaths.matrixPhiR` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Both occurrences of the cumulative matrix edge use the same whole-factor rank. The sweep splits theta, saves the U edge, joins eta with the incoming U edge and continues through the original layers. The inverse visits these same cells in reverse order. Both composites are identities; every endpoint and independent copy number is recovered.

**Definition 1.38 (The matrixPhiS actual sweep).**

$$\forall H \in Type,\; [\operatorname{Group}\left(H\right)][\operatorname{Fintype}\left(H\right)][\operatorname{LinearOrder}\left(H\right)]\forall n \in Nat, m \in Nat, L \in Nat, A \in \operatorname{GroupMat}\left(H, n, n\right), B \in \operatorname{GroupMat}\left(H, m, m\right), c \in \operatorname{Chain}\left(H, A, B, L\right), i \in \operatorname{Fin}\left(m\right), j \in \operatorname{Fin}\left(n\right),\; \operatorname{matrixPhiS}\left(c, i, j\right):\operatorname{Equiv}\left(\Sigma_{x:\operatorname{Fin}\left(m\right)}((\operatorname{At}\left(B, i, x\right)\times\operatorname{At}\left(\operatorname{S}\left(c\right), x, j\right))), \Sigma_{y:\operatorname{Fin}\left(n\right)}((\operatorname{At}\left(\operatorname{S}\left(c\right), i, y\right)\times\operatorname{At}\left(A, y, j\right)))\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/FactorPaths.matrixPhiS` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Both occurrences of the cumulative matrix edge use the same whole-factor rank. The sweep uses the actual reversed chain and its decreasing original V factors. The inverse visits these same cells in reverse order. Both composites are identities; every endpoint and independent copy number is recovered.

**Definition 1.39 (The phiRPower actual sweep).**

$$\forall H \in Type,\; [\operatorname{Group}\left(H\right)][\operatorname{Fintype}\left(H\right)][\operatorname{LinearOrder}\left(H\right)]\forall n \in Nat, m \in Nat, L \in Nat, A \in \operatorname{GroupMat}\left(H, n, n\right), B \in \operatorname{GroupMat}\left(H, m, m\right), c \in \operatorname{Chain}\left(H, A, B, L\right), l \in Nat, i \in \operatorname{Fin}\left(n\right), j \in \operatorname{Fin}\left(m\right),\; \operatorname{phiRPower}\left(c, l, i, j\right):\operatorname{Equiv}\left(\Sigma_{x:\operatorname{Fin}\left(n\right)}((\operatorname{Word}\left(A, l, i, x\right)\times\operatorname{FactorPath}\left(\operatorname{forwardFactors}\left(c\right), x, j\right))), \Sigma_{y:\operatorname{Fin}\left(m\right)}((\operatorname{FactorPath}\left(\operatorname{forwardFactors}\left(c\right), i, y\right)\times\operatorname{Word}\left(B, l, y, j\right)))\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/FactorPaths.phiRPower` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each finite word is processed from its rightmost column to its leftmost column. The sweep splits theta, saves the U edge, joins eta with the incoming U edge and continues through the original layers. The inverse visits these same cells in reverse order. Both composites are identities; every endpoint and independent copy number is recovered.

**Definition 1.40 (The phiSPower actual sweep).**

$$\forall H \in Type,\; [\operatorname{Group}\left(H\right)][\operatorname{Fintype}\left(H\right)][\operatorname{LinearOrder}\left(H\right)]\forall n \in Nat, m \in Nat, L \in Nat, A \in \operatorname{GroupMat}\left(H, n, n\right), B \in \operatorname{GroupMat}\left(H, m, m\right), c \in \operatorname{Chain}\left(H, A, B, L\right), l \in Nat, i \in \operatorname{Fin}\left(m\right), j \in \operatorname{Fin}\left(n\right),\; \operatorname{phiSPower}\left(c, l, i, j\right):\operatorname{Equiv}\left(\Sigma_{x:\operatorname{Fin}\left(m\right)}((\operatorname{Word}\left(B, l, i, x\right)\times\operatorname{FactorPath}\left(\operatorname{backwardFactors}\left(c\right), x, j\right))), \Sigma_{y:\operatorname{Fin}\left(n\right)}((\operatorname{FactorPath}\left(\operatorname{backwardFactors}\left(c\right), i, y\right)\times\operatorname{Word}\left(A, l, y, j\right)))\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/FactorPaths.phiSPower` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each finite word is processed from its rightmost column to its leftmost column. The sweep uses the actual reversed chain and its decreasing original V factors. The inverse visits these same cells in reverse order. Both composites are identities; every endpoint and independent copy number is recovered.

**Definition 1.41 (The actual chain in decreasing layer order).**

$$\forall H \in Type,\; [\operatorname{Group}\left(H\right)][\operatorname{Fintype}\left(H\right)]\forall n \in Nat, m \in Nat, L \in Nat, A \in \operatorname{GroupMat}\left(H, n, n\right), B \in \operatorname{GroupMat}\left(H, m, m\right), c \in \operatorname{Chain}\left(H, A, B, L\right),\; \operatorname{reverseChain}\left(c\right):\operatorname{Chain}\left(H, B, A, L\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/FactorPaths.reverseChain` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The reversed chain retains each original matrix and factor equality, exchanging U and V and visiting the original layers in decreasing order. Its forward factors are precisely the original backward factors, and its backward factors are precisely the original forward factors.

**Definition 1.42 (Append the prescribed final SSE step).**

$$\forall H \in Type,\; [\operatorname{Group}\left(H\right)][\operatorname{Fintype}\left(H\right)]\forall n \in Nat, k \in Nat, m \in Nat, L \in Nat, A \in \operatorname{GroupMat}\left(H, n, n\right), B \in \operatorname{GroupMat}\left(H, k, k\right), C \in \operatorname{GroupMat}\left(H, m, m\right), c \in \operatorname{Chain}\left(H, A, B, L\right), U \in \operatorname{GroupMat}\left(H, k, m\right), V \in \operatorname{GroupMat}\left(H, m, k\right), hB \in B = \operatorname{product}\left(U, V\right), hC \in C = \operatorname{product}\left(V, U\right),\; \operatorname{chainSnoc}\left(c, U, V, hB, hC\right):\operatorname{Chain}\left(H, A, C, \operatorname{successor}\left(L\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/FactorPaths.chainSnoc` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The operation appends this actual final step after the retained chain. Its U sequence appends U; its decreasing V sequence prepends V.

**Definition 1.43 (The single whole-factor rank at fixed endpoints).**

$$\forall H \in Type,\; [\operatorname{Group}\left(H\right)][\operatorname{Fintype}\left(H\right)][\operatorname{LinearOrder}\left(H\right)]\forall n \in Nat, m \in Nat, L \in Nat, f \in \operatorname{Factors}\left(H, n, m, L\right), i \in \operatorname{Fin}\left(n\right), j \in \operatorname{Fin}\left(m\right),\; \operatorname{pathAtEquiv}\left(f, i, j\right):\operatorname{Equiv}\left(\operatorname{At}\left(\operatorname{factorProduct}\left(f\right), i, j\right), \operatorname{FactorPath}\left(f, i, j\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/FactorPaths.pathAtEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The map reads the label and global rank of a cumulative matrix edge and returns the actual complete factor path in that fiber. Its inverse reads the same fiber rank. All original factor copies, endpoints and the ordered total label are recovered.

**Definition 1.44 (The saved U edge, internal VU word and saved V edge).**

$$\forall H \in Type,\; [\operatorname{Group}\left(H\right)]\forall n \in Nat, k \in Nat, U \in \operatorname{GroupMat}\left(H, n, k\right), V \in \operatorname{GroupMat}\left(H, k, n\right), l \in Nat, i \in \operatorname{Fin}\left(n\right), j \in \operatorname{Fin}\left(n\right),\; \operatorname{PeelBoundary}\left(U, V, l, i, j\right) = \Sigma_{x:\operatorname{Fin}\left(k\right)}(\Sigma_{y:\operatorname{Fin}\left(k\right)}((\operatorname{At}\left(U, i, x\right)\times(\operatorname{Word}\left(\operatorname{product}\left(V, U\right), l, x, y\right)\times\operatorname{At}\left(V, y, j\right)))))$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/FactorPaths.PeelBoundary` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The outside half-edges are retained individually. The internal word has length l, so the original word has length l+1. All middle endpoints are typed and retained.

**Definition 1.45 (One triangular peeling layer).**

$$\forall H \in Type,\; [\operatorname{Group}\left(H\right)][\operatorname{Fintype}\left(H\right)][\operatorname{LinearOrder}\left(H\right)]\forall n \in Nat, k \in Nat, U \in \operatorname{GroupMat}\left(H, n, k\right), V \in \operatorname{GroupMat}\left(H, k, n\right), l \in Nat, i \in \operatorname{Fin}\left(n\right), j \in \operatorname{Fin}\left(n\right),\; \operatorname{peelRow}\left(U, V, l, i, j\right):\operatorname{Equiv}\left(\operatorname{Word}\left(\operatorname{product}\left(U, V\right), \operatorname{successor}\left(l\right), i, j\right), \Sigma_{x:\operatorname{Fin}\left(k\right)}(\Sigma_{y:\operatorname{Fin}\left(k\right)}((\operatorname{At}\left(U, i, x\right)\times(\operatorname{Word}\left(\operatorname{product}\left(V, U\right), l, x, y\right)\times\operatorname{At}\left(V, y, j\right)))))\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/FactorPaths.peelRow` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Split every theta edge, save the leftmost U and rightmost V, and join adjacent internal VU pairs using eta. The inverse splits those eta edges, restores the saved edges, and joins the theta pairs. Both composites recover every label and independent copy number.

**Definition 1.46 (The actual local theta-eta cell).**

$$\forall H \in Type,\; [\operatorname{Group}\left(H\right)][\operatorname{Fintype}\left(H\right)][\operatorname{LinearOrder}\left(H\right)]\forall n \in Nat, k \in Nat, U \in \operatorname{GroupMat}\left(H, n, k\right), V \in \operatorname{GroupMat}\left(H, k, n\right), i \in \operatorname{Fin}\left(n\right), j \in \operatorname{Fin}\left(k\right),\; \operatorname{localSweep}\left(U, V, i, j\right):\operatorname{Equiv}\left(\Sigma_{x:\operatorname{Fin}\left(n\right)}((\operatorname{At}\left(\operatorname{product}\left(U, V\right), i, x\right)\times\operatorname{At}\left(U, x, j\right))), \Sigma_{y:\operatorname{Fin}\left(k\right)}((\operatorname{At}\left(U, i, y\right)\times\operatorname{At}\left(\operatorname{product}\left(V, U\right), y, j\right)))\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/FactorPaths.localSweep` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Split the actual theta rank into u,v and return u together with eta(v,u-prime). The inverse splits eta and rejoins theta. All three half-edge labels occur in the same order.

**Theorem 1.47 (Forward factors of an appended actual step).**

$$\forall H \in Type,\; [\operatorname{Group}\left(H\right)][\operatorname{Fintype}\left(H\right)]\forall n \in Nat, k \in Nat, m \in Nat, L \in Nat, A \in \operatorname{GroupMat}\left(H, n, n\right), B \in \operatorname{GroupMat}\left(H, k, k\right), C \in \operatorname{GroupMat}\left(H, m, m\right), c \in \operatorname{Chain}\left(H, A, B, L\right), U \in \operatorname{GroupMat}\left(H, k, m\right), V \in \operatorname{GroupMat}\left(H, m, k\right), hB \in B = U \cdot V, hC \in C = V \cdot U,\; \operatorname{forwardFactors}\left(\operatorname{chainSnoc}\left(c, U, V, hB, hC\right)\right) = \operatorname{factorSnoc}\left(\operatorname{forwardFactors}\left(c\right), U\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/FactorPaths.forward_snoc` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the supplied equalities B=UV and C=VU, appending the step retains the increasing factors of c and then U. Dimensions n,k,m and the full original length L are quantified.

**Theorem 1.48 (Backward factors of an appended actual step).**

$$\forall H \in Type,\; [\operatorname{Group}\left(H\right)][\operatorname{Fintype}\left(H\right)]\forall n \in Nat, k \in Nat, m \in Nat, L \in Nat, A \in \operatorname{GroupMat}\left(H, n, n\right), B \in \operatorname{GroupMat}\left(H, k, k\right), C \in \operatorname{GroupMat}\left(H, m, m\right), c \in \operatorname{Chain}\left(H, A, B, L\right), U \in \operatorname{GroupMat}\left(H, k, m\right), V \in \operatorname{GroupMat}\left(H, m, k\right), hB \in B = U \cdot V, hC \in C = V \cdot U,\; \operatorname{backwardFactors}\left(\operatorname{chainSnoc}\left(c, U, V, hB, hC\right)\right) = \operatorname{FactorsCons}\left(V, \operatorname{backwardFactors}\left(c\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/FactorPaths.backward_snoc` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The decreasing backward factor list begins with the appended V, followed by every backward factor of c. The same supplied B=UV,C=VU equalities are retained.

**Theorem 1.49 (Reversal exchanges the complete forward factor list).**

$$\forall H \in Type,\; [\operatorname{Group}\left(H\right)][\operatorname{Fintype}\left(H\right)]\forall n \in Nat, m \in Nat, L \in Nat, A \in \operatorname{GroupMat}\left(H, n, n\right), B \in \operatorname{GroupMat}\left(H, m, m\right), c \in \operatorname{Chain}\left(H, A, B, L\right),\; \operatorname{forwardFactors}\left(\operatorname{reverseChain}\left(c\right)\right) = \operatorname{backwardFactors}\left(c\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/FactorPaths.reverse_forward` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every actual chain c, the increasing factors of its reversal are exactly the decreasing original backward factors, including the named nil chain.

**Theorem 1.50 (Reversal exchanges the complete backward factor list).**

$$\forall H \in Type,\; [\operatorname{Group}\left(H\right)][\operatorname{Fintype}\left(H\right)]\forall n \in Nat, m \in Nat, L \in Nat, A \in \operatorname{GroupMat}\left(H, n, n\right), B \in \operatorname{GroupMat}\left(H, m, m\right), c \in \operatorname{Chain}\left(H, A, B, L\right),\; \operatorname{backwardFactors}\left(\operatorname{reverseChain}\left(c\right)\right) = \operatorname{forwardFactors}\left(c\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/FactorPaths.reverse_backward` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every actual chain c, the decreasing factors of its reversal are exactly the increasing original forward factors.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/FactorPaths.At`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/FactorPaths.Chain`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/FactorPaths.ChainBoundary`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/FactorPaths.FactorFiber`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/FactorPaths.FactorPath`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/FactorPaths.Factors`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/FactorPaths.IndexedChain`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/FactorPaths.PeelBoundary`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/FactorPaths.R`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/FactorPaths.S`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/FactorPaths.Word`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/FactorPaths.backwardFactors`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/FactorPaths.backward_snoc`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/FactorPaths.chainSnoc`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/FactorPaths.consPath`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/FactorPaths.cumulative_equations`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/FactorPaths.edgePathEquiv`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/FactorPaths.factorLabel`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/FactorPaths.factorProduct`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/FactorPaths.factorSnoc`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/FactorPaths.fiberConsEquiv`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/FactorPaths.fiber_card`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/FactorPaths.forwardFactors`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/FactorPaths.forward_snoc`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/FactorPaths.localSweep`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/FactorPaths.matrixPhiR`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/FactorPaths.matrixPhiS`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/FactorPaths.matrixPsi0`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/FactorPaths.matrixPsiL`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/FactorPaths.nilPath`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/FactorPaths.orderedAtEquiv`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/FactorPaths.pathAtEquiv`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/FactorPaths.pathHeadEquiv`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/FactorPaths.pathSnocEquiv`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/FactorPaths.peelRow`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/FactorPaths.phiR`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/FactorPaths.phiRPower`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/FactorPaths.phiS`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/FactorPaths.phiSPower`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/FactorPaths.psi0`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/FactorPaths.psiL`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/FactorPaths.rankedFiberEquiv`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/FactorPaths.rankedFiberOrderIso`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/FactorPaths.reverseChain`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/FactorPaths.reverse_backward`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/FactorPaths.reverse_forward`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/FactorPaths.rightNilEquiv`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/FactorPaths.tail`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/FactorPaths.toChain`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/FactorPaths.wordFactors`
- Dependency: [D5/S3/ConceptDynamics/Coding/CountedGroupOverlap](../CountedGroupOverlap.md)
