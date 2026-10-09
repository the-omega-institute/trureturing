# Prescribed finite arrays and ordered labels

## Abstract

Prescribed finite arrays and ordered labels. All numbered edges, ordered labels and source conditions are retained.

**Definition 1.1 (The rowFirst actual sweep).**

$$\forall H \in Type,\; [\operatorname{Group}\left(H\right)][\operatorname{Fintype}\left(H\right)][\operatorname{LinearOrder}\left(H\right)]\forall n \in Nat, m \in Nat, L \in Nat, A \in \operatorname{GroupMat}\left(H, n, n\right), B \in \operatorname{GroupMat}\left(H, m, m\right), c \in \operatorname{Chain}\left(H, A, B, L\right), l \in Nat, i \in \operatorname{Fin}\left(n\right), j \in \operatorname{Fin}\left(m\right),\; \operatorname{rowFirst}\left(c, l, i, j\right):\operatorname{Equiv}\left(\Sigma_{x:\operatorname{Fin}\left(n\right)}((\operatorname{Word}\left(A, l, i, x\right)\times\operatorname{FactorPath}\left(\operatorname{forwardFactors}\left(c\right), x, j\right))), \Sigma_{y:\operatorname{Fin}\left(m\right)}((\operatorname{FactorPath}\left(\operatorname{forwardFactors}\left(c\right), i, y\right)\times\operatorname{Word}\left(B, l, y, j\right)))\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/PrescribedArrays.rowFirst` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The same local transformations are evaluated one complete layer row at a time, always using the given factor path at the right boundary. The inverse visits these same cells in reverse order. Both composites are identities; every endpoint and independent copy number is recovered.

**Theorem 1.2 (Ordered total-label preservation).**

$$\forall H \in Type,\; [\operatorname{Group}\left(H\right)][\operatorname{Fintype}\left(H\right)][\operatorname{LinearOrder}\left(H\right)]\forall n \in Nat, m \in Nat, L \in Nat, A \in \operatorname{GroupMat}\left(H, n, n\right), B \in \operatorname{GroupMat}\left(H, m, m\right), c \in \operatorname{Chain}\left(H, A, B, L\right), i \in \operatorname{Fin}\left(n\right), j \in \operatorname{Fin}\left(n\right), p \in \Sigma_{v:\operatorname{Fin}\left(m\right)}((\operatorname{FactorPath}\left(\operatorname{forwardFactors}\left(c\right), i, v\right)\times\operatorname{FactorPath}\left(\operatorname{backwardFactors}\left(c\right), v, j\right))),\; \operatorname{factorLabel}\left(\operatorname{wordFactors}\left(A, L\right), \operatorname{apply}\left(\operatorname{psi0}\left(c, i, j\right), p\right)\right) = \operatorname{factorLabel}\left(\operatorname{forwardFactors}\left(c\right), \operatorname{first}\left(p\right)\right) \cdot \operatorname{factorLabel}\left(\operatorname{backwardFactors}\left(c\right), \operatorname{second}\left(p\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/PrescribedArrays.psi0_label` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The sigma vertex is omitted by first and second, which denote the two composable components. Labels multiply in traversal order. The equality uses associativity and inverse cancellation in an arbitrary group; it does not exchange group elements.

**Theorem 1.3 (Ordered total-label preservation).**

$$\forall H \in Type,\; [\operatorname{Group}\left(H\right)][\operatorname{Fintype}\left(H\right)][\operatorname{LinearOrder}\left(H\right)]\forall n \in Nat, m \in Nat, L \in Nat, A \in \operatorname{GroupMat}\left(H, n, n\right), B \in \operatorname{GroupMat}\left(H, m, m\right), c \in \operatorname{Chain}\left(H, A, B, L\right), i \in \operatorname{Fin}\left(m\right), j \in \operatorname{Fin}\left(m\right), p \in \Sigma_{v:\operatorname{Fin}\left(n\right)}((\operatorname{FactorPath}\left(\operatorname{backwardFactors}\left(c\right), i, v\right)\times\operatorname{FactorPath}\left(\operatorname{forwardFactors}\left(c\right), v, j\right))),\; \operatorname{factorLabel}\left(\operatorname{wordFactors}\left(B, L\right), \operatorname{apply}\left(\operatorname{psiL}\left(c, i, j\right), p\right)\right) = \operatorname{factorLabel}\left(\operatorname{backwardFactors}\left(c\right), \operatorname{first}\left(p\right)\right) \cdot \operatorname{factorLabel}\left(\operatorname{forwardFactors}\left(c\right), \operatorname{second}\left(p\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/PrescribedArrays.psiL_label` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The sigma vertex is omitted by first and second, which denote the two composable components. Labels multiply in traversal order. The equality uses associativity and inverse cancellation in an arbitrary group; it does not exchange group elements.

**Theorem 1.4 (Ordered total-label preservation).**

$$\forall H \in Type,\; [\operatorname{Group}\left(H\right)][\operatorname{Fintype}\left(H\right)][\operatorname{LinearOrder}\left(H\right)]\forall n \in Nat, m \in Nat, L \in Nat, A \in \operatorname{GroupMat}\left(H, n, n\right), B \in \operatorname{GroupMat}\left(H, m, m\right), c \in \operatorname{Chain}\left(H, A, B, L\right), i \in \operatorname{Fin}\left(n\right), j \in \operatorname{Fin}\left(n\right), p \in \Sigma_{v:\operatorname{Fin}\left(m\right)}((\operatorname{At}\left(\operatorname{R}\left(c\right), i, v\right)\times\operatorname{At}\left(\operatorname{S}\left(c\right), v, j\right))),\; \operatorname{factorLabel}\left(\operatorname{wordFactors}\left(A, L\right), \operatorname{apply}\left(\operatorname{matrixPsi0}\left(c, i, j\right), p\right)\right) = \operatorname{label}\left(\operatorname{first}\left(p\right)\right) \cdot \operatorname{label}\left(\operatorname{second}\left(p\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/PrescribedArrays.matrixPsi0_label` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The sigma vertex is omitted by first and second, which denote the two composable components. Labels multiply in traversal order. The equality uses associativity and inverse cancellation in an arbitrary group; it does not exchange group elements.

**Theorem 1.5 (Ordered total-label preservation).**

$$\forall H \in Type,\; [\operatorname{Group}\left(H\right)][\operatorname{Fintype}\left(H\right)][\operatorname{LinearOrder}\left(H\right)]\forall n \in Nat, m \in Nat, L \in Nat, A \in \operatorname{GroupMat}\left(H, n, n\right), B \in \operatorname{GroupMat}\left(H, m, m\right), c \in \operatorname{Chain}\left(H, A, B, L\right), i \in \operatorname{Fin}\left(m\right), j \in \operatorname{Fin}\left(m\right), p \in \Sigma_{v:\operatorname{Fin}\left(n\right)}((\operatorname{At}\left(\operatorname{S}\left(c\right), i, v\right)\times\operatorname{At}\left(\operatorname{R}\left(c\right), v, j\right))),\; \operatorname{factorLabel}\left(\operatorname{wordFactors}\left(B, L\right), \operatorname{apply}\left(\operatorname{matrixPsiL}\left(c, i, j\right), p\right)\right) = \operatorname{label}\left(\operatorname{first}\left(p\right)\right) \cdot \operatorname{label}\left(\operatorname{second}\left(p\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/PrescribedArrays.matrixPsiL_label` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The sigma vertex is omitted by first and second, which denote the two composable components. Labels multiply in traversal order. The equality uses associativity and inverse cancellation in an arbitrary group; it does not exchange group elements.

**Theorem 1.6 (Ordered total-label preservation).**

$$\forall H \in Type,\; [\operatorname{Group}\left(H\right)][\operatorname{Fintype}\left(H\right)][\operatorname{LinearOrder}\left(H\right)]\forall n \in Nat, m \in Nat, L \in Nat, A \in \operatorname{GroupMat}\left(H, n, n\right), B \in \operatorname{GroupMat}\left(H, m, m\right), c \in \operatorname{Chain}\left(H, A, B, L\right), i \in \operatorname{Fin}\left(n\right), j \in \operatorname{Fin}\left(m\right), p \in \Sigma_{x:\operatorname{Fin}\left(n\right)}((\operatorname{At}\left(A, i, x\right)\times\operatorname{FactorPath}\left(\operatorname{forwardFactors}\left(c\right), x, j\right))),\; \operatorname{factorLabel}\left(\operatorname{forwardFactors}\left(c\right), \operatorname{first}\left(\operatorname{apply}\left(\operatorname{phiR}\left(c, i, j\right), p\right)\right)\right) \cdot \operatorname{label}\left(\operatorname{second}\left(\operatorname{apply}\left(\operatorname{phiR}\left(c, i, j\right), p\right)\right)\right) = \operatorname{label}\left(\operatorname{first}\left(p\right)\right) \cdot \operatorname{factorLabel}\left(\operatorname{forwardFactors}\left(c\right), \operatorname{second}\left(p\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/PrescribedArrays.phiR_label` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The sigma vertex is omitted by first and second, which denote the two composable components. Labels multiply in traversal order. The equality uses associativity and inverse cancellation in an arbitrary group; it does not exchange group elements.

**Theorem 1.7 (Ordered total-label preservation).**

$$\forall H \in Type,\; [\operatorname{Group}\left(H\right)][\operatorname{Fintype}\left(H\right)][\operatorname{LinearOrder}\left(H\right)]\forall n \in Nat, m \in Nat, L \in Nat, A \in \operatorname{GroupMat}\left(H, n, n\right), B \in \operatorname{GroupMat}\left(H, m, m\right), c \in \operatorname{Chain}\left(H, A, B, L\right), i \in \operatorname{Fin}\left(m\right), j \in \operatorname{Fin}\left(n\right), p \in \Sigma_{x:\operatorname{Fin}\left(m\right)}((\operatorname{At}\left(B, i, x\right)\times\operatorname{FactorPath}\left(\operatorname{backwardFactors}\left(c\right), x, j\right))),\; \operatorname{factorLabel}\left(\operatorname{backwardFactors}\left(c\right), \operatorname{first}\left(\operatorname{apply}\left(\operatorname{phiS}\left(c, i, j\right), p\right)\right)\right) \cdot \operatorname{label}\left(\operatorname{second}\left(\operatorname{apply}\left(\operatorname{phiS}\left(c, i, j\right), p\right)\right)\right) = \operatorname{label}\left(\operatorname{first}\left(p\right)\right) \cdot \operatorname{factorLabel}\left(\operatorname{backwardFactors}\left(c\right), \operatorname{second}\left(p\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/PrescribedArrays.phiS_label` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The sigma vertex is omitted by first and second, which denote the two composable components. Labels multiply in traversal order. The equality uses associativity and inverse cancellation in an arbitrary group; it does not exchange group elements.

**Theorem 1.8 (Ordered total-label preservation).**

$$\forall H \in Type,\; [\operatorname{Group}\left(H\right)][\operatorname{Fintype}\left(H\right)][\operatorname{LinearOrder}\left(H\right)]\forall n \in Nat, m \in Nat, L \in Nat, A \in \operatorname{GroupMat}\left(H, n, n\right), B \in \operatorname{GroupMat}\left(H, m, m\right), c \in \operatorname{Chain}\left(H, A, B, L\right), i \in \operatorname{Fin}\left(n\right), j \in \operatorname{Fin}\left(m\right), p \in \Sigma_{x:\operatorname{Fin}\left(n\right)}((\operatorname{At}\left(A, i, x\right)\times\operatorname{At}\left(\operatorname{R}\left(c\right), x, j\right))),\; \operatorname{label}\left(\operatorname{first}\left(\operatorname{apply}\left(\operatorname{matrixPhiR}\left(c, i, j\right), p\right)\right)\right) \cdot \operatorname{label}\left(\operatorname{second}\left(\operatorname{apply}\left(\operatorname{matrixPhiR}\left(c, i, j\right), p\right)\right)\right) = \operatorname{label}\left(\operatorname{first}\left(p\right)\right) \cdot \operatorname{label}\left(\operatorname{second}\left(p\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/PrescribedArrays.matrixPhiR_label` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The sigma vertex is omitted by first and second, which denote the two composable components. Labels multiply in traversal order. The equality uses associativity and inverse cancellation in an arbitrary group; it does not exchange group elements.

**Theorem 1.9 (Ordered total-label preservation).**

$$\forall H \in Type,\; [\operatorname{Group}\left(H\right)][\operatorname{Fintype}\left(H\right)][\operatorname{LinearOrder}\left(H\right)]\forall n \in Nat, m \in Nat, L \in Nat, A \in \operatorname{GroupMat}\left(H, n, n\right), B \in \operatorname{GroupMat}\left(H, m, m\right), c \in \operatorname{Chain}\left(H, A, B, L\right), i \in \operatorname{Fin}\left(m\right), j \in \operatorname{Fin}\left(n\right), p \in \Sigma_{x:\operatorname{Fin}\left(m\right)}((\operatorname{At}\left(B, i, x\right)\times\operatorname{At}\left(\operatorname{S}\left(c\right), x, j\right))),\; \operatorname{label}\left(\operatorname{first}\left(\operatorname{apply}\left(\operatorname{matrixPhiS}\left(c, i, j\right), p\right)\right)\right) \cdot \operatorname{label}\left(\operatorname{second}\left(\operatorname{apply}\left(\operatorname{matrixPhiS}\left(c, i, j\right), p\right)\right)\right) = \operatorname{label}\left(\operatorname{first}\left(p\right)\right) \cdot \operatorname{label}\left(\operatorname{second}\left(p\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/PrescribedArrays.matrixPhiS_label` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The sigma vertex is omitted by first and second, which denote the two composable components. Labels multiply in traversal order. The equality uses associativity and inverse cancellation in an arbitrary group; it does not exchange group elements.

**Definition 1.10 (One row with its prescribed right boundary).**

$$\forall H \in Type,\; [\operatorname{Group}\left(H\right)][\operatorname{Fintype}\left(H\right)][\operatorname{LinearOrder}\left(H\right)]\forall n \in Nat, k \in Nat, U \in \operatorname{GroupMat}\left(H, n, k\right), V \in \operatorname{GroupMat}\left(H, k, n\right), l \in Nat, i \in \operatorname{Fin}\left(n\right), j \in \operatorname{Fin}\left(k\right),\; \operatorname{layerSweep}\left(U, V, l, i, j\right):\operatorname{Equiv}\left(\Sigma_{x:\operatorname{Fin}\left(n\right)}((\operatorname{Word}\left(\operatorname{product}\left(U, V\right), l, i, x\right)\times\operatorname{At}\left(U, x, j\right))), \Sigma_{y:\operatorname{Fin}\left(k\right)}((\operatorname{At}\left(U, i, y\right)\times\operatorname{Word}\left(\operatorname{product}\left(V, U\right), l, y, j\right)))\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/PrescribedArrays.layerSweep` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Apply the actual local cells from right to left along the row. The given U edge supplies the last cell at i=l-1, and each other cell reads the U edge just computed at its right neighbor. The reverse algorithm inverts the same cells in the opposite order.

**Definition 1.11 (A finite row with all numbered edges).**

$$\forall H \in Type,\; [\operatorname{Group}\left(H\right)]\forall n \in Nat, l \in Nat, A \in \operatorname{GroupMat}\left(H, n, n\right),\; \operatorname{NumberedRow}\left(A, l\right):Type$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/PrescribedArrays.NumberedRow` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A row consists of a vertex function x:Fin(l+1)→Fin n and, for each i:Fin l, an edge in At(A,x(i.castSucc),x(i.succ)). These are the literal vertices 0 through l and edges 0 through l−1. The length-zero row retains its named vertex.

**Definition 1.12 (All U half-edges including the prescribed boundary).**

$$\forall H \in Type,\; [\operatorname{Group}\left(H\right)][\operatorname{Fintype}\left(H\right)][\operatorname{LinearOrder}\left(H\right)]\forall n \in Nat, k \in Nat, l \in Nat, U \in \operatorname{GroupMat}\left(H, n, k\right), V \in \operatorname{GroupMat}\left(H, k, n\right), r \in \operatorname{NumberedRow}\left(U \cdot V, l\right), z \in \operatorname{Fin}\left(k\right), right \in \operatorname{At}\left(U, \operatorname{lastVertex}\left(r\right), z\right),\; \operatorname{rowHalves}\left(U, V, r, z, right\right):TypedUHalfEdges$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/PrescribedArrays.rowHalves` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For r:NumberedRow(UV,l), z:Fin k and right:At(U,r.vertex(l),z), this dependent function assigns a target y_i and an actual U edge from r.vertex(i) to y_i for every i:Fin(l+1). At i<l it reads the prescribed ordered theta split of r.edge(i); at i=l it returns exactly z and right. In this formula lastVertex denotes r.vertex(Fin.last l), and A=UV.

**Definition 1.13 (The literal eta recurrence).**

$$\forall H \in Type,\; [\operatorname{Group}\left(H\right)][\operatorname{Fintype}\left(H\right)][\operatorname{LinearOrder}\left(H\right)]\forall n \in Nat, k \in Nat, l \in Nat, U \in \operatorname{GroupMat}\left(H, n, k\right), V \in \operatorname{GroupMat}\left(H, k, n\right), r \in \operatorname{NumberedRow}\left(U \cdot V, l\right), z \in \operatorname{Fin}\left(k\right), right \in \operatorname{At}\left(U, \operatorname{lastVertex}\left(r\right), z\right),\; \operatorname{nextNumberedRow}\left(U, V, r, z, right\right):\operatorname{NumberedRow}\left(V \cdot U, l\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/PrescribedArrays.nextNumberedRow` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For the factor row A=UV and B=VU, let (u_i,v_i)=theta inverse(r.edge(i)) for i<l and let u_l be the prescribed right edge. The next vertex at i is target(u_i). Its edge at i is eta(v_i,u_(i+1)). The target of v_i is the source of u_(i+1), including at i=l−1, so every edge has its actual legal endpoints.

**Definition 1.14 (A row and its actual recurrence laws).**

$$\forall H \in Type,\; [\operatorname{Group}\left(H\right)][\operatorname{Fintype}\left(H\right)][\operatorname{LinearOrder}\left(H\right)]\forall n \in Nat, k \in Nat, l \in Nat, A \in \operatorname{GroupMat}\left(H, n, n\right), B \in \operatorname{GroupMat}\left(H, k, k\right), U \in \operatorname{GroupMat}\left(H, n, k\right), V \in \operatorname{GroupMat}\left(H, k, n\right), hA \in A = U \cdot V, hB \in B = V \cdot U, r \in \operatorname{NumberedRow}\left(A, l\right),\; \operatorname{G34Step}\left(A, B, U, V, hA, hB, r\right):Type$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/PrescribedArrays.G34Step` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A step retains next:NumberedRow(B,l), all u_i:At(U,r.vertex(i),next.vertex(i)) for 0≤i≤l, and all v_i:At(V,next.vertex(i),r.vertex(i+1)) for 0≤i<l. Its theta law states theta inverse(r.edge(i))=(next.vertex(i),u_i,v_i), with the A=UV equality transporting the input type. Its eta law states next.edge(i)=eta(v_i,u_(i+1)), with B=VU transporting the output type. Every label and copy number belongs to these actual sigma coordinates.

**Definition 1.15 (Construct a legal row with its prescribed boundary).**

$$\forall H \in Type,\; [\operatorname{Group}\left(H\right)][\operatorname{Fintype}\left(H\right)][\operatorname{LinearOrder}\left(H\right)]\forall n \in Nat, k \in Nat, l \in Nat, A \in \operatorname{GroupMat}\left(H, n, n\right), B \in \operatorname{GroupMat}\left(H, k, k\right), U \in \operatorname{GroupMat}\left(H, n, k\right), V \in \operatorname{GroupMat}\left(H, k, n\right), hA \in A = U \cdot V, hB \in B = V \cdot U, r \in \operatorname{NumberedRow}\left(A, l\right), z \in \operatorname{Fin}\left(k\right), right \in \operatorname{At}\left(U, \operatorname{lastVertex}\left(r\right), z\right),\; \operatorname{generateG34Step}\left(A, B, U, V, hA, hB, r, z, right\right):\operatorname{G34Step}\left(A, B, U, V, hA, hB, r\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/PrescribedArrays.generateG34Step` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The constructor applies the given ordered splits to all top edges and the given ordered joins to adjacent half-edges. It produces the complete G34Step and proves both displayed recurrence laws. Its final vertex is z and its final U edge is the supplied right edge, with only the necessary endpoint equality transport. Here lastVertex is r.vertex(Fin.last l).

**Definition 1.16 (The single dependent finite rectangular array).**

$$\forall H \in Type,\; [\operatorname{Group}\left(H\right)][\operatorname{Fintype}\left(H\right)][\operatorname{LinearOrder}\left(H\right)]\forall L \in Nat, l \in Nat, data \in \operatorname{IndexedChain}\left(H, L\right),\; \operatorname{G34Array}\left(data, l\right):Type$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/PrescribedArrays.G34Array` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The IndexedChain data retain every original d_j,A_j,U_j,V_j and both equalities A_j=U_jV_j and A_(j+1)=V_jU_j. An array has row(j):NumberedRow(A_j,l) for j:Fin(L+1), step(j):G34Step(A_j,A_(j+1),U_j,V_j,leftFactor(j),rightFactor(j),row(j)) for j:Fin L, and nextRow(j):step(j).next=row(j+1). Thus its a_i^j,u_i^j,v_i^j use literal i<l,j<L. Taking l=L gives exactly the source G34 square; intermediate dimensions may vary or vanish.

**Definition 1.17 (Generate the same array from the top and right sides).**

$$\forall H \in Type,\; [\operatorname{Group}\left(H\right)][\operatorname{Fintype}\left(H\right)][\operatorname{LinearOrder}\left(H\right)]\forall L \in Nat, l \in Nat, data \in \operatorname{IndexedChain}\left(H, L\right), b \in \left(\forall j \in \operatorname{Fin}\left(\operatorname{successor}\left(L\right)\right),\; \operatorname{Fin}\left(\operatorname{dimension}\left(data, j\right)\right)\right), rin \in \left(\forall j \in \operatorname{Fin}\left(L\right),\; \operatorname{At}\left(\operatorname{U}\left(data, j\right), \operatorname{b}\left(\operatorname{castSucc}\left(j\right)\right), \operatorname{b}\left(\operatorname{succ}\left(j\right)\right)\right)\right), r \in \operatorname{NumberedRow}\left(\operatorname{A}\left(data, 0\right), l\right), hr \in \operatorname{lastVertex}\left(r\right) = \operatorname{b}\left(0\right),\; \operatorname{generateG34}\left(data, l, b, rin, r, hr\right):\operatorname{PrescribedG34Array}\left(data, l, b, rin, r\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/PrescribedArrays.generateG34` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Here b(j):Fin(d_j) is the actual right-side vertex at each level, rin(j):At(U_j,b(j),b(j+1)) is each supplied right U edge, and r is the supplied A_0 top row with r.vertex(l)=b(0). PrescribedG34Array is the subtype of arrays g satisfying g.row(0)=r, g.row(j).vertex(l)=b(j) at every level and HEq(step(j).u(l),rin(j)) at every step. The recursion generates one complete row, then the actual remaining source layers. It imposes no inhabitance, positivity or commutativity premise.

**Theorem 1.18 (Uniqueness of one literal recurrence row).**

$$\forall H \in Type,\; [\operatorname{Group}\left(H\right)][\operatorname{Fintype}\left(H\right)][\operatorname{LinearOrder}\left(H\right)]\forall n \in Nat, k \in Nat, l \in Nat, A \in \operatorname{GroupMat}\left(H, n, n\right), B \in \operatorname{GroupMat}\left(H, k, k\right), U \in \operatorname{GroupMat}\left(H, n, k\right), V \in \operatorname{GroupMat}\left(H, k, n\right), hA \in A = U \cdot V, hB \in B = V \cdot U, r \in \operatorname{NumberedRow}\left(A, l\right), p \in \operatorname{G34Step}\left(A, B, U, V, hA, hB, r\right), q \in \operatorname{G34Step}\left(A, B, U, V, hA, hB, r\right),\; \operatorname{lastVertex}\left(\operatorname{next}\left(p\right)\right) = \operatorname{lastVertex}\left(\operatorname{next}\left(q\right)\right)\land\operatorname{HEq}\left(\operatorname{lastU}\left(p\right), \operatorname{lastU}\left(q\right)\right)\implies p = q$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/PrescribedArrays.g34Step_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For two legal G34 steps on the same original A,B,U,V,hA,hB and top row r, equality of their final next vertices and equality of their prescribed last U edges force equality of the entire steps. Theta determines every interior next vertex and half-edge; eta then determines every next numbered edge. HEq records the necessary dependent endpoint transport.

**Theorem 1.19 (Recurrence uniqueness for the entire same array).**

$$\forall H \in Type,\; [\operatorname{Group}\left(H\right)][\operatorname{Fintype}\left(H\right)][\operatorname{LinearOrder}\left(H\right)]\forall L \in Nat, l \in Nat, data \in \operatorname{IndexedChain}\left(H, L\right), p \in \operatorname{G34Array}\left(data, l\right), q \in \operatorname{G34Array}\left(data, l\right),\; \operatorname{row}\left(p, 0\right) = \operatorname{row}\left(q, 0\right)\land\operatorname{SameRightVertices}\left(p, q\right)\land\operatorname{SameRightUEdges}\left(p, q\right)\implies p = q$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/PrescribedArrays.g34Array_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

SameRightVertices means p.row(j).vertex(l)=q.row(j).vertex(l) for every j:Fin(L+1). SameRightUEdges means HEq(p.step(j).u(l),q.step(j).u(l)) for every j:Fin L. With the same top row these data determine equality of all rows, half-edges, actual numbered edges and recurrence proofs by finite level induction. No commutation hypothesis is used.

**Definition 1.20 (The complete word in a finite numbered row).**

$$\forall H \in Type,\; [\operatorname{Group}\left(H\right)]\forall n \in Nat, l \in Nat, A \in \operatorname{GroupMat}\left(H, n, n\right), r \in \operatorname{NumberedRow}\left(A, l\right),\; \operatorname{rowWord}\left(A, l, r\right):\operatorname{Word}\left(A, l, \operatorname{vertex}\left(r, 0\right), \operatorname{lastVertex}\left(r\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/PrescribedArrays.rowWord` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Read edges in increasing i order, retaining each intervening vertex, group label and copy number. The zero-length result is the named nil path at r.vertex(0), which is also the final vertex.

**Definition 1.21 (The actual subarray after the first layer).**

$$\forall H \in Type,\; [\operatorname{Group}\left(H\right)][\operatorname{Fintype}\left(H\right)][\operatorname{LinearOrder}\left(H\right)]\forall L \in Nat, l \in Nat, data \in \operatorname{IndexedChain}\left(H, \operatorname{successor}\left(L\right)\right), g \in \operatorname{G34Array}\left(data, l\right),\; \operatorname{arrayTail}\left(g\right):\operatorname{G34Array}\left(\operatorname{tail}\left(data\right), l\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/PrescribedArrays.arrayTail` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For data of length L+1, remove the first source layer. The resulting row(j),step(j),nextRow(j) are the original row(j+1),step(j+1),nextRow(j+1). Its source is exactly tail(data), not another chain with equal endpoint products.

**Definition 1.22 (The source-indexed left U boundary).**

$$\forall H \in Type,\; [\operatorname{Group}\left(H\right)][\operatorname{Fintype}\left(H\right)][\operatorname{LinearOrder}\left(H\right)]\forall L \in Nat, l \in Nat, data \in \operatorname{IndexedChain}\left(H, L\right), g \in \operatorname{G34Array}\left(data, l\right),\; \operatorname{arrayLeftPath}\left(g\right):\operatorname{FactorPath}\left(\operatorname{forwardFactors}\left(\operatorname{toChain}\left(data\right)\right), \operatorname{vertex}\left(\operatorname{row}\left(g, 0\right), 0\right), \operatorname{vertex}\left(\operatorname{row}\left(g, L\right), 0\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/PrescribedArrays.arrayLeftPath` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This is the actual factor path (u_0^0,u_0^1,...,u_0^(L−1)), with each edge transported through nextRow to the matching next source row. Its initial endpoint is a_0^0 source and its final endpoint is a_0^L source. At L=0 it is the named nil path.

**Definition 1.23 (The actual R output and bottom row).**

$$\forall H \in Type,\; [\operatorname{Group}\left(H\right)][\operatorname{Fintype}\left(H\right)][\operatorname{LinearOrder}\left(H\right)]\forall L \in Nat, l \in Nat, data \in \operatorname{IndexedChain}\left(H, L\right), g \in \operatorname{G34Array}\left(data, l\right),\; \operatorname{arrayOutput}\left(g\right):\operatorname{LeftBoundaryAndBottomWord}\left(data, l, g\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/PrescribedArrays.arrayOutput` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

LeftBoundaryAndBottomWord is the sigma over y:Fin(d_L) of FactorPath(forwardFactors(toChain(data)),row(0).vertex(0),y) times Word(A_L,l,y,row(L).vertex(l)). The constructor uses exactly y=row(L).vertex(0), the literal leftPath, and rowWord of the same array’s bottom row.

**Theorem 1.24 (The sweep evaluates the literal same row).**

$$\forall H \in Type,\; [\operatorname{Group}\left(H\right)][\operatorname{Fintype}\left(H\right)][\operatorname{LinearOrder}\left(H\right)]\forall n \in Nat, k \in Nat, l \in Nat, U \in \operatorname{GroupMat}\left(H, n, k\right), V \in \operatorname{GroupMat}\left(H, k, n\right), r \in \operatorname{NumberedRow}\left(U \cdot V, l\right), p \in \operatorname{G34FactorStep}\left(U, V, r\right),\; \operatorname{layerSweep}\left(U, V, l, \operatorname{firstVertex}\left(r\right), \operatorname{lastVertex}\left(\operatorname{next}\left(p\right)\right), \operatorname{topWordAndLastU}\left(r, p\right)\right) = \operatorname{firstUAndBottomWord}\left(p\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/PrescribedArrays.g34_layerSweep` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

G34FactorStep(U,V,r) is G34Step(UV,VU,U,V,rfl,rfl,r). The input is the sigma tuple (r.vertex(l),rowWord(UV,l,r),p.u(l)). The output is (p.next.vertex(0),p.u(0),rowWord(VU,l,p.next)). Thus the actual layerSweep evaluates this same legal G34 row, including its prescribed last U edge and every independent label and copy number. The proof recursively evaluates the right suffix and then its remaining local cell.

**Definition 1.25 (Remove the first actual word edge).**

$$\forall H \in Type,\; [\operatorname{Group}\left(H\right)]\forall n \in Nat, l \in Nat, A \in \operatorname{GroupMat}\left(H, n, n\right), r \in \operatorname{NumberedRow}\left(A, \operatorname{successor}\left(l\right)\right),\; \operatorname{rowTail}\left(r\right):\operatorname{NumberedRow}\left(A, l\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/PrescribedArrays.rowTail` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For r of length l+1, vertex(i)=r.vertex(i.succ) and edge(i)=r.edge(i.succ). This preserves the full actual endpoints and numbered edges.

**Definition 1.26 (Remove the first column of the same typed step).**

$$\forall H \in Type,\; [\operatorname{Group}\left(H\right)][\operatorname{Fintype}\left(H\right)][\operatorname{LinearOrder}\left(H\right)]\forall n \in Nat, k \in Nat, l \in Nat, A \in \operatorname{GroupMat}\left(H, n, n\right), B \in \operatorname{GroupMat}\left(H, k, k\right), U \in \operatorname{GroupMat}\left(H, n, k\right), V \in \operatorname{GroupMat}\left(H, k, n\right), hA \in A = U \cdot V, hB \in B = V \cdot U, r \in \operatorname{NumberedRow}\left(A, \operatorname{successor}\left(l\right)\right), p \in \operatorname{G34Step}\left(A, B, U, V, hA, hB, r\right),\; \operatorname{stepTail}\left(p\right):\operatorname{G34Step}\left(A, B, U, V, hA, hB, \operatorname{rowTail}\left(r\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/PrescribedArrays.stepTail` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The next row is rowTail(p.next). All u,v,theta,eta fields are restricted by i.succ. Both matrix equations remain the original hA,hB.

**Definition 1.27 (Remove the last actual word edge).**

$$\forall H \in Type,\; [\operatorname{Group}\left(H\right)]\forall n \in Nat, l \in Nat, A \in \operatorname{GroupMat}\left(H, n, n\right), r \in \operatorname{NumberedRow}\left(A, \operatorname{successor}\left(l\right)\right),\; \operatorname{rowPrefix}\left(r\right):\operatorname{NumberedRow}\left(A, l\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/PrescribedArrays.rowPrefix` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For r of length l+1, vertex(i)=r.vertex(i.castSucc) and edge(i)=r.edge(i.castSucc), retaining every prefix endpoint and numbered edge.

**Definition 1.28 (Remove the last column of every actual row).**

$$\forall H \in Type,\; [\operatorname{Group}\left(H\right)][\operatorname{Fintype}\left(H\right)][\operatorname{LinearOrder}\left(H\right)]\forall L \in Nat, l \in Nat, data \in \operatorname{IndexedChain}\left(H, L\right), g \in \operatorname{G34Array}\left(data, \operatorname{successor}\left(l\right)\right),\; \operatorname{arrayPrefix}\left(g\right):\operatorname{G34Array}\left(data, l\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/PrescribedArrays.arrayPrefix` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

All rows use rowPrefix, all steps restrict their u,v,theta,eta fields by castSucc, and every nextRow proof is transported by rowPrefix. The original full indexed chain and both factor equations are unchanged.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/PrescribedArrays.G34Array`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/PrescribedArrays.G34Step`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/PrescribedArrays.NumberedRow`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/PrescribedArrays.arrayLeftPath`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/PrescribedArrays.arrayOutput`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/PrescribedArrays.arrayPrefix`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/PrescribedArrays.arrayTail`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/PrescribedArrays.g34Array_unique`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/PrescribedArrays.g34Step_unique`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/PrescribedArrays.g34_layerSweep`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/PrescribedArrays.generateG34`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/PrescribedArrays.generateG34Step`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/PrescribedArrays.layerSweep`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/PrescribedArrays.matrixPhiR_label`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/PrescribedArrays.matrixPhiS_label`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/PrescribedArrays.matrixPsi0_label`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/PrescribedArrays.matrixPsiL_label`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/PrescribedArrays.nextNumberedRow`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/PrescribedArrays.phiR_label`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/PrescribedArrays.phiS_label`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/PrescribedArrays.psi0_label`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/PrescribedArrays.psiL_label`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/PrescribedArrays.rowFirst`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/PrescribedArrays.rowHalves`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/PrescribedArrays.rowPrefix`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/PrescribedArrays.rowTail`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/PrescribedArrays.rowWord`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/PrescribedArrays.stepTail`
- Dependency: [D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/FactorPaths](FactorPaths.md)
