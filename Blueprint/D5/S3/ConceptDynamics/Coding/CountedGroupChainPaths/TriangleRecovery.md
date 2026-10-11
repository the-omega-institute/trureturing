# Exact triangle recovery in the prescribed array

## Abstract

Exact triangle recovery in the prescribed array. All numbered edges, ordered labels and source conditions are retained.

**Definition 1.1 (The literal decreasing V diagonal).**

$$\forall H \in Type,\; [\operatorname{Group}\left(H\right)][\operatorname{Fintype}\left(H\right)][\operatorname{LinearOrder}\left(H\right)]\forall L \in Nat, data \in \operatorname{IndexedChain}\left(H, L\right), g \in \operatorname{G34Array}\left(data, L\right),\; \operatorname{arrayMiddlePath}\left(g\right):\operatorname{FactorPath}\left(\operatorname{backwardFactors}\left(\operatorname{toChain}\left(data\right)\right), \operatorname{vertex}\left(\operatorname{row}\left(g, L\right), 0\right), \operatorname{vertex}\left(\operatorname{row}\left(g, 0\right), L\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/TriangleRecovery.arrayMiddlePath` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Read v_0^(L−1),v_1^(L−2),...,v_(L−1)^0 from this same literal square. Removing its first layer and final column restricts to the same inner triangle; append the original final V_0 edge. The path begins at row(L).vertex(0) and ends at row(0).vertex(L), following backwardFactors(toChain(data)) in decreasing layer order. Every actual V copy and label is retained. At L=0 this is the named nil vertex.

**Theorem 1.2 (Forward peeling of the same recurrence row).**

$$\forall H \in Type,\; [\operatorname{Group}\left(H\right)][\operatorname{Fintype}\left(H\right)][\operatorname{LinearOrder}\left(H\right)]\forall n \in Nat, k \in Nat, l \in Nat, U \in \operatorname{GroupMat}\left(H, n, k\right), V \in \operatorname{GroupMat}\left(H, k, n\right), r \in \operatorname{NumberedRow}\left(U \cdot V, \operatorname{successor}\left(l\right)\right), p \in \operatorname{G34FactorStep}\left(U, V, r\right),\; \operatorname{peelRow}\left(U, V, l, \operatorname{vertex}\left(r, 0\right), \operatorname{lastVertex}\left(r\right), \operatorname{rowWord}\left(U \cdot V, \operatorname{successor}\left(l\right), r\right)\right) = \operatorname{tuple}\left(\operatorname{vertex}\left(\operatorname{next}\left(p\right), 0\right), \operatorname{vertex}\left(\operatorname{next}\left(p\right), l\right), \operatorname{u}\left(p, 0\right), \operatorname{rowWord}\left(V \cdot U, l, \operatorname{rowPrefix}\left(\operatorname{next}\left(p\right)\right)\right), \operatorname{v}\left(p, l\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/TriangleRecovery.g34_peelRow` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

G34FactorStep(U,V,r) means G34Step(UV,VU,U,V,rfl,rfl,r). For a row of length l+1, peelRow returns the tuple (next.vertex(0),next.vertex(l),u(0),rowWord(VU,l,rowPrefix(next)),v(l)). Here rowPrefix deletes the last edge and last vertex, and tuple denotes the nested dependent sigma and product of PeelBoundary. This is the same row’s interior eta word, left U edge and last V edge. The prescribed outer U(l+1) is not used. For l=0 the interior word is nil at next.vertex(0).

**Theorem 1.3 (Reverse peeling of the same recurrence row).**

$$\forall H \in Type,\; [\operatorname{Group}\left(H\right)][\operatorname{Fintype}\left(H\right)][\operatorname{LinearOrder}\left(H\right)]\forall n \in Nat, k \in Nat, l \in Nat, U \in \operatorname{GroupMat}\left(H, n, k\right), V \in \operatorname{GroupMat}\left(H, k, n\right), r \in \operatorname{NumberedRow}\left(U \cdot V, \operatorname{successor}\left(l\right)\right), p \in \operatorname{G34FactorStep}\left(U, V, r\right),\; \operatorname{peelRow}\left(V, U, l, \operatorname{vertex}\left(\operatorname{next}\left(p\right), 0\right), \operatorname{lastVertex}\left(\operatorname{next}\left(p\right)\right), \operatorname{rowWord}\left(V \cdot U, \operatorname{successor}\left(l\right), \operatorname{next}\left(p\right)\right)\right) = \operatorname{tuple}\left(\operatorname{vertex}\left(r, 1\right), \operatorname{lastVertex}\left(r\right), \operatorname{v}\left(p, 0\right), \operatorname{rowWord}\left(U \cdot V, l, \operatorname{rowTail}\left(r\right)\right), \operatorname{u}\left(p, \operatorname{successor}\left(l\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/TriangleRecovery.g34_reversePeelRow` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the same U,V,r and G34FactorStep p, reverse peeling of next returns (r.vertex(1),r.vertex(l+1),v(0),rowWord(UV,l,rowTail(r)),u(l+1)). The operation rowTail deletes the first edge and first vertex. Tuple has the dependent PeelBoundary type, retaining actual endpoints, labels and independent copy numbers. Thus the saved last U is the originally prescribed right edge of this same legal row, and the inner word is the exact source suffix. At l=0 that suffix is the named nil at r.vertex(1).

**Theorem 1.4 (Both complete evaluations on every actual input).**

$$\forall H \in Type,\; [\operatorname{Group}\left(H\right)][\operatorname{Fintype}\left(H\right)][\operatorname{LinearOrder}\left(H\right)]\forall n \in Nat, m \in Nat, L \in Nat, A \in \operatorname{GroupMat}\left(H, n, n\right), B \in \operatorname{GroupMat}\left(H, m, m\right), c \in \operatorname{Chain}\left(H, A, B, L\right), l \in Nat, i \in \operatorname{Fin}\left(n\right), j \in \operatorname{Fin}\left(m\right), p \in \operatorname{WordAndRightBoundary}\left(A, l, \operatorname{forwardFactors}\left(c\right), i, j\right),\; \operatorname{rowFirst}\left(c, l, i, j, p\right) = \operatorname{phiRPower}\left(c, l, i, j, p\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/TriangleRecovery.rowFirst_eq_phiRPower` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

WordAndRightBoundary denotes the sigma over x:Fin n of Word(A,l,i,x) times FactorPath(forwardFactors(c),x,j). For every actual chain c, every finite word length l, every pair of endpoints and every such input p, the complete row-first evaluation equals the right-to-left column-first phiRPower evaluation, including the full output path, word, all endpoint vertices, ordered labels and numbered parallel edges. The proof uses induction on the actual chain to establish the word-successor equation, then induction on word length. It assumes no commuting adjacent functions and no long compatibility law.

**Definition 1.5 (Read the complete original word as a numbered row).**

$$\forall H \in Type,\; [\operatorname{Group}\left(H\right)]\forall n \in Nat, l \in Nat, A \in \operatorname{GroupMat}\left(H, n, n\right), i \in \operatorname{Fin}\left(n\right), j \in \operatorname{Fin}\left(n\right), w \in \operatorname{Word}\left(A, l, i, j\right),\; \operatorname{wordToRow}\left(A, l, i, j, w\right):\operatorname{RowWithWord}\left(A, l, i, j, w\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/TriangleRecovery.wordToRow` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

RowWithWord is the subtype of r:NumberedRow(A,l) with r.vertex(0)=i, r.vertex(l)=j and HEq(rowWord(A,l,r),w). Recursion reads every actual numbered edge of w and keeps its ordered label and intermediate vertex. The zero-word case keeps the original named vertex; it introduces no arbitrary enumeration.

**Definition 1.6 (The exact prescribed right-side factor data).**

$$\forall H \in Type,\; [\operatorname{Group}\left(H\right)][\operatorname{Fintype}\left(H\right)]\forall L \in Nat, data \in \operatorname{IndexedChain}\left(H, L\right), i \in \operatorname{Fin}\left(\operatorname{dimension}\left(data, 0\right)\right), j \in \operatorname{Fin}\left(\operatorname{dimension}\left(data, L\right)\right),\; \operatorname{RightBoundary}\left(data, i, j\right):Type$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/TriangleRecovery.RightBoundary` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A RightBoundary(data,i,j) retains vertex(k):Fin(d_k) for every k from 0 through L and edge(k):At(U_k,vertex(k),vertex(k+1)) for every k<L. Its first vertex equals i and its last equals j. Thus every original U factor edge, label and copy is prescribed.

**Definition 1.7 (Unpack the entire original R factor path).**

$$\forall H \in Type,\; [\operatorname{Group}\left(H\right)][\operatorname{Fintype}\left(H\right)]\forall L \in Nat, data \in \operatorname{IndexedChain}\left(H, L\right), i \in \operatorname{Fin}\left(\operatorname{dimension}\left(data, 0\right)\right), j \in \operatorname{Fin}\left(\operatorname{dimension}\left(data, L\right)\right), p \in \operatorname{FactorPath}\left(\operatorname{forwardFactors}\left(\operatorname{toChain}\left(data\right)\right), i, j\right),\; \operatorname{pathToRightBoundary}\left(data, i, j, p\right):\operatorname{RightBoundary}\left(data, i, j\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/TriangleRecovery.pathToRightBoundary` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Structural recursion on the original indexed chain reads each whole factor-path coordinate. The named nil vertex supplies both boundary endpoints at L=0. A successor retains its actual first U edge and recursively retains the same suffix.

**Definition 1.8 (Generate G34 from the actual word and whole factor path).**

$$\forall H \in Type,\; [\operatorname{Group}\left(H\right)][\operatorname{Fintype}\left(H\right)][\operatorname{LinearOrder}\left(H\right)]\forall L \in Nat, l \in Nat, data \in \operatorname{IndexedChain}\left(H, L\right), i \in \operatorname{Fin}\left(\operatorname{dimension}\left(data, 0\right)\right), j \in \operatorname{Fin}\left(\operatorname{dimension}\left(data, L\right)\right), p \in \operatorname{OriginalWordAndRightFactorPath}\left(data, l, i, j\right),\; \operatorname{wordFactorArray}\left(data, l, i, j, p\right):\operatorname{G34Array}\left(data, l\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/TriangleRecovery.wordFactorArray` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The input is the sigma over x:Fin(d_0) of Word(A_0,l,i,x) times FactorPath(forwardFactors(toChain(data)),x,j). wordToRow reads its actual top word and pathToRightBoundary reads its full prescribed right U path. Their endpoint proofs provide the required seam, and generateG34 fills the same original indexed recurrence.

**Definition 1.9 (The entire original right U column).**

$$\forall H \in Type,\; [\operatorname{Group}\left(H\right)][\operatorname{Fintype}\left(H\right)][\operatorname{LinearOrder}\left(H\right)]\forall L \in Nat, l \in Nat, data \in \operatorname{IndexedChain}\left(H, L\right), g \in \operatorname{G34Array}\left(data, l\right),\; \operatorname{arrayRightPath}\left(g\right):\operatorname{RightColumnFactorPath}\left(data, l, g\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/TriangleRecovery.arrayRightPath` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

RightColumnFactorPath has factors forwardFactors(toChain(data)), source row(0).vertex(l) and target row(L).vertex(l). It reads u_l^0,...,u_l^(L-1), transported only by each nextRow equality; the zero-length column is the named nil vertex.

**Theorem 1.10 (All rows evaluate this same full array).**

$$\forall H \in Type,\; [\operatorname{Group}\left(H\right)][\operatorname{Fintype}\left(H\right)][\operatorname{LinearOrder}\left(H\right)]\forall L \in Nat, l \in Nat, data \in \operatorname{IndexedChain}\left(H, L\right), g \in \operatorname{G34Array}\left(data, l\right),\; \operatorname{rowFirst}\left(\operatorname{toChain}\left(data\right), l, \operatorname{topSource}\left(g\right), \operatorname{bottomTarget}\left(g\right), \operatorname{arrayInput}\left(g\right)\right) = \operatorname{arrayOutput}\left(g\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/TriangleRecovery.g34_rowFirst` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every original IndexedChain data, every finite width l and every legal G34Array g, arrayInput is (row(0).vertex(l),rowWord(A_0,l,row(0)),arrayRightPath(g)). Its endpoints are topSource=row(0).vertex(0) and bottomTarget=row(L).vertex(l). The complete rowFirst algorithm returns exactly arrayOutput(g), the left U column and the same full bottom word. Induction passes through each actual varying-dimension layer using its supplied factor equalities.

**Theorem 1.11 (All columns evaluate that very same full array).**

$$\forall H \in Type,\; [\operatorname{Group}\left(H\right)][\operatorname{Fintype}\left(H\right)][\operatorname{LinearOrder}\left(H\right)]\forall L \in Nat, l \in Nat, data \in \operatorname{IndexedChain}\left(H, L\right), g \in \operatorname{G34Array}\left(data, l\right),\; \operatorname{phiRPower}\left(\operatorname{toChain}\left(data\right), l, \operatorname{topSource}\left(g\right), \operatorname{bottomTarget}\left(g\right), \operatorname{arrayInput}\left(g\right)\right) = \operatorname{arrayOutput}\left(g\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/TriangleRecovery.g34_phiRPower` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the identical data,g and complete prescribed input just defined, the actual right-to-left column-first phiRPower evaluation returns that same arrayOutput. The equality includes all factor edges, bottom-row edges, group labels and copy numbers. It uses the proved complete row/column equality, with no assumed long law or commutation principle.

**Theorem 1.12 (The actual input word is the generated top word).**

$$\forall H \in Type,\; [\operatorname{Group}\left(H\right)][\operatorname{Fintype}\left(H\right)][\operatorname{LinearOrder}\left(H\right)]\forall L \in Nat, l \in Nat, data \in \operatorname{IndexedChain}\left(H, L\right), i \in \operatorname{Fin}\left(\operatorname{dimension}\left(data, 0\right)\right), j \in \operatorname{Fin}\left(\operatorname{dimension}\left(data, L\right)\right), p \in \operatorname{OriginalWordAndRightFactorPath}\left(data, l, i, j\right),\; \operatorname{HEq}\left(\operatorname{rowWord}\left(\operatorname{A}\left(data, 0\right), l, \operatorname{row}\left(\operatorname{wordFactorArray}\left(data, l, i, j, p\right), 0\right)\right), \operatorname{inputWord}\left(p\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/TriangleRecovery.wordFactorArray_top` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every actual typed input p, the top row of wordFactorArray reads back its full original word p.second.first. HEq accounts for the reconstructed endpoint proofs and preserves every actual numbered edge. The proof consumes both the exact generated top-row identity and the wordToRow reconstruction law.

**Theorem 1.13 (The literal top triangle recovers R and S).**

$$\forall H \in Type,\; [\operatorname{Group}\left(H\right)][\operatorname{Fintype}\left(H\right)][\operatorname{LinearOrder}\left(H\right)]\forall L \in Nat, data \in \operatorname{IndexedChain}\left(H, L\right), g \in \operatorname{G34Array}\left(data, L\right),\; \operatorname{inverseTopTriangle}\left(data, g\right) = \operatorname{tuple}\left(\operatorname{vertex}\left(\operatorname{row}\left(g, L\right), 0\right), \operatorname{arrayLeftPath}\left(g\right), \operatorname{arrayMiddlePath}\left(g\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/TriangleRecovery.g34_psi0` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every source square g, inverseTopTriangle means psi0(toChain(data),row(0).vertex(0),row(0).vertex(L)) inverse applied to rowWord(A_0,L,row(0)). Its result is exactly (row(L).vertex(0),R_out,S_mid), where R_out=arrayLeftPath(g) reads u_0^0 through u_0^(L−1) and S_mid=arrayMiddlePath(g) reads v_0^(L−1),v_1^(L−2),...,v_(L−1)^0. The entire sigma equality includes every endpoint, ordered label and copy. At L=0 it recovers the named nil vertex.

**Theorem 1.14 (The literal bottom triangle recovers S and the prescribed R).**

$$\forall H \in Type,\; [\operatorname{Group}\left(H\right)][\operatorname{Fintype}\left(H\right)][\operatorname{LinearOrder}\left(H\right)]\forall L \in Nat, data \in \operatorname{IndexedChain}\left(H, L\right), g \in \operatorname{G34Array}\left(data, L\right),\; \operatorname{inverseBottomTriangle}\left(data, g\right) = \operatorname{tuple}\left(\operatorname{vertex}\left(\operatorname{row}\left(g, 0\right), L\right), \operatorname{arrayMiddlePath}\left(g\right), \operatorname{arrayRightPath}\left(g\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/TriangleRecovery.g34_psiL` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

InverseBottomTriangle is psiL(toChain(data),row(L).vertex(0),row(L).vertex(L)) inverse applied to the complete bottom Word(A_L,L,row(L)). It yields exactly (row(0).vertex(L),S_mid,R_in), with the identical diagonal S_mid and the original prescribed right path u_L^0,...,u_L^(L−1). Induction removes the last actual source layer and first column, uses reverse peeling of that same row, prepends its literal left V and appends its original right U. The path identities agree with the existing decreasing V and increasing U paths. No supplied bottom-boundary identity is used.

**Theorem 1.15 (Both triangles and the sweep on the same square).**

$$\forall H \in Type,\; [\operatorname{Group}\left(H\right)][\operatorname{Fintype}\left(H\right)][\operatorname{LinearOrder}\left(H\right)]\forall L \in Nat, data \in \operatorname{IndexedChain}\left(H, L\right), g \in \operatorname{G34Array}\left(data, L\right),\; \operatorname{sweepOfTopTriangleAndRight}\left(data, g\right) = \operatorname{leftAndBottomTriangle}\left(data, g\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/TriangleRecovery.g34_longR` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let i=row(0).vertex(0),x=row(0).vertex(L),y=row(L).vertex(0),j=row(L).vertex(L). Write R=R_out,S=S_mid,Rprime=R_in. Then phiRPower(c,L,i,j)(x,psi0(c,i,x)(y,R,S),Rprime)=(y,R,psiL(c,y,j)(x,S,Rprime)), with c=toChain(data). This is the literal whole-square equation on its actual three boundary paths. It follows from the two inverse triangle identities and the complete column evaluation.

**Theorem 1.16 (Reverse an appended original step).**

$$\forall H \in Type,\; [\operatorname{Group}\left(H\right)][\operatorname{Fintype}\left(H\right)]\forall n \in Nat, k \in Nat, m \in Nat, L \in Nat, A \in \operatorname{GroupMat}\left(H, n, n\right), B \in \operatorname{GroupMat}\left(H, k, k\right), C \in \operatorname{GroupMat}\left(H, m, m\right), c \in \operatorname{Chain}\left(H, A, B, L\right), U \in \operatorname{GroupMat}\left(H, k, m\right), V \in \operatorname{GroupMat}\left(H, m, k\right), hB \in B = U \cdot V, hC \in C = V \cdot U,\; \operatorname{reverseChain}\left(\operatorname{chainSnoc}\left(c, U, V, hB, hC\right)\right) = \operatorname{ChainCons}\left(V, U, hC, hB, \operatorname{reverseChain}\left(c\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/TriangleRecovery.reverseChain_snoc` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Reversing the appended U,V step places the actual exchanged V,U step first, with hC,hB in that order, followed by the same reversed original chain.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/TriangleRecovery.RightBoundary`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/TriangleRecovery.arrayMiddlePath`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/TriangleRecovery.arrayRightPath`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/TriangleRecovery.g34_longR`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/TriangleRecovery.g34_peelRow`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/TriangleRecovery.g34_phiRPower`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/TriangleRecovery.g34_psi0`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/TriangleRecovery.g34_psiL`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/TriangleRecovery.g34_reversePeelRow`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/TriangleRecovery.g34_rowFirst`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/TriangleRecovery.pathToRightBoundary`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/TriangleRecovery.reverseChain_snoc`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/TriangleRecovery.rowFirst_eq_phiRPower`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/TriangleRecovery.wordFactorArray`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/TriangleRecovery.wordFactorArray_top`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/TriangleRecovery.wordToRow`
- Dependency: [D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/PrescribedArrays](PrescribedArrays.md)
