# Complete original long compatibility equations

## Abstract

Complete original long compatibility equations. All numbered edges, ordered labels and source conditions are retained.

**Definition 1.1 (Reassemble every prescribed original U edge).**

$$\forall H \in Type,\; [\operatorname{Group}\left(H\right)][\operatorname{Fintype}\left(H\right)]\forall L \in Nat, data \in \operatorname{IndexedChain}\left(H, L\right), v \in \operatorname{BoundaryVertices}\left(data\right), e \in \operatorname{BoundaryUEdges}\left(data, v\right),\; \operatorname{rightBoundaryPath}\left(data, v, e\right):\operatorname{FactorPath}\left(\operatorname{forwardFactors}\left(\operatorname{toChain}\left(data\right)\right), \operatorname{v}\left(0\right), \operatorname{v}\left(L\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths.rightBoundaryPath` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

BoundaryVertices means v(k):Fin(d_k) for every k:Fin(L+1). BoundaryUEdges means e(k):At(U_k,v(k),v(k+1)) for every k:Fin L. Reassembly reads these edges in increasing source-layer order; the nil case retains v(0). The generated-boundary bridge proves that unpacking and reassembling the original factor path recovers that path, including labels and copies.

**Theorem 1.2 (The entire generated right boundary is the original input).**

$$\forall H \in Type,\; [\operatorname{Group}\left(H\right)][\operatorname{Fintype}\left(H\right)][\operatorname{LinearOrder}\left(H\right)]\forall L \in Nat, l \in Nat, data \in \operatorname{IndexedChain}\left(H, L\right), i \in \operatorname{Fin}\left(\operatorname{dimension}\left(data, 0\right)\right), j \in \operatorname{Fin}\left(\operatorname{dimension}\left(data, L\right)\right), p \in \operatorname{OriginalWordAndRightFactorPath}\left(data, l, i, j\right),\; \operatorname{HEq}\left(\operatorname{arrayRightPath}\left(\operatorname{wordFactorArray}\left(data, l, i, j, p\right)\right), \operatorname{inputRightPath}\left(p\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths.wordFactorArray_right` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For all original typed inputs p, arrayRightPath(wordFactorArray(data,l,i,j,p)) is heterogeneously equal to p.second.second. Every generated last U edge is the actual prescribed input edge; finite induction reassembles the complete original path. Together with wordFactorArray_top and its endpoint identities, this gives the actual Word/FactorPath-to-G34 bridge for every input, including a named nil word and path.

**Theorem 1.3 (The original long R law for every supplied chain).**

$$\forall H \in Type,\; [\operatorname{Group}\left(H\right)][\operatorname{Fintype}\left(H\right)][\operatorname{LinearOrder}\left(H\right)]\forall n \in Nat, m \in Nat, L \in Nat, A \in \operatorname{GroupMat}\left(H, n, n\right), B \in \operatorname{GroupMat}\left(H, m, m\right), c \in \operatorname{Chain}\left(H, A, B, L\right),\; \forall i \in \operatorname{Fin}\left(n\right), x \in \operatorname{Fin}\left(n\right), y \in \operatorname{Fin}\left(m\right), j \in \operatorname{Fin}\left(m\right), r \in \operatorname{FactorPath}\left(\operatorname{forwardFactors}\left(c\right), i, y\right), s \in \operatorname{FactorPath}\left(\operatorname{backwardFactors}\left(c\right), y, x\right), rp \in \operatorname{FactorPath}\left(\operatorname{forwardFactors}\left(c\right), x, j\right),\; \operatorname{phiRPower}\left(c, L, i, j, \operatorname{tuple}\left(x, \operatorname{psi0}\left(c, i, x, \operatorname{tuple}\left(y, r, s\right)\right), rp\right)\right) = \operatorname{tuple}\left(y, r, \operatorname{psiL}\left(c, y, j, \operatorname{tuple}\left(x, s, rp\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths.phiRPower_long` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For all original H,n,m,L,A,B,c,i,x,y,j and paths r:forwardFactors(c)(i,y),s:backwardFactors(c)(y,x),rprime:forwardFactors(c)(x,j), the displayed equality holds on the entire typed input. The actual chain is indexed without changing its factors; its Word/FactorPath input generates the prescribed G34 square. The two recovered triangle boundaries identify exactly r,s,rprime. The equation is a conclusion, with no long-law, commutation or enumeration hypothesis.

**Theorem 1.4 (The original long S law on that same tuple).**

$$\forall H \in Type,\; [\operatorname{Group}\left(H\right)][\operatorname{Fintype}\left(H\right)][\operatorname{LinearOrder}\left(H\right)]\forall n \in Nat, m \in Nat, L \in Nat, A \in \operatorname{GroupMat}\left(H, n, n\right), B \in \operatorname{GroupMat}\left(H, m, m\right), c \in \operatorname{Chain}\left(H, A, B, L\right),\; \forall i \in \operatorname{Fin}\left(m\right), x \in \operatorname{Fin}\left(m\right), y \in \operatorname{Fin}\left(n\right), j \in \operatorname{Fin}\left(n\right), r \in \operatorname{FactorPath}\left(\operatorname{backwardFactors}\left(c\right), i, y\right), s \in \operatorname{FactorPath}\left(\operatorname{forwardFactors}\left(c\right), y, x\right), rp \in \operatorname{FactorPath}\left(\operatorname{backwardFactors}\left(c\right), x, j\right),\; \operatorname{phiSPower}\left(c, L, i, j, \operatorname{tuple}\left(x, \operatorname{psiL}\left(c, i, x, \operatorname{tuple}\left(y, r, s\right)\right), rp\right)\right) = \operatorname{tuple}\left(y, r, \operatorname{psi0}\left(c, y, j, \operatorname{tuple}\left(x, s, rp\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths.phiSPower_long` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In this dual displayed formula r names the S path, s names the R path and rprime names the second S path. The proof applies the constructed R law to reverseChain(c), whose U factors are the original V factors in decreasing order. Reversing twice recovers c, so its terminal triangle is the original psi0. The result uses the same A,B,R,S,L and all actual numbered paths; it restricts neither the group nor dimensions.

**Definition 1.5 (Synchronous whole-rank conjugation of the complete R sweep).**

$$\forall H \in Type,\; [\operatorname{Group}\left(H\right)][\operatorname{Fintype}\left(H\right)][\operatorname{LinearOrder}\left(H\right)]\forall n \in Nat, m \in Nat, L \in Nat, A \in \operatorname{GroupMat}\left(H, n, n\right), B \in \operatorname{GroupMat}\left(H, m, m\right), c \in \operatorname{Chain}\left(H, A, B, L\right), l \in Nat, i \in \operatorname{Fin}\left(n\right), j \in \operatorname{Fin}\left(m\right),\; \operatorname{matrixPhiRPower}\left(c, l, i, j\right):\operatorname{Equiv}\left(\Sigma_{x:\operatorname{Fin}\left(n\right)}((\operatorname{Word}\left(A, l, i, x\right)\times\operatorname{At}\left(\operatorname{R}\left(c\right), x, j\right))), \Sigma_{y:\operatorname{Fin}\left(m\right)}((\operatorname{At}\left(\operatorname{R}\left(c\right), i, y\right)\times\operatorname{Word}\left(B, l, y, j\right)))\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths.matrixPhiRPower` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

At the incoming and outgoing R boundary use exactly pathAtEquiv(forwardFactors(c)) and its inverse, preserving the whole-factor lexicographic rank. The intervening map is the literal complete phiRPower, the right-to-left iteration of the original one-edge phiR. Intermediate rank transports cancel when composing columns. No new enumeration or endpoint matrix is introduced.

**Definition 1.6 (Synchronous whole-rank conjugation of the complete S sweep).**

$$\forall H \in Type,\; [\operatorname{Group}\left(H\right)][\operatorname{Fintype}\left(H\right)][\operatorname{LinearOrder}\left(H\right)]\forall n \in Nat, m \in Nat, L \in Nat, A \in \operatorname{GroupMat}\left(H, n, n\right), B \in \operatorname{GroupMat}\left(H, m, m\right), c \in \operatorname{Chain}\left(H, A, B, L\right), l \in Nat, i \in \operatorname{Fin}\left(m\right), j \in \operatorname{Fin}\left(n\right),\; \operatorname{matrixPhiSPower}\left(c, l, i, j\right):\operatorname{Equiv}\left(\Sigma_{x:\operatorname{Fin}\left(m\right)}((\operatorname{Word}\left(B, l, i, x\right)\times\operatorname{At}\left(\operatorname{S}\left(c\right), x, j\right))), \Sigma_{y:\operatorname{Fin}\left(n\right)}((\operatorname{At}\left(\operatorname{S}\left(c\right), i, y\right)\times\operatorname{Word}\left(A, l, y, j\right)))\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths.matrixPhiSPower` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Use the identical pathAtEquiv(backwardFactors(c)) rank in every S occurrence before and after the literal reversed-chain phiSPower. The complete word and its endpoints are unchanged. This is the dual synchronous conjugation of the same actual supplied chain.

**Theorem 1.7 (The original matrix-edge R compatibility equation).**

$$\forall H \in Type,\; [\operatorname{Group}\left(H\right)][\operatorname{Fintype}\left(H\right)][\operatorname{LinearOrder}\left(H\right)]\forall n \in Nat, m \in Nat, L \in Nat, A \in \operatorname{GroupMat}\left(H, n, n\right), B \in \operatorname{GroupMat}\left(H, m, m\right), c \in \operatorname{Chain}\left(H, A, B, L\right),\; \forall i \in \operatorname{Fin}\left(n\right), x \in \operatorname{Fin}\left(n\right), y \in \operatorname{Fin}\left(m\right), j \in \operatorname{Fin}\left(m\right), r \in \operatorname{At}\left(\operatorname{R}\left(c\right), i, y\right), s \in \operatorname{At}\left(\operatorname{S}\left(c\right), y, x\right), rp \in \operatorname{At}\left(\operatorname{R}\left(c\right), x, j\right),\; \operatorname{matrixPhiRPower}\left(c, L, i, j, \operatorname{tuple}\left(x, \operatorname{matrixPsi0}\left(c, i, x, \operatorname{tuple}\left(y, r, s\right)\right), rp\right)\right) = \operatorname{tuple}\left(y, r, \operatorname{matrixPsiL}\left(c, y, j, \operatorname{tuple}\left(x, s, rp\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths.matrixPhiRPower_long` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every r,rprime is an actual At(R(c)) edge and s an actual At(S(c)) edge. All occurrences in matrixPsi0,matrixPsiL and matrixPhiRPower use the same whole-fiber ranks. Apply the actual path-level long law and cancel the outgoing rank roundtrip; every independent edge number and label is preserved.

**Theorem 1.8 (The original matrix-edge S compatibility equation).**

$$\forall H \in Type,\; [\operatorname{Group}\left(H\right)][\operatorname{Fintype}\left(H\right)][\operatorname{LinearOrder}\left(H\right)]\forall n \in Nat, m \in Nat, L \in Nat, A \in \operatorname{GroupMat}\left(H, n, n\right), B \in \operatorname{GroupMat}\left(H, m, m\right), c \in \operatorname{Chain}\left(H, A, B, L\right),\; \forall i \in \operatorname{Fin}\left(m\right), x \in \operatorname{Fin}\left(m\right), y \in \operatorname{Fin}\left(n\right), j \in \operatorname{Fin}\left(n\right), r \in \operatorname{At}\left(\operatorname{S}\left(c\right), i, y\right), s \in \operatorname{At}\left(\operatorname{R}\left(c\right), y, x\right), rp \in \operatorname{At}\left(\operatorname{S}\left(c\right), x, j\right),\; \operatorname{matrixPhiSPower}\left(c, L, i, j, \operatorname{tuple}\left(x, \operatorname{matrixPsiL}\left(c, i, x, \operatorname{tuple}\left(y, r, s\right)\right), rp\right)\right) = \operatorname{tuple}\left(y, r, \operatorname{matrixPsi0}\left(c, y, j, \operatorname{tuple}\left(x, s, rp\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths.matrixPhiSPower_long` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The dual law uses the same concrete cumulative R(c),S(c), source A, target B and original length L. In this displayed formula r and rprime are At(S(c)) edges and s is At(R(c)). It follows from the path-level dual law through the exact same S rank; no separately chosen compatible tuple occurs.

**Definition 1.9 (Both long laws at the original concrete tuple).**

$$\forall H \in Type,\; [\operatorname{Group}\left(H\right)][\operatorname{Fintype}\left(H\right)][\operatorname{LinearOrder}\left(H\right)]\forall n \in Nat, m \in Nat, L \in Nat, A \in \operatorname{GroupMat}\left(H, n, n\right), B \in \operatorname{GroupMat}\left(H, m, m\right), c \in \operatorname{Chain}\left(H, A, B, L\right),\; \operatorname{Compatibility}\left(c\right):Prop$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths.Compatibility` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The certificate asserts AR=RB,BS=SA,RS=A^L,SR=B^L and both fully quantified matrix-edge long equations just displayed, with R=R(c),S=S(c) and the four actual equivalences matrixPsi0,matrixPsiL,matrixPhiR,matrixPhiS. Each equivalence supplies both inverse identities. The complete-word sweeps are their synchronous whole-rank conjugations. The certificate has no supplied-law fields or replacement endpoints.

**Theorem 1.10 (The complete same-tuple source compatibility certificate).**

$$\forall H \in Type,\; [\operatorname{Group}\left(H\right)][\operatorname{Fintype}\left(H\right)][\operatorname{LinearOrder}\left(H\right)]\forall n \in Nat, m \in Nat, L \in Nat, A \in \operatorname{GroupMat}\left(H, n, n\right), B \in \operatorname{GroupMat}\left(H, m, m\right), c \in \operatorname{Chain}\left(H, A, B, L\right),\; \operatorname{Compatibility}\left(c\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths.original27_2` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite ordered group and every actual natural group-ring chain c:Chain(H,A,B,L), construct Compatibility(c). Its four algebraic equations are the cumulative equations of that chain. Both long laws are proved for every typed endpoint and every numbered input by the literal G34 construction and its reverse, using the same whole-fiber R/S ranks. Zero length, empty coefficient fibers and varying or zero dimensions remain in the universal telescope.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths.Compatibility`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths.matrixPhiRPower`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths.matrixPhiRPower_long`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths.matrixPhiSPower`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths.matrixPhiSPower_long`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths.original27_2`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths.phiRPower_long`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths.phiSPower_long`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths.rightBoundaryPath`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths.wordFactorArray_right`
- Dependency: [D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/TriangleRecovery](CountedGroupChainPaths/TriangleRecovery.md)
