# Quantitative response controls

## Abstract

Original balanced maps control quotient essentiality, node orders and the same first diamond factors.

All dimensions n, k and the lag m range over natural numbers. A and B are square natural count matrices of orders n and k; R has shape n by k and S has shape k by n. Essential means that every row and every column has a nonzero entry. The original input consists of essential A and B, positive lag m, and four numbered equivalence families: phiR(i,z): EdgePair(A,R,i,z) ≃ EdgePair(R,B,i,z); phiS(t,w): EdgePair(B,S,t,w) ≃ EdgePair(S,A,t,w); psiA(i,j): EdgePair(R,S,i,j) ≃ FinitePath(A,m,i,j); psiB(t,z): EdgePair(S,R,t,z) ≃ FinitePath(B,m,t,z). Both original BalancedA(phiR,phiS,psiA) and BalancedB(phiR,phiS,psiB) identities are required. NumberedEdgePairEquiv and NumberedPathEquiv in the displays abbreviate precisely these indexed families. No quotient control, factor bound or resulting trace is supplied as an input.

**Theorem 1.1 (The balanced sweep identity).**

$$\forall n \in \mathit{Nat}, k \in \mathit{Nat}, m \in \mathit{Nat}, A \in \operatorname{CountMat}\left(n, n\right), B \in \operatorname{CountMat}\left(k, k\right), R \in \operatorname{CountMat}\left(n, k\right), S \in \operatorname{CountMat}\left(k, n\right),\; \forall phiR \in \operatorname{NumberedEdgePairEquiv}\left(A, R, R, B\right), phiS \in \operatorname{NumberedEdgePairEquiv}\left(B, S, S, A\right), psiA \in \operatorname{NumberedPathEquiv}\left(R, S, A, m\right), psiB \in \operatorname{NumberedPathEquiv}\left(S, R, B, m\right),\; \left(\operatorname{Essential}\left(A\right) \land \left(\operatorname{Essential}\left(B\right) \land \left(1 \le m \land \left(\operatorname{BalancedA}\left(\mathit{phiR}, \mathit{phiS}, \mathit{psiA}\right) \land \operatorname{BalancedB}\left(\mathit{phiR}, \mathit{phiS}, \mathit{psiB}\right)\right)\right)\right)\right) \Rightarrow \left(\forall i \in \operatorname{Fin}\left(n\right), j \in \operatorname{Fin}\left(n\right), z \in \operatorname{Fin}\left(k\right), alpha \in \operatorname{FinitePath}\left(A, m, i, j\right), r \in \operatorname{Fin}\left(\operatorname{entry}\left(R, j, z\right)\right),\; \operatorname{sweep}\left(\mathit{phiR}, \mathit{alpha}, r\right) = \operatorname{balancedBoundary}\left(\mathit{psiA}, \mathit{psiB}, \mathit{alpha}, r\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/OriginalResponseControls.balanced_sweep` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For alpha from i to j and a numbered R edge r from j to z, write psiA(i,j)⁻¹(alpha)=(u,r₀,s₀). The balancedBoundary expression is the dependent triple (u,r₀,psiB(u,z)(j,s₀,r)). The sweep along phiR equals this triple. Row essentiality and the path equivalences supply the auxiliary numbered edges, and the two balance identities identify the boundary and tail. This reconstructs the compatibility field used below.

**Definition 1.2 (Controls on an actual node).**

$$\forall r \in \mathit{Nat}, X \in \operatorname{CountMat}\left(r, r\right), q \in \mathit{Nat}, bound \in \mathit{Nat},\; \operatorname{NodeControl}\left(X, q, \mathit{bound}\right) = \left(r \le q \land \left(\operatorname{Essential}\left(X\right) \land \left(\forall i \in \operatorname{Fin}\left(r\right), j \in \operatorname{Fin}\left(r\right),\; \operatorname{entry}\left(X, i, j\right) \le \mathit{bound}\right)\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/OriginalResponseControls.NodeControl` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

NodeControl(X,q,bound) consists of order(X) ≤ q, a nonzero entry in every row, a nonzero entry in every column, and X(i,j) ≤ bound for every entry. The two essentiality clauses are separate obligations. When the order is zero their universal clauses are vacuous; no inhabitant is chosen.

**Definition 1.3 (Controls at every response depth).**

$$\forall p \in \mathit{Nat}, A \in \operatorname{CountMat}\left(p, p\right), Q \in \mathit{Type}, L \in \operatorname{IncomingLift}\left(A, Q\right), q \in \mathit{Nat}, bound \in \mathit{Nat},\; \operatorname{ResponseControl}\left(L, q, \mathit{bound}\right) = \left(\operatorname{AllNumberedResponseNodesControlled}\left(L, q, \mathit{bound}\right) \land \operatorname{AllNumberedResponseFactorsControlled}\left(L, \operatorname{max}\left(1, \mathit{bound}\right)\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/OriginalResponseControls.ResponseControl` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every natural depth d, every natural r, and every equivalence e: Quotient(L.response d) ≃ Fin r, the reindexed incomingResponseMatrix has NodeControl(q,bound). For every additional numbering f at d+1, set U=reindex(e,f,incomingResponseU L d) and V=reindex(f,e,incomingResponseV L d). The two numbered matrices equal U V and V U respectively, and each entry of both U and V is at most max(1,bound). These are the actual fiber-count and membership matrices.

**Theorem 1.4 (Essential and bounded response quotients).**

$$\forall n \in \mathit{Nat}, k \in \mathit{Nat}, m \in \mathit{Nat}, A \in \operatorname{CountMat}\left(n, n\right), B \in \operatorname{CountMat}\left(k, k\right), R \in \operatorname{CountMat}\left(n, k\right), S \in \operatorname{CountMat}\left(k, n\right),\; \forall c \in \operatorname{CompatibleCertificate}\left(A, B, R, S, m\right),\; \operatorname{ResponseControl}\left(\operatorname{squareIncomingLift}\left(c\right), \operatorname{cardEdge}\left(R\right), \operatorname{max}\left(\operatorname{cardEdge}\left(A\right), \operatorname{cardEdge}\left(B\right)\right)\right) \land \left(\operatorname{ResponseControl}\left(\operatorname{squareOutgoingLift}\left(c\right), \operatorname{cardEdge}\left(R\right), \operatorname{max}\left(\operatorname{cardEdge}\left(A\right), \operatorname{cardEdge}\left(B\right)\right)\right) \land \operatorname{AllTransposedOutgoingNodesControlled}\left(c, \operatorname{cardEdge}\left(R\right), \operatorname{max}\left(\operatorname{cardEdge}\left(A\right), \operatorname{cardEdge}\left(B\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/OriginalResponseControls.square_response_controls` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any compatible certificate c, the incoming and outgoing square lifts satisfy ResponseControl with q=card(Edge R) and bound=max(card(Edge A),card(Edge B)). Every numbered outgoing quotient, after transpose, has the same NodeControl. To prove essentiality at arbitrary depth, an outgoing lifted edge from a representative supplies an inhabited incoming response fiber; fiber-cardinality transport moves the witness to the chosen quotient representative. For a prescribed target class, an incoming base edge supplies a fiber member. The actual square graph supplies these lift witnesses. Cardinal surjection and subtype bounds then give the order and entry bounds.

**Theorem 1.5 (The square graph order).**

$$\forall n \in \mathit{Nat}, k \in \mathit{Nat}, m \in \mathit{Nat}, A \in \operatorname{CountMat}\left(n, n\right), B \in \operatorname{CountMat}\left(k, k\right), R \in \operatorname{CountMat}\left(n, k\right), S \in \operatorname{CountMat}\left(k, n\right),\; \forall c \in \operatorname{CompatibleCertificate}\left(A, B, R, S, m\right),\; \operatorname{cardEdge}\left(R\right) = \operatorname{sumEntries}\left(R\right) \land \operatorname{max}\left(n, k\right) \le \operatorname{cardEdge}\left(R\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/OriginalResponseControls.square_order_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Numbered R edges correspond bijectively to the dependent sum over i,j of Fin(R(i,j)), so q is the sum of all R entries. Surjectivity of the original source and target projections gives n ≤ q and k ≤ q. These cardinal identities retain both projections.

**Definition 1.6 (The maximum power entry).**

$$\forall n \in \mathit{Nat}, A \in \operatorname{CountMat}\left(n, n\right), m \in \mathit{Nat},\; \operatorname{powerMaximum}\left(A, m\right) = \operatorname{finiteSupPowerEntries}\left(A, m\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/OriginalResponseControls.powerMaximum` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

powerMaximum(A,m) is Finset.univ.sup of (A^m)(i,j) over Fin n × Fin n. Its value is zero for n=0. For positive order it is the ordinary maximum of the entries of A^m.

**Theorem 1.7 (Counting numbered paths).**

$$\forall n \in \mathit{Nat}, A \in \operatorname{CountMat}\left(n, n\right), d \in \mathit{Nat}, i \in \operatorname{Fin}\left(n\right), j \in \operatorname{Fin}\left(n\right),\; \operatorname{Finite}\left(\operatorname{FinitePath}\left(A, d, i, j\right)\right) \land \operatorname{NatCard}\left(\operatorname{FinitePath}\left(A, d, i, j\right)\right) = \operatorname{entry}\left(\operatorname{power}\left(A, d\right), i, j\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/OriginalResponseControls.numbered_path_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The finite numbered length-d paths from i to j have cardinality (A^d)(i,j), also for d=0 and empty dimensions. At zero length the fiber is a singleton exactly when the endpoints agree. At a successor length, split off the first numbered edge and count the dependent sum over its target. This is the existing counting argument used by the square-order bound.

**Theorem 1.8 (The individual factor bound).**

$$\forall n \in \mathit{Nat}, k \in \mathit{Nat}, m \in \mathit{Nat}, A \in \operatorname{CountMat}\left(n, n\right), B \in \operatorname{CountMat}\left(k, k\right), R \in \operatorname{CountMat}\left(n, k\right), S \in \operatorname{CountMat}\left(k, n\right),\; \left(\operatorname{RowEssential}\left(B\right) \land \left(\operatorname{HasNumberedPathEquiv}\left(R, S, A, m\right) \land \operatorname{HasNumberedPathEquiv}\left(S, R, B, m\right)\right)\right) \Rightarrow \left(\forall i \in \operatorname{Fin}\left(n\right), j \in \operatorname{Fin}\left(k\right),\; \operatorname{entry}\left(R, i, j\right) \le \operatorname{powerMaximum}\left(A, m\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/OriginalResponseControls.factor_entry_upper` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

RowEssential(B) means a nonzero entry in every row of B. For arbitrary R and S with the two displayed numbered path equivalences, each entry R(i,j) is bounded by powerMaximum(A,m). Recover an S edge from the inverse B-path bijection and inject the R fiber into the corresponding A-path fiber. Counting paths and taking the maximum proves the inequality. This factors the existing square_order_upper argument so that the same bound also supplies the unrestricted finite search.

**Theorem 1.9 (The quantitative square-order bound).**

$$\forall n \in \mathit{Nat}, k \in \mathit{Nat}, m \in \mathit{Nat}, A \in \operatorname{CountMat}\left(n, n\right), B \in \operatorname{CountMat}\left(k, k\right), R \in \operatorname{CountMat}\left(n, k\right), S \in \operatorname{CountMat}\left(k, n\right),\; \forall c \in \operatorname{CompatibleCertificate}\left(A, B, R, S, m\right),\; \operatorname{cardEdge}\left(R\right) \le n \cdot k \cdot \operatorname{powerMaximum}\left(A, m\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/OriginalResponseControls.square_order_upper` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Choose a numbered S edge leaving each target vertex. Pairing it with an R edge and applying psiA injects that R fiber into a length-m A-path fiber. The standard path count is (A^m)(i,l), hence each R entry is at most powerMaximum(A,m). Summing over n times k entries gives the displayed bound, including empty dimensions.

**Theorem 1.10 (Bounds on the same diamond factors).**

$$\forall n \in \mathit{Nat}, k \in \mathit{Nat}, m \in \mathit{Nat}, A \in \operatorname{CountMat}\left(n, n\right), B \in \operatorname{CountMat}\left(k, k\right), R \in \operatorname{CountMat}\left(n, k\right), S \in \operatorname{CountMat}\left(k, n\right),\; \forall c \in \operatorname{CompatibleCertificate}\left(A, B, R, S, m\right),\; \exists D \in \operatorname{CountMat}\left(\operatorname{rightFirstOrder}\left(c\right), \operatorname{leftFirstOrder}\left(c\right)\right),\; \operatorname{leftFirstMatrix}\left(c\right) = \operatorname{intersection}\left(c\right) \cdot D \land \left(\operatorname{rightFirstMatrix}\left(c\right) = D \cdot \operatorname{intersection}\left(c\right) \land \left(\operatorname{EntryBound}\left(\operatorname{intersection}\left(c\right), \operatorname{max}\left(\operatorname{cardEdge}\left(R\right), \operatorname{max}\left(\operatorname{cardEdge}\left(A\right), \operatorname{cardEdge}\left(B\right)\right)\right)\right) \land \operatorname{EntryBound}\left(D, \operatorname{max}\left(\operatorname{cardEdge}\left(R\right), \operatorname{max}\left(\operatorname{cardEdge}\left(A\right), \operatorname{cardEdge}\left(B\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/OriginalResponseControls.square_diamond_controls` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let IL and IJ be first-left column membership and first-right row membership, SL and SJ their representative selectors, and P=IL IJ. The leftFirstMatrix is IL C SL and rightFirstMatrix is SJ C IJ for C=c.squareMatrix. FirstResponseDiamond supplies one D satisfying IL C SL=P D and SJ C IJ=D P. Every P entry is at most q. For a column h of P, choose u=firstRightRep(h) and g=firstLeftClass(u). The u summand gives P(g,h)≥1, so D(h,f)≤P(g,h)D(h,f)≤(P D)(g,f)≤bound≤max(q,bound). The conclusion bounds this same D with both factor equations. It does not assert a representative-entry formula for D.

**Theorem 1.11 (Controls from the original four maps).**

$$\forall n \in \mathit{Nat}, k \in \mathit{Nat}, m \in \mathit{Nat}, A \in \operatorname{CountMat}\left(n, n\right), B \in \operatorname{CountMat}\left(k, k\right), R \in \operatorname{CountMat}\left(n, k\right), S \in \operatorname{CountMat}\left(k, n\right),\; \forall phiR \in \operatorname{NumberedEdgePairEquiv}\left(A, R, R, B\right), phiS \in \operatorname{NumberedEdgePairEquiv}\left(B, S, S, A\right), psiA \in \operatorname{NumberedPathEquiv}\left(R, S, A, m\right), psiB \in \operatorname{NumberedPathEquiv}\left(S, R, B, m\right),\; \left(\operatorname{Essential}\left(A\right) \land \left(\operatorname{Essential}\left(B\right) \land \left(1 \le m \land \left(\operatorname{BalancedA}\left(\mathit{phiR}, \mathit{phiS}, \mathit{psiA}\right) \land \operatorname{BalancedB}\left(\mathit{phiR}, \mathit{phiS}, \mathit{psiB}\right)\right)\right)\right)\right) \Rightarrow \left(\left(\operatorname{cardEdge}\left(R\right) = \operatorname{sumEntries}\left(R\right) \land \left(\operatorname{max}\left(n, k\right) \le \operatorname{cardEdge}\left(R\right) \land \operatorname{cardEdge}\left(R\right) \le n \cdot k \cdot \operatorname{powerMaximum}\left(A, m\right)\right)\right) \land \operatorname{BothResponseLegControls}\left(\operatorname{balancedCertificate}\left(A, B, R, S, m, \mathit{phiR}, \mathit{phiS}, \mathit{psiA}, \mathit{psiB}\right), \operatorname{cardEdge}\left(R\right), \operatorname{max}\left(\operatorname{cardEdge}\left(A\right), \operatorname{cardEdge}\left(B\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/OriginalResponseControls.originalBalancedResponseControls` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Construct c internally with the original matrices, positive lag, essentiality and numbered maps; balanced_sweep provides its compatibility equation. The result gives q=sumEntries(R), max(n,k)≤q≤n k powerMaximum(A,m), both ResponseControl clauses, and all transposed outgoing NodeControls. BothResponseLegControls abbreviates exactly these three response conclusions. The certificate and these conclusions are derived from the original telescope.

The quotient-fiber argument and the same-D inequality use the original numbered square construction. Path counting, cardinal transport, the square graph projections and the unbounded first diamond are supplied by the imported results and mathlib. The statement concerns fixed positive lag; independent least forgetting depths and a literal representative formula for D are separate questions.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Coding/OriginalResponseControls.NodeControl`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/OriginalResponseControls.ResponseControl`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/OriginalResponseControls.balanced_sweep`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/OriginalResponseControls.factor_entry_upper`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/OriginalResponseControls.numbered_path_count`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/OriginalResponseControls.originalBalancedResponseControls`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/OriginalResponseControls.powerMaximum`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/OriginalResponseControls.square_diamond_controls`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/OriginalResponseControls.square_order_identity`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/OriginalResponseControls.square_order_upper`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/OriginalResponseControls.square_response_controls`
- Dependency: [D5/S3/ConceptDynamics/Coding/CompatibleResponseForgettingBound](CompatibleResponseForgettingBound.md)
- Dependency: [D5/S3/ConceptDynamics/Coding/OriginalAlignedBalanced](OriginalAlignedBalanced.md)
