# Quantitative exchange traces

## Abstract

Controlled Type traces retain actual factors, tags and all node controls at exact length 2m minus one.

All dimensions n, k and the lag m range over natural numbers. A and B are square natural count matrices of orders n and k; R has shape n by k and S has shape k by n. Essential means that every row and every column has a nonzero entry. The original input consists of essential A and B, positive lag m, and four numbered equivalence families: phiR(i,z): EdgePair(A,R,i,z) ≃ EdgePair(R,B,i,z); phiS(t,w): EdgePair(B,S,t,w) ≃ EdgePair(S,A,t,w); psiA(i,j): EdgePair(R,S,i,j) ≃ FinitePath(A,m,i,j); psiB(t,z): EdgePair(S,R,t,z) ≃ FinitePath(B,m,t,z). Both original BalancedA(phiR,phiS,psiA) and BalancedB(phiR,phiS,psiB) identities are required. NumberedEdgePairEquiv and NumberedPathEquiv in the displays abbreviate precisely these indexed families. No quotient control, factor bound or resulting trace is supplied as an input.

**Definition 1.1 (Ordinary and diamond bounds).**

$$\forall q \in \mathit{Nat}, bound \in \mathit{Nat}, tag \in \mathit{Bool},\; \operatorname{factorBound}\left(q, \mathit{bound}, \mathit{tag}\right) = \operatorname{ifThenElse}\left(\mathit{tag}, \operatorname{max}\left(q, \mathit{bound}\right), \operatorname{max}\left(1, \mathit{bound}\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/OriginalQuantitativeExchangeChain.factorBound` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A true tag marks the diamond step and gives max(q,bound); a false tag marks an ordinary response step and gives max(1,bound).

**Definition 1.2 (A dependent data trace).**

$$\forall q \in \mathit{Nat}, bound \in \mathit{Nat}, a \in \mathit{Nat}, b \in \mathit{Nat}, X \in \operatorname{CountMat}\left(a, a\right), Y \in \operatorname{CountMat}\left(b, b\right), length \in \mathit{Nat},\; \operatorname{TypeTrace}\left(q, \mathit{bound}, X, Y, \mathit{length}\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/OriginalQuantitativeExchangeChain.ControlledChain` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

ControlledChain q bound X Y length is an inductive Type. A nil node stores X and its NodeControl, has endpoint X and length zero. A cons stores the actual rectangular U and V, its Boolean tag, both entry bounds, NodeControl(U V), and a tail from V U to the endpoint. The source is U V and the length is tail length plus one. Thus the final node remains controlled even for an empty trace.

**Theorem 1.3 (Erasing the controls).**

$$\forall q \in \mathit{Nat}, bound \in \mathit{Nat}, a \in \mathit{Nat}, b \in \mathit{Nat}, X \in \operatorname{CountMat}\left(a, a\right), Y \in \operatorname{CountMat}\left(b, b\right), length \in \mathit{Nat}, trace \in \operatorname{ControlledChain}\left(q, \mathit{bound}, X, Y, \mathit{length}\right),\; \operatorname{ExchangeChain}\left(X, Y, \mathit{length}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/OriginalQuantitativeExchangeChain.erase` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Erasure recursively uses each stored U and V to construct the ordinary ExchangeChain. It discards the controls and tags while keeping the factor matrices on the same sequence of exchanges.

**Theorem 1.4 (The source node is controlled).**

$$\forall q \in \mathit{Nat}, bound \in \mathit{Nat}, a \in \mathit{Nat}, b \in \mathit{Nat}, X \in \operatorname{CountMat}\left(a, a\right), Y \in \operatorname{CountMat}\left(b, b\right), length \in \mathit{Nat}, trace \in \operatorname{ControlledChain}\left(q, \mathit{bound}, X, Y, \mathit{length}\right),\; \operatorname{NodeControl}\left(X, q, \mathit{bound}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/OriginalQuantitativeExchangeChain.sourceControl` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Case analysis reads the control stored by nil or cons. Reversal uses the tail source control when adjoining the reversed last exchange.

**Definition 1.5 (Concatenating actual traces).**

$$\forall q \in \mathit{Nat}, bound \in \mathit{Nat}, a \in \mathit{Nat}, b \in \mathit{Nat}, c \in \mathit{Nat}, X \in \operatorname{CountMat}\left(a, a\right), Y \in \operatorname{CountMat}\left(b, b\right), Z \in \operatorname{CountMat}\left(c, c\right), l1 \in \mathit{Nat}, l2 \in \mathit{Nat}, left \in \operatorname{ControlledChain}\left(q, \mathit{bound}, X, Y, \mathit{l1}\right), right \in \operatorname{ControlledChain}\left(q, \mathit{bound}, Y, Z, \mathit{l2}\right),\; \operatorname{ControlledChain}\left(q, \mathit{bound}, X, Z, \mathit{l1} + \mathit{l2}\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/OriginalQuantitativeExchangeChain.trans` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The structurally recursive local function traverses the left trace, retaining each factor pair, tag and control, and replaces its nil tail by the right trace. Length transport uses addition identities.

**Definition 1.6 (Reversing actual traces).**

$$\forall q \in \mathit{Nat}, bound \in \mathit{Nat}, a \in \mathit{Nat}, b \in \mathit{Nat}, X \in \operatorname{CountMat}\left(a, a\right), Y \in \operatorname{CountMat}\left(b, b\right), length \in \mathit{Nat}, trace \in \operatorname{ControlledChain}\left(q, \mathit{bound}, X, Y, \mathit{length}\right),\; \operatorname{ControlledChain}\left(q, \mathit{bound}, Y, X, \mathit{length}\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/OriginalQuantitativeExchangeChain.reverse` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Reversal recursively reverses the tail and appends the exchanged pair (V,U) with its original tag and swapped bounds. This reverses tag order, preserves length and gives the original source as the final controlled node.

**Definition 1.7 (Transposing actual traces).**

$$\forall q \in \mathit{Nat}, bound \in \mathit{Nat}, a \in \mathit{Nat}, b \in \mathit{Nat}, X \in \operatorname{CountMat}\left(a, a\right), Y \in \operatorname{CountMat}\left(b, b\right), length \in \mathit{Nat}, trace \in \operatorname{ControlledChain}\left(q, \mathit{bound}, X, Y, \mathit{length}\right),\; \operatorname{ControlledChain}\left(q, \mathit{bound}, \operatorname{transpose}\left(X\right), \operatorname{transpose}\left(Y\right), \mathit{length}\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/OriginalQuantitativeExchangeChain.transpose` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Transpose recursively sends (U,V) to (V transpose,U transpose) and keeps tag order. It exchanges the row and column essentiality clauses of each node control. Concatenation, reversal and transpose recurse on the uncast tail through local indexed functions; their definitions use structural recursion.

**Theorem 1.8 (The controlled fixed-lag chain).**

$$\forall n \in \mathit{Nat}, k \in \mathit{Nat}, m \in \mathit{Nat}, A \in \operatorname{CountMat}\left(n, n\right), B \in \operatorname{CountMat}\left(k, k\right), R \in \operatorname{CountMat}\left(n, k\right), S \in \operatorname{CountMat}\left(k, n\right),\; \forall c \in \operatorname{CompatibleCertificate}\left(A, B, R, S, m\right),\; \operatorname{Nonempty}\left(\operatorname{ControlledChain}\left(\operatorname{cardEdge}\left(R\right), \operatorname{max}\left(\operatorname{cardEdge}\left(A\right), \operatorname{cardEdge}\left(B\right)\right), A, B, 2 \cdot m - 1\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/OriginalQuantitativeExchangeChain.compatibleControlledChain` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For m≥2, compose the reversed left response leg, the one-step diamond and the transposed right leg. The diamond uses exactly the D and both product equations supplied by square_diamond_controls; its bound supplies the actual middle V bound. For m=1, simultaneously renumber the two endpoints of that same diamond. The lengths total 2m−1. No positive dimension is added.

**Theorem 1.9 (Quantitative traces from the original maps).**

$$\forall n \in \mathit{Nat}, k \in \mathit{Nat}, m \in \mathit{Nat}, A \in \operatorname{CountMat}\left(n, n\right), B \in \operatorname{CountMat}\left(k, k\right), R \in \operatorname{CountMat}\left(n, k\right), S \in \operatorname{CountMat}\left(k, n\right),\; \forall phiR \in \operatorname{NumberedEdgePairEquiv}\left(A, R, R, B\right), phiS \in \operatorname{NumberedEdgePairEquiv}\left(B, S, S, A\right), psiA \in \operatorname{NumberedPathEquiv}\left(R, S, A, m\right), psiB \in \operatorname{NumberedPathEquiv}\left(S, R, B, m\right),\; \left(\operatorname{Essential}\left(A\right) \land \left(\operatorname{Essential}\left(B\right) \land \left(1 \le m \land \left(\operatorname{BalancedA}\left(\mathit{phiR}, \mathit{phiS}, \mathit{psiA}\right) \land \operatorname{BalancedB}\left(\mathit{phiR}, \mathit{phiS}, \mathit{psiB}\right)\right)\right)\right)\right) \Rightarrow \left(\left(\operatorname{cardEdge}\left(R\right) = \operatorname{sumEntries}\left(R\right) \land \left(\operatorname{max}\left(n, k\right) \le \operatorname{cardEdge}\left(R\right) \land \operatorname{cardEdge}\left(R\right) \le n \cdot k \cdot \operatorname{powerMaximum}\left(A, m\right)\right)\right) \land \left(\exists trace \in \operatorname{ControlledChain}\left(\operatorname{cardEdge}\left(R\right), \operatorname{max}\left(\operatorname{cardEdge}\left(A\right), \operatorname{cardEdge}\left(B\right)\right), A, B, 2 \cdot m - 1\right),\; \operatorname{Nonempty}\left(\operatorname{ErasureFiber}\left(\mathit{trace}\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/OriginalQuantitativeExchangeChain.originalBalancedQuantitativeExchangeChain` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The original four maps and both balance identities construct the compatible certificate internally. One obtains q=sumEntries(R), max(n,k)≤q≤n k powerMaximum(A,m), and an actual trace in ControlledChain(q,bound,A,B,2m−1). ErasureFiber(trace) is the subtype of ordinary ExchangeChain values equal to trace.erase; it is inhabited by trace.erase itself. Thus the ordinary chain and the controlled trace use the same factor data.

The single and single_reindex constructors build the one actual diamond step, using both endpoint controls and both factor equations. controlled_response_chain_to recursively uses the original incomingResponseU and incomingResponseV at every response depth and allows the prescribed final numbering. These constructions preserve empty dimensions and the nil terminal control. They do not supply an executable finite-table exporter, independent forgetting depths, a minimum-lag characterization or further original sections beyond this fixed-lag result.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Coding/OriginalQuantitativeExchangeChain.ControlledChain`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/OriginalQuantitativeExchangeChain.compatibleControlledChain`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/OriginalQuantitativeExchangeChain.erase`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/OriginalQuantitativeExchangeChain.factorBound`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/OriginalQuantitativeExchangeChain.originalBalancedQuantitativeExchangeChain`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/OriginalQuantitativeExchangeChain.reverse`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/OriginalQuantitativeExchangeChain.sourceControl`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/OriginalQuantitativeExchangeChain.trans`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/OriginalQuantitativeExchangeChain.transpose`
- Dependency: [D5/S3/ConceptDynamics/Coding/OriginalResponseControls](OriginalResponseControls.md)
