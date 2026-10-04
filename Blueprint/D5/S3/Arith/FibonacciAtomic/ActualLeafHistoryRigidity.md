# Native Leaf-History Geometry and Literal Context Recovery

## Abstract

Actual third Fibonacci images admit complete node classification, five-row leaf forcing, and literal frontier recovery.

T is FreeMagma Bool: nonempty finite ordered full binary trees with true labelled alpha and false labelled beta. The original substitution sends alpha to beta, beta to pair(beta,alpha), and preserves ordered pairs. R is its actual third iterate. Positive(P) means P=R(Q) for some Q in T. Word is List Bool, with false left, true right and the empty root included. read(u,P) is the native four-valued reply alpha, beta, branch or absent, and Leaves(P) enumerates actual leaf words. E=pair(beta,alpha), A=pair(E,beta), C=pair(A,E). n is native leaf count.

**Definition 1.1 (Arbitrary finite histories).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ActualLeafHistoryRigidity.LeafHistory`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ActualLeafHistoryRigidity.LeafHistory` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

History is a finite list of pairs (word,reply). Repeated requests and all four reply types are allowed.

**Definition 1.2 (Positive leaf-only comparison).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ActualLeafHistoryRigidity.Compatible`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ActualLeafHistoryRigidity.Compatible` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

compatible(H,P) means Positive(P) and, for each (u,y) in H with y equal to alpha or beta, read(u,P)=y. Branch and absent pairs impose no constraint.

**Definition 1.3 (The two literal block kinds).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ActualLeafHistoryRigidity.BlockKind`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ActualLeafHistoryRigidity.BlockKind` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Kind has exactly a and c.

tree(a)=A and tree(c)=C. A block d is a pair (root(d),kind(d)) in Word times Kind.

**Definition 1.4 (The exact five-row leaf decoder).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ActualLeafHistoryRigidity.decodeBlock`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ActualLeafHistoryRigidity.decodeBlock` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

decode(wR,beta)=some(w,a); decode(wLL,beta)=some(w,a); decode(wLR,alpha)=some(w,a); decode(wRL,beta)=some(w,c); decode(wRR,alpha)=some(w,c). All other pairs decode to none. The decoder examines the reversed address, so the beta R row also includes depth-one reports.

**Definition 1.5 (History blocks as a finite set).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ActualLeafHistoryRigidity.forcedBlocks`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ActualLeafHistoryRigidity.forcedBlocks` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

blocks(H) is the finite-set view of filterMap(decode,H). Repeated blocks are retained once. Only leaf replies have nonempty decoded values.

**Definition 1.6 (Actual alpha addresses).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ActualLeafHistoryRigidity.alphaLeaves`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ActualLeafHistoryRigidity.alphaLeaves` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

alpha(P) filters the actual finite leaf-address set by read(u,P)=alpha.

**Definition 1.7 (Covered alpha union).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ActualLeafHistoryRigidity.gamma`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ActualLeafHistoryRigidity.gamma` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

gamma(H) is the union over d in blocks(H) of root(d) prefixed alpha addresses of tree(kind(d)). For a it contributes root(d)LR, and for c it contributes root(d)LLR and root(d)RR. This is a set union; overlapping contributions count once.

**Definition 1.8 (Reference residual).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ActualLeafHistoryRigidity.uncovered`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ActualLeafHistoryRigidity.uncovered` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

unc(H,P)=alpha(P) minus gamma(H).

**Definition 1.9 (Finite ordered literal output contexts).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ActualLeafHistoryRigidity.OutputContext`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ActualLeafHistoryRigidity.OutputContext` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Context has constructors hole, left(J,R), and right(L,J), where L and R are actual native output trees.

plug(hole,X)=X; plug(left(J,R),X)=pair(plug(J,X),R); plug(right(L,J),X)=pair(L,plug(J,X)).

hole(hole) is empty; hole(left(J,R))=L hole(J); hole(right(L,J))=R hole(J).

outside(hole)=0; outside(left(J,R))=outside(J)+n(R); outside(right(L,J))=n(L)+outside(J).

**Definition 1.10 (Actual subtree navigation).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ActualLeafHistoryRigidity.subtree`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ActualLeafHistoryRigidity.subtree` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

sub(empty,P)=some(P); crossing an atomic leaf at a nonempty word gives none; L and R choose the corresponding ordered child.

**Definition 1.11 (Complete canonical block offset table).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ActualLeafHistoryRigidity.BlockOffset`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ActualLeafHistoryRigidity.BlockOffset` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

offset(true,z,Y) lists precisely (empty,A),(L,E),(LL,beta),(LR,alpha),(R,beta). offset(false,z,Y) lists precisely (empty,C),(L,A),(LL,E),(LLL,beta),(LLR,alpha),(LR,beta),(R,E),(RL,beta),(RR,alpha).

**Definition 1.12 (Preimage branch or canonical leaf block).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ActualLeafHistoryRigidity.ImagePosition`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ActualLeafHistoryRigidity.ImagePosition` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

position(Q,u,Y) means either sub(u,Q)=some(pair(q,r)) and Y=pair(R(q),R(r)), or there are v,b,z with sub(v,Q)=some(atom(b)), u=v concat z, and offset(b,z,Y).

concat is ordered word concatenation; prefix is ordinary word prefix. some and none are Option constructors, atom(b) is the native labelled leaf, reply(true)=alpha and reply(false)=beta. nav(z) is the function Y mapped to sub(z,Y), and bind is Option.bind. The theorem's read cases are separated into none and some conditions below. All displayed quantifiers range over the native objects just defined.

**Theorem 1.13 (Complete Address and History Geometry).**

$$(\forall Q: T, (\forall u: \operatorname{Word}\left(\right), (\forall Y: T, ((\operatorname{sub}\left(u, \operatorname{R}\left(Q\right)\right) = \operatorname{some}\left(Y\right)) \iff (\operatorname{position}\left(Q, u, Y\right)))))) \land (\forall P: T, ((\operatorname{Positive}\left(P\right)) \implies (\forall u: \operatorname{Word}\left(\right), (\forall Y: T, ((\operatorname{sub}\left(u, P\right) = \operatorname{some}\left(Y\right)) \implies (((\operatorname{n}\left(Y\right) = 2) \implies (Y = E)) \land ((\operatorname{n}\left(Y\right) = 3) \implies (Y = A)))))))) \land (\forall P: T, ((\operatorname{Positive}\left(P\right)) \implies (\forall w: \operatorname{Word}\left(\right), (((\operatorname{read}\left(\operatorname{concat}\left(w, [R]\right), P\right) = \operatorname{beta}\left(\right)) \implies (\operatorname{sub}\left(w, P\right) = \operatorname{some}\left(A\right))) \land ((\operatorname{read}\left(\operatorname{concat}\left(w, [L, L]\right), P\right) = \operatorname{beta}\left(\right)) \implies (\operatorname{sub}\left(w, P\right) = \operatorname{some}\left(A\right))) \land ((\operatorname{read}\left(\operatorname{concat}\left(w, [L, R]\right), P\right) = \operatorname{alpha}\left(\right)) \implies (\operatorname{sub}\left(w, P\right) = \operatorname{some}\left(A\right))) \land ((\operatorname{read}\left(\operatorname{concat}\left(w, [R, L]\right), P\right) = \operatorname{beta}\left(\right)) \implies (\operatorname{sub}\left(w, P\right) = \operatorname{some}\left(C\right))) \land ((\operatorname{read}\left(\operatorname{concat}\left(w, [R, R]\right), P\right) = \operatorname{alpha}\left(\right)) \implies (\operatorname{sub}\left(w, P\right) = \operatorname{some}\left(C\right))))))) \land (\forall P: T, ((\operatorname{Positive}\left(P\right)) \implies (\forall u: \operatorname{Word}\left(\right), (\forall r: \operatorname{Reply}\left(\right), ((((r = \operatorname{alpha}\left(\right)) \lor (r = \operatorname{beta}\left(\right))) \land (\operatorname{read}\left(u, P\right) = r)) \implies (\exists d: \operatorname{Block}\left(\right), (((\operatorname{decode}\left(u, r\right) = \operatorname{some}\left(d\right)) \land (\operatorname{sub}\left(\operatorname{root}\left(d\right), P\right) = \operatorname{some}\left(\operatorname{tree}\left(\operatorname{kind}\left(d\right)\right)\right))) \land (\forall q: \operatorname{Block}\left(\right), (((\operatorname{decode}\left(u, r\right) = \operatorname{some}\left(q\right)) \land (\operatorname{sub}\left(\operatorname{root}\left(q\right), P\right) = \operatorname{some}\left(\operatorname{tree}\left(\operatorname{kind}\left(q\right)\right)\right))) \implies (q = d)))))))))) \land (\forall H: \operatorname{History}\left(\right), (\forall P: T, ((\operatorname{compatible}\left(H, P\right)) \implies ((\forall d: \operatorname{Block}\left(\right), ((d \in \operatorname{blocks}\left(H\right)) \implies (\operatorname{sub}\left(\operatorname{root}\left(d\right), P\right) = \operatorname{some}\left(\operatorname{tree}\left(\operatorname{kind}\left(d\right)\right)\right)))) \land (\operatorname{subset}\left(\operatorname{gamma}\left(H\right), \operatorname{alpha}\left(P\right)\right)))))) \land (\forall P: T, (\forall u: \operatorname{Word}\left(\right), (\forall v: \operatorname{Word}\left(\right), (\forall S: T, (\forall Z: T, ((((S = A) \lor (S = C)) \land ((Z = A) \lor (Z = C)) \land (\operatorname{sub}\left(u, P\right) = \operatorname{some}\left(S\right)) \land (\operatorname{sub}\left(v, P\right) = \operatorname{some}\left(Z\right))) \implies (((u = v) \land (S = Z)) \lor ((\neg (\operatorname{prefix}\left(u, v\right))) \land (\neg (\operatorname{prefix}\left(v, u\right)))) \lor ((S = C) \land (Z = A) \land (v = \operatorname{concat}\left(u, [L]\right))) \lor ((S = A) \land (Z = C) \land (u = \operatorname{concat}\left(v, [L]\right)))))))))) \land (\forall H: \operatorname{History}\left(\right), (\forall P: T, ((\operatorname{compatible}\left(H, P\right)) \implies ((\operatorname{card}\left(\operatorname{unc}\left(H, P\right)\right) = 0) \implies (\forall Pp: T, ((\operatorname{compatible}\left(H, Pp\right)) \implies (Pp = P))))))) \land (\forall P: T, (\forall u: \operatorname{Word}\left(\right), ((\operatorname{sub}\left(u, P\right) = \operatorname{none}\left(\right)) \iff (\exists v: \operatorname{Word}\left(\right), (\exists b: \operatorname{Bool}\left(\right), (\exists z: \operatorname{Word}\left(\right), ((\operatorname{sub}\left(v, P\right) = \operatorname{some}\left(\operatorname{atom}\left(b\right)\right)) \land (u = \operatorname{concat}\left(v, z\right)) \land (z \neq [])))))))) \land (\forall P: T, (\forall u: \operatorname{Word}\left(\right), (\forall v: \operatorname{Word}\left(\right), (\forall b: \operatorname{Bool}\left(\right), (\forall c: \operatorname{Bool}\left(\right), (((\operatorname{sub}\left(u, P\right) = \operatorname{some}\left(\operatorname{atom}\left(b\right)\right)) \land (\operatorname{sub}\left(v, P\right) = \operatorname{some}\left(\operatorname{atom}\left(c\right)\right)) \land (\operatorname{prefix}\left(u, v\right))) \implies ((u = v) \land (b = c)))))))) \land (\forall h: \operatorname{Word}\left(\right), (\forall P: T, (\forall X: T, ((\operatorname{sub}\left(h, P\right) = \operatorname{some}\left(X\right)) \implies (\exists J: \operatorname{Context}\left(\right), ((\operatorname{hole}\left(J\right) = h) \land (\operatorname{plug}\left(J, X\right) = P) \land (\forall Pp: T, ((\forall u: \operatorname{Word}\left(\right), (((u \in \operatorname{Leaves}\left(P\right)) \land (\neg (\operatorname{prefix}\left(h, u\right)))) \implies (\operatorname{read}\left(u, Pp\right) = \operatorname{read}\left(u, P\right)))) \implies (\exists Y: T, ((\operatorname{sub}\left(h, Pp\right) = \operatorname{some}\left(Y\right)) \land (\operatorname{plug}\left(J, Y\right) = Pp))))))))))) \land (\forall H: \operatorname{History}\left(\right), (\forall u: \operatorname{Word}\left(\right), ((u \in \operatorname{gamma}\left(H\right)) \iff ((\exists w: \operatorname{Word}\left(\right), (((w, \operatorname{a}\left(\right)) \in \operatorname{blocks}\left(H\right)) \land (u = \operatorname{concat}\left(w, [L, R]\right)))) \lor (\exists w: \operatorname{Word}\left(\right), (((w, \operatorname{c}\left(\right)) \in \operatorname{blocks}\left(H\right)) \land ((u = \operatorname{concat}\left(w, [L, L, R]\right)) \lor (u = \operatorname{concat}\left(w, [R, R]\right))))))))) \land (\forall H: \operatorname{History}\left(\right), (\forall w: \operatorname{Word}\left(\right), (((\operatorname{concat}\left(w, [R, R]\right) \in \operatorname{gamma}\left(H\right)) \implies ((w, \operatorname{c}\left(\right)) \in \operatorname{blocks}\left(H\right))) \land ((\operatorname{concat}\left(w, [L, R]\right) \in \operatorname{gamma}\left(H\right)) \implies (((w, \operatorname{a}\left(\right)) \in \operatorname{blocks}\left(H\right)) \lor (\exists v: \operatorname{Word}\left(\right), ((w = \operatorname{concat}\left(v, [L]\right)) \land ((v, \operatorname{c}\left(\right)) \in \operatorname{blocks}\left(H\right))))))))) \land (\forall H: \operatorname{History}\left(\right), (\forall P: T, ((\operatorname{compatible}\left(H, P\right)) \implies ((\operatorname{card}\left(\operatorname{unc}\left(H, P\right)\right) = 1) \implies (\exists x: \operatorname{Word}\left(\right), ((\operatorname{unc}\left(H, P\right) = \{x\}) \land ((\exists v: \operatorname{Word}\left(\right), ((\operatorname{sub}\left(v, P\right) = \operatorname{some}\left(A\right)) \land (x = \operatorname{concat}\left(v, [L, R]\right)))) \lor (\exists v: \operatorname{Word}\left(\right), ((\operatorname{sub}\left(v, P\right) = \operatorname{some}\left(C\right)) \land (x = \operatorname{concat}\left(v, [R, R]\right)) \land (\operatorname{concat}\left(v, [L, L, R]\right) \in \operatorname{gamma}\left(H\right)) \land (\forall Pp: T, ((\operatorname{compatible}\left(H, Pp\right)) \implies (\operatorname{sub}\left(\operatorname{concat}\left(v, [L]\right), Pp\right) = \operatorname{some}\left(A\right))))))))))))) \land ((\forall v: \operatorname{Word}\left(\right), (\forall z: \operatorname{Word}\left(\right), (\forall P: T, ((\operatorname{sub}\left(v, P\right) = \operatorname{none}\left(\right)) \implies (\operatorname{read}\left(\operatorname{concat}\left(v, z\right), P\right) = \operatorname{absent}\left(\right)))))) \land (\forall v: \operatorname{Word}\left(\right), (\forall z: \operatorname{Word}\left(\right), (\forall P: T, (\forall Y: T, ((\operatorname{sub}\left(v, P\right) = \operatorname{some}\left(Y\right)) \implies (\operatorname{read}\left(\operatorname{concat}\left(v, z\right), P\right) = \operatorname{read}\left(z, Y\right)))))))) \land (\forall v: \operatorname{Word}\left(\right), (\forall z: \operatorname{Word}\left(\right), (\forall P: T, (\operatorname{sub}\left(\operatorname{concat}\left(v, z\right), P\right) = \operatorname{bind}\left(\operatorname{sub}\left(v, P\right), \operatorname{nav}\left(z\right)\right))))) \land (\forall P: T, (\forall u: \operatorname{Word}\left(\right), (\forall b: \operatorname{Bool}\left(\right), ((\operatorname{read}\left(u, P\right) = \operatorname{reply}\left(b\right)) \implies (\operatorname{sub}\left(u, P\right) = \operatorname{some}\left(\operatorname{atom}\left(b\right)\right)))))) \land (\forall P: T, (\forall u: \operatorname{Word}\left(\right), ((u \in \operatorname{alpha}\left(P\right)) \iff (\operatorname{read}\left(u, P\right) = \operatorname{alpha}\left(\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/ActualLeafHistoryRigidity.actual_address_geometry` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Induction on the original preimage locates every existing output subtree. A preimage branch keeps its two actual positive children. A preimage leaf gives A or C, whose complete finite offset tables account for all remaining nodes. Positive children have at least three leaves, so a composite branch has at least six. The table then makes E the unique two-leaf subtree and A the unique three-leaf subtree of a positive ambient tree.

The five report suffixes cover every compatible positive leaf. A beta right child determines A. Beta left children and alpha right children belong to E; the side of E in its parent chooses A or C. The finite table includes root block queries, all short leaf addresses, and A inside the immediate left side of C. Determinism of the suffix decoder gives uniqueness. Each retained history block occurs in every compatible tree, hence every covered alpha is an actual alpha there.

Comparable A/C roots can only be equal or be a C with its immediate left A. All other block roots are incomparable. If no alpha remains uncovered, the LR alpha of each canonical A or the RR alpha of each canonical C fixes that entire block in every competitor. Their union is the reference tree's complete labelled frontier; the existing complete-frontier theorem then identifies the literal outputs without comparing sizes.

A nonexistent subtree word is exactly a strict extension of a leaf. Two actual leaf words related by prefix coincide and have the same label. Given a reference subtree at h and matching labelled leaves outside h, induction along h constructs a literal output context. Each sibling's full frontier forces the competitor to have the same sibling and a branch at the path prefix. Thus the hole exists in every matching arbitrary tree. An empty h gives the single root hole.

The explicit gamma union gives its exact LR and LLR/RR membership forms. Suffix cancellation shows that covered RR forces that same C block; covered LR forces that A or an immediately enclosing C. For a singleton residual x, classify the canonical block containing x. A missing C-left alpha would leave C-right covered, forcing C and covering x, a contradiction. Therefore the only cases are an A alpha or a C-right alpha. In the latter case the left alpha is covered and fixes the left A in all competitors, without a size premise. Native navigation transfers all four readout values through an existing subtree and transfers subtree lookup by Option.bind.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualLeafHistoryRigidity.BlockKind`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualLeafHistoryRigidity.BlockOffset`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualLeafHistoryRigidity.Compatible`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualLeafHistoryRigidity.ImagePosition`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualLeafHistoryRigidity.LeafHistory`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualLeafHistoryRigidity.OutputContext`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualLeafHistoryRigidity.actual_address_geometry`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualLeafHistoryRigidity.alphaLeaves`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualLeafHistoryRigidity.decodeBlock`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualLeafHistoryRigidity.forcedBlocks`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualLeafHistoryRigidity.gamma`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualLeafHistoryRigidity.subtree`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualLeafHistoryRigidity.uncovered`
- Dependency: [D5/S3/Arith/FibonacciAtomic/ActualImageSevenLeafSeparation](ActualImageSevenLeafSeparation.md)
