# Complete Leaf-History Rigidity and a Common Literal Output Hole

## Abstract

A finite leaf history with at most one uncovered alpha fixes every equal-size compatible actual third image.

T is the original FreeMagma Bool of nonempty finite ordered full binary trees. True labels alpha and false labels beta; address bits false and true mean left and right. All finite addresses, including the empty root, have the four replies alpha, beta, branch and absent. Positive trees are actual third substitution images. E=pair(beta,alpha), A=pair(E,beta), and C=pair(A,E). Their leaf counts are two, three and five.

History is any finite list of address/reply pairs, with repetitions permitted. compatible(H,P) means that P is positive and matches exactly the alpha and beta reports in H. Branch and absent reports impose no comparison constraint. blocks(H) is the finite set obtained from those leaf reports by the five-row decoder of ActualLeafHistoryRigidity. gamma(H) is the set union of alpha addresses in those blocks; overlaps are counted once. unc(H,P) is alphaLeaves(P) minus gamma(H). No equal-size condition is part of compatibility.

Context is the finite literal OutputContext from ActualLeafHistoryRigidity, whose left and right constructors store actual output siblings. hole(J) is its unique hole address and plug(J,X) fills that hole. sub(h,P) is some(X) exactly when the actual subtree X exists at h. Leaves(P) is the full labelled leaf frontier, with labels obtained by read(u,P). root(d) is the root of a decoded block d; prefix is ordinary word prefix. n(P) is the native leaf count, and card is finite-set cardinality.

**Theorem 1.1 (Leaf Count of a Filled Context).**

$$\forall J: \operatorname{Context}\left(\right), (\forall Z: T, (\operatorname{n}\left(\operatorname{plug}\left(J, Z\right)\right) = \operatorname{outsideLeaves}\left(J\right) + \operatorname{n}\left(Z\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/ActualHistorySingleHoleRecovery.context_length` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Filling the hole of a literal output context J with Z gives n(plug(J,Z))=outsideLeaves(J)+n(Z), by induction on the context: the hole adds nothing, and each left or right constructor adds the leaf count of its stored sibling.

**Theorem 1.2 (Zero Recovery, Size-Free Common Context, and Same-Size Rigidity).**

$$\forall H: \operatorname{History}\left(\right), (\forall P: T, ((\operatorname{compatible}\left(H, P\right)) \implies (((\operatorname{card}\left(\operatorname{unc}\left(H, P\right)\right) = 0) \implies (\forall Pp: T, ((\operatorname{compatible}\left(H, Pp\right)) \implies (Pp = P)))) \land ((\operatorname{card}\left(\operatorname{unc}\left(H, P\right)\right) = 1) \implies (\exists J: \operatorname{Context}\left(\right), (\exists h: \operatorname{Word}\left(\right), (\exists X: T, ((\operatorname{hole}\left(J\right) = h) \land ((X = A) \lor (X = E)) \land (\operatorname{sub}\left(h, P\right) = \operatorname{some}\left(X\right)) \land (\operatorname{plug}\left(J, X\right) = P) \land (\forall d: \operatorname{Block}\left(\right), ((d \in \operatorname{blocks}\left(H\right)) \implies ((\neg (\operatorname{prefix}\left(\operatorname{root}\left(d\right), h\right))) \land (\neg (\operatorname{prefix}\left(h, \operatorname{root}\left(d\right)\right)))))) \land (\forall Pp: T, ((\operatorname{compatible}\left(H, Pp\right)) \implies ((\forall u: \operatorname{Word}\left(\right), (((u \in \operatorname{Leaves}\left(P\right)) \land (\neg (\operatorname{prefix}\left(h, u\right)))) \implies (\operatorname{read}\left(u, Pp\right) = \operatorname{read}\left(u, P\right)))) \land (\exists Y: T, ((\operatorname{sub}\left(h, Pp\right) = \operatorname{some}\left(Y\right)) \land (\operatorname{plug}\left(J, Y\right) = Pp))))))))))) \land ((\operatorname{card}\left(\operatorname{unc}\left(H, P\right)\right) \leq 1) \implies (\forall Pp: T, (((\operatorname{compatible}\left(H, Pp\right)) \land (\operatorname{n}\left(Pp\right) = \operatorname{n}\left(P\right))) \implies (Pp = P)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/ActualHistorySingleHoleRecovery.complete_history_rigidity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If every alpha is covered, the previously established complete labelled-frontier recovery fixes the entire output tree without comparing sizes.

For a singleton residual x, the native position classification chooses either an A at h with x=hLR, or the right E of a C at v with h=vR and x=vRR. In the second case the left A is already fixed. For each leaf outside h, locate its canonical A or C block. An A whose LR alpha differs from x is fixed; a C whose RR alpha differs from x is fixed. Equality identifies the special block by suffix cancellation. Its outside leaves are absent in the A case and belong to the fixed left A in the C case. Thus all outside labelled leaves match in every compatible tree.

A forced A/C block meeting the A hole would contain x by block overlap. A block meeting the right E hole is either that C, which contains x, or its left A, which is disjoint from the hole. Hence every history block has an incomparable root to the selected hole. Replacing the reference subtree by a hole gives one context J before competitors are quantified. Complete sibling frontiers force each path branch, fix each literal sibling, and ensure the hole exists in every competitor. The empty path gives the root-hole case, including empty history on A.

A common literal context has n(plug(J,Z))=outsideLeaves(J)+n(Z), proved by context induction. Equal total leaf counts cancel the common outside count. The competitor remains ambient positive, so an existing two-leaf hole subtree is E and a three-leaf hole subtree is A. No positivity of the hole subtree is assumed. Consequently its filling equals the reference filling, and the full trees are equal.

With P=pair(A,A), H containing only the beta report at LR, and Pp=C=pair(A,E), the common context is right(A,hole). The fillings A and E have different sizes. This demonstrates why context recovery precedes and does not require the equal-size condition.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualHistorySingleHoleRecovery.complete_history_rigidity`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualHistorySingleHoleRecovery.context_length`
- Dependency: [D5/S3/Arith/FibonacciAtomic/ActualLeafHistoryRigidity](ActualLeafHistoryRigidity.md)
