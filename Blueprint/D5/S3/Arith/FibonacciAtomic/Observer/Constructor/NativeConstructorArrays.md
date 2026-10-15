# Native constructor array reconstruction

## Abstract

NativeConstructorArrays

The source is the free ordered Boolean tree, with true labelling alpha. Allowed consists exactly of branch/alpha, branch/beta, branch/branch, alpha/absent, beta/absent and absent/absent. Edges checks these pairs at every represented parent and child. Root nonabsence is a separate hypothesis. Neither predicate refers to an existing realization.

Write alpha = Source.of true, beta = Source.of false and C0 = Source.mul alpha alpha. Canonical 0 t means t = alpha. Canonical (k+1) accepts either labelled leaf, and Canonical (k+1) (Source.mul l r) means Canonical k l and Canonical k r. Hence S d = {t : Source | Canonical d t} has S1 = {alpha,beta,C0} and S(k+1) = {alpha,beta} disjoint-union {Source.mul l r | l,r in S k} for positive k. The depth-zero auxiliary carrier fixes the two children of each cutoff branch to alpha; it is not an extra represented coordinate.

Address is a Boolean word, with false = L and true = R. W d = {w : Address | w.length < d}, including the empty root word when d is positive. For z : W d -> Reply, extend z w is z w inside this menu and absent outside it. Edges d z a means that Allowed (z (a ++ w)) (z (a ++ w ++ [b])) holds for every Boolean b and every w with w.length + 1 < d. H d = {z : W d -> Reply | extend z [] is not absent and Edges d (extend z) []}. Thus H is defined by the root condition and six local pairs, independently of any matching tree. Reply consists exactly of alpha, beta, branch and absent.

**Theorem 1.1 (Literal realization of independently legal arrays).**

$$\forall d: Nat, (\forall z: Address \to Reply, (\forall a: Address, ((\operatorname{Edges}\left(d, z, a\right)) \implies (((0 < d) \implies (\operatorname{z}\left(a\right) \neq absent)) \implies ((\operatorname{Canonical}\left(d, \operatorname{realize}\left(d, z, a\right)\right)) \land (\forall w: Address, ((\operatorname{length}\left(w\right) < d) \implies (\operatorname{readout}\left(w, \operatorname{realize}\left(d, z, a\right)\right) = \operatorname{z}\left(\operatorname{append}\left(a, w\right)\right)))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeConstructorArrays.legal_realization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Reconstruction uses NativeWholeRowService.decodePattern and NativeDepthPatterns.fill with a constant alpha frontier. The proof derives absence below an early leaf directly from the six pairs and recursively realizes both subarrays below a branch. It proves the literal replies for every represented word, with no actual-matching-tree hypothesis and no realization choice.

This result supplies the array-to-tree direction. The complete representation below consumes this independent reconstruction in both inverse laws. The six-pair induction supplies the independent native reconstruction; finite product and coordinate arithmetic reuse that correspondence.

**Theorem 1.2 (Faithful constructor representation on the whole native carrier).**

$$\forall d, n: Nat, (\forall hd: 0 < d, (\forall hn: 0 < n, ((\forall t: Source, ((\operatorname{Canonical}\left(1, t\right)) \iff ((t = \operatorname{of}\left(true\right)) \lor ((t = \operatorname{of}\left(false\right)) \lor (t = \operatorname{mul}\left(\operatorname{of}\left(true\right), \operatorname{of}\left(true\right)\right)))))) \land ((\forall k: Nat, (\forall l, r: Source, ((\operatorname{Canonical}\left(k + 1, \operatorname{mul}\left(l, r\right)\right)) \iff ((\operatorname{Canonical}\left(k, l\right)) \land (\operatorname{Canonical}\left(k, r\right)))))) \land ((\operatorname{Bijective}\left(\operatorname{scalarReadout}\left(d, hd\right)\right)) \land ((\operatorname{Bijective}\left(\operatorname{productEquiv}\left(d, n, hd\right)\right)) \land ((\forall x: \operatorname{Fin}\left(n\right) \to \operatorname{S}\left(d\right), (\forall i: \operatorname{Fin}\left(n\right), (\forall w: \operatorname{W}\left(d\right), (\operatorname{val}\left(\operatorname{productEquiv}\left(d, n, hd, x, i\right)\right)\left(w\right) = \operatorname{readout}\left(\operatorname{val}\left(w\right), \operatorname{val}\left(\operatorname{x}\left(i\right)\right)\right))))) \land ((\operatorname{card}\left(\operatorname{Prod}\left(\operatorname{Fin}\left(n\right), \operatorname{W}\left(d\right)\right)\right) = n \times (2^{d} - 1)) \land (\operatorname{card}\left(Reply\right) = 4)))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeConstructorArrays.faithful_constructor_representation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive d and n, S d is the subtype of the original FreeMagma Bool satisfying Canonical d, with true = alpha, false = beta and C0 the ordered pair of alpha leaves. The statement explicitly proves S1 = {alpha,beta,C0}; the successor pair membership is exactly membership of each child in the preceding carrier. Both native labelled leaves remain in every positive carrier. This is the source recursion, not an arbitrary height bound.

W d consists of exactly the actual Boolean words of length less than d. H d is the subtype of arrays on W d with nonabsent root and precisely the independent six parent/append-bit-child pairs. Total extension outside W d is irrelevant padding by absent. Native readout satisfies the constraints; independent reconstruction supplies a canonical native tree and every represented literal reply. Canonical uniqueness proves the left inverse, and the literal reconstruction law proves the right inverse.

The displayed binders hd : 0 < d and hn : 0 < n are exactly the original hypotheses, with no upper bound on d or n. scalarReadout d hd maps t : S d to the legal array w |-> readout w.val t.val. scalarReconstruct d z is realize d (extend z.val) [] with its proved Canonical property. scalarEquiv uses exactly these forward and inverse functions and proves both inverse laws. productEquiv d n hd applies scalarEquiv in every Fin n component, and its inverse applies scalarReconstruct componentwise. The displayed literal equality therefore concerns the same tuple x and the same pair (i,w), retaining all correlations, early leaves and absent coordinates.

The coordinate count is a cardinality of Fin n times W d, not the length of a list with possible repetitions: the prefix list is proved duplicate-free and its exact count is reused. There are n(2^d-1) distinct coordinates and exactly four possible Reply symbols. Repeated uses of (i,w) are one function application and one actual reply. At the cutoff a branch reconstructs C0, whose two alpha children lie just outside W d. An early alpha or beta forces every represented proper descendant absent. The deterministic decodePattern and constant-alpha fill introduce no auxiliary realization choice.

This is a native representation theorem. It adds no preparation or reader port, recovers no arbitrary unobserved deeper labels and makes no resource or literature-originality claim. The canonical boundary, actual source and literal addresses are those of the source theorem.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeConstructorArrays.faithful_constructor_representation`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeConstructorArrays.legal_realization`
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/NativeWholeRowPlan](../NativeWholeRowPlan.md)
