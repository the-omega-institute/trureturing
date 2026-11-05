# Native relative prefix boxes

## Abstract

NativeRelativePrefixBoxes

Source is the original free ordered magma on Boolean leaves: true is alpha, false is beta, and substitution sends alpha to beta, beta to the ordered pair (beta,alpha), and preserves pairing. Address is List Bool with false = L and true = R. readout is the original alpha, beta, branch or absent literal reply. S d is exactly NativeConstructorArrays.S d: Canonical 0 fixes alpha, and Canonical (k+1) admits both leaves and pairs of Canonical k children. In particular S 1 contains precisely alpha, beta and C0 = (alpha,alpha).

Factor is Nat times Bool, with Boolean false and true denoting the integer second coordinates zero and one. pathCost r counts L with weight one and R with weight two. lastRight r is the last-letter R indicator for nonempty r. leafFactor r b has first coordinate pathCost r + (if b then 2 else 1); its second coordinate is b for empty r and lastRight r otherwise. Thus it is precisely (2-e,1-e) at a leaf endpoint and (s(r)+2-e,indicator last R) at a strict blocking prefix, with e(alpha)=0 and e(beta)=1.

gamma follows the actual original constructors along q. At the first actual leaf of label b it returns leafFactor of the remaining suffix and b. At a branch endpoint it returns (0,false). A blocker at index i means readout (take i q) u = leafReply b, where leafReply true = alpha and leafReply false = beta. This nonabsent leaf forces the earlier ancestors to be branches. descriptor q i b = leafFactor (drop i q) b. An absent target has a strict actual blocking prefix, rather than an absent leaf.

level d q z is the set of all u in S d with gamma q u = z. projection d q v z is the actual image of this entire level under u |-> readout v u. It is not the image of a selected representative, and repeated appearances of one literal are the same actual reply. DoubleAt q i means i+1 < length q and the letter at index i is L.

**Theorem 1.1 (Every attained blocking factor is a relative prefix box).**

$$\forall d: Nat, (\forall q: Address, ((\operatorname{length}\left(q\right) < d) \implies (\forall z: Factor, ((\exists u: \operatorname{S}\left(d\right), (\operatorname{gamma}\left(q, \operatorname{val}\left(u\right)\right) = z)) \implies ((\operatorname{level}\left(d, q, z\right) = \{ u: \operatorname{S}\left(d\right) \mid \forall v: Address, ((\operatorname{IsPrefix}\left(v, q\right)) \implies (\operatorname{readout}\left(v, \operatorname{val}\left(u\right)\right) \in \operatorname{projection}\left(d, q, v, z\right))) \}) \land ((\operatorname{Classified}\left(d, q, z\right)) \land ((\forall i, j: Nat, (\forall b, c: Bool, ((i \leq \operatorname{length}\left(q\right)) \implies ((j \leq \operatorname{length}\left(q\right)) \implies ((i < j) \implies ((\operatorname{descriptor}\left(q, i, b\right) = \operatorname{descriptor}\left(q, j, c\right)) \iff ((b = false) \land ((c = true) \land ((j = i + 1) \land (\operatorname{DoubleAt}\left(q, i\right))))))))))) \land ((\forall i: Nat, ((i \leq \operatorname{length}\left(q\right)) \implies (\forall b: Bool, (\exists u: \operatorname{S}\left(d\right), (\operatorname{readout}\left(\operatorname{take}\left(i, q\right), \operatorname{val}\left(u\right)\right) = \operatorname{leafReply}\left(b\right)))))) \land ((\exists u: \operatorname{S}\left(d\right), (\operatorname{readout}\left(q, \operatorname{val}\left(u\right)\right) = branch)) \land ((\forall u: Source, ((\operatorname{snd}\left(\operatorname{gamma}\left(q, u\right)\right) = true) \implies (2 \leq \operatorname{fst}\left(\operatorname{gamma}\left(q, u\right)\right)))) \land (\forall u: Source, ((\operatorname{readout}\left(q, u\right) = absent) \implies (\exists i: Nat, ((i < \operatorname{length}\left(q\right)) \land (\exists b: Bool, ((\operatorname{readout}\left(\operatorname{take}\left(i, q\right), u\right) = \operatorname{leafReply}\left(b\right)) \land (\operatorname{gamma}\left(q, u\right) = \operatorname{descriptor}\left(q, i, b\right))))))))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeRelativePrefixBoxes.canonical_factor_levels` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Classified d q z has exactly the following three alternatives. The branch factor is (0,false), its level is exactly readout q = branch, and its projection at q is the singleton branch. A singleton descriptor has some i at most length q and label b; among all valid descriptors, descriptor q j c = z holds exactly when j=i and c=b. Its level is exactly readout (take i q) = leafReply b, and that projection is the corresponding singleton.

The double alternative has DoubleAt q i and z = descriptor q i false. Among all descriptors it consists exactly of (i,beta) and (i+1,alpha). The level is recognized by both tests: readout (take i q) belongs to {beta,branch}, and readout (take (i+1) q) belongs to {absent,alpha}. The intervening L makes take (i+1) q = take i q appended with L. These two projections of the whole level are exactly the displayed two-element sets; both alternatives are attained by actual canonical trees.

For i<j, equality of complete descriptor factors forces b=false, c=true, j=i+1 and DoubleAt q i, and these conditions suffice. The first-coordinate gap bounds the separation of positions. At a final L the preceding beta and terminal alpha first coordinates coincide, but their second coordinates are false and true. This excludes the terminal candidate, every nonadjacent or R collision, and every class of three descriptors.

Canonical realization uses the existing spine context with alpha at every unused sibling. Both labelled leaves are realized at every prefix, and a branch endpoint is realized by planting C0. The strict length bound permits C0 at the last represented position, while its alpha children are fixed by Canonical 0 outside the menu. These are trees of the recursive canonical carrier, not merely arbitrary trees of bounded height.

A true second coordinate requires a first coordinate of at least two. Every initially absent target has a strict actual blocking prefix with one of the two genuine leaf labels, and its gamma is the corresponding descriptor. The theorem concerns this initial blocking formula; identification with the complete substitution trajectory is an additional assertion.

Every member satisfies its own image conditions at every prefix, including root and q. Conversely the conditions include the one or two exact tests of its classified level. Actual tree consistency then puts the candidate in that level. For q empty there are only the two labelled leaves and a branch root, and the single tests apply. For length q = d-1 the branch realization still uses C0 and the terminal exception still applies. In particular d=1 is included.

This is an equality relative to actual canonical trees. It gives no independent reply-array choices, additional observation service, preparation shortcut or resource bound. All coordinates refer to one actual tree.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeRelativePrefixBoxes.canonical_factor_levels`
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeConstructorArrays](NativeConstructorArrays.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/NativeFiniteMenuCode](../NativeFiniteMenuCode.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/NativeRankedNavigationCompiler](../NativeRankedNavigationCompiler.md)
