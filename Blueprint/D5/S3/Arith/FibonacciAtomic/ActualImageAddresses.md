# Actual Image Addresses

## Abstract

Raw endpoint observations and address sets of ordered Fibonacci source trees.

Sources are nonempty ordered full binary trees with alpha and beta leaves. The substitution sends alpha to beta and beta to (beta,alpha), and preserves pairing. Addresses reuse ActualTreeReadoutAcquisition.Address, with false for left and true for right. The frozen Reply and readout interface supplies alpha, beta, branch and absent endpoint reports. The complete leaf frontier reuses ActualImageSevenLeafSeparation.leafAddresses.

**Definition 1.1 (Maximum leaf depth).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ActualImageAddresses.height`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ActualImageAddresses.height` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Height is the height of the existing ordered shape decomposition. A leaf has height zero.

**Definition 1.2 (Actual substitution image).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ActualImageAddresses.ActualImage`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ActualImageAddresses.ActualImage` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

ActualImage(d) is the range of the d-fold native substitution on complete source trees.

**Definition 1.3 (Finite depth window).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ActualImageAddresses.Within`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ActualImageAddresses.Within` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Within(h,Q) means that each address in the finite set Q has length at most h.

**Definition 1.4 (Positive address certificate).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ActualImageAddresses.Sound`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ActualImageAddresses.Sound` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Sound(d,V,h,Q) means Within(h,Q) and: every complete tree U with c(U)=c(V) and readout(u,U)=readout(u,V) for every u in Q belongs to ActualImage(d). Exact composition is the only competitor promise, no prefix-closure condition on Q, and no adaptive or random query order.

**Definition 1.5 (Alpha leaf addresses).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ActualImageAddresses.alphaAddresses`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ActualImageAddresses.alphaAddresses` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The finite set contains exactly the root-first addresses of alpha leaves.

**Definition 1.6 (Certificates without a composition promise).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ActualImageAddresses.UnSound`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ActualImageAddresses.UnSound` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every complete source U matching all queried endpoint results must belong to ActualImage(d). No composition or leaf-count constraint is placed on U; the depth window is imposed separately.

**Definition 1.7 (Complete addressed subtree).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ActualImageAddresses.subtree`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ActualImageAddresses.subtree` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The addressed subtree is present exactly when the path reaches a node; otherwise it is absent.

**Definition 1.8 (Subtree replacement).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ActualImageAddresses.replace`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ActualImageAddresses.replace` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Replacement changes the complete subtree at a valid address and retains the surrounding ordered tree. Invalid paths leave the tree unchanged.

**Definition 1.9 (Alpha coverage of branches).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ActualImageAddresses.AlphaCovered`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ActualImageAddresses.AlphaCovered` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every internal node has an alpha leaf descendant, recursively throughout the tree.

**Definition 1.10 (Right comb source).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ActualImageAddresses.rightComb`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ActualImageAddresses.rightComb` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The zero comb is beta. The successor comb pairs alpha on the left with the preceding comb on the right, giving m alpha side leaves and one terminal beta at m right steps.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualImageAddresses.ActualImage`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualImageAddresses.AlphaCovered`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualImageAddresses.Sound`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualImageAddresses.UnSound`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualImageAddresses.Within`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualImageAddresses.alphaAddresses`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualImageAddresses.height`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualImageAddresses.replace`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualImageAddresses.rightComb`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualImageAddresses.subtree`
- Dependency: [D5/S3/Arith/FibonacciAtomic/ActualImageSevenLeafSeparation](ActualImageSevenLeafSeparation.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition](ActualTreeReadoutAcquisition.md)
