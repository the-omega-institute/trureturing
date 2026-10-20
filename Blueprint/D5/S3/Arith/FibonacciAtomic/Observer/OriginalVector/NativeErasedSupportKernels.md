# Native erased and support prefix kernels

## Abstract

NativeErasedSupportKernels

**Definition 1.1 (Leaf erasure).**

$$(\operatorname{erase}\left(alpha\right) = leaf) \land (\operatorname{erase}\left(beta\right) = leaf) \land (\operatorname{erase}\left(branch\right) = branch) \land (\operatorname{erase}\left(absent\right) = absent)$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/OriginalVector/NativeErasedSupportKernels.erase` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

ErasedReply has the three constructors leaf, branch, and absent. Erasure identifies exactly the alpha and beta leaf replies. In particular, an absent address remains distinct from a leaf and from a branch.

**Definition 1.2 (Erased prefix agreement).**

$$\forall r: Nat, (\forall u: Source, (\forall v: Source, ((\operatorname{ErasedAgree}\left(r, u, v\right)) \iff (\forall a: Address, ((\operatorname{length}\left(a\right) \leq r) \implies (\operatorname{erase}\left(\operatorname{readout}\left(a, u\right)\right) = \operatorname{erase}\left(\operatorname{readout}\left(a, v\right)\right)))))))$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/OriginalVector/NativeErasedSupportKernels.ErasedAgree` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

ErasedAgree compares all erased replies at ordered addresses of length at most the radius. Addresses below an original leaf are included and return absent.

**Definition 1.3 (Presence prefix agreement).**

$$\forall r: Nat, (\forall u: Source, (\forall v: Source, ((\operatorname{SupportAgree}\left(r, u, v\right)) \iff (\forall a: Address, ((\operatorname{length}\left(a\right) \leq r) \implies ((\operatorname{readout}\left(a, u\right) \neq absent) \iff (\operatorname{readout}\left(a, v\right) \neq absent)))))))$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/OriginalVector/NativeErasedSupportKernels.SupportAgree` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

SupportAgree retains only whether each address is present. On full binary trees, the presence of an address and of one specified child distinguishes absent, leaf, and branch. Thus erased agreement through radius r is equivalent to presence agreement through radius r+1.

**Theorem 1.4 (Exact two-step kernels).**

$$\forall h: Nat, (\forall u: Source, (\forall v: Source, (((\operatorname{OriginalAgree}\left(h, u, v\right)) \iff (\operatorname{OriginalAgree}\left(h + 1, \operatorname{iterate}\left(substitution, 2, u\right), \operatorname{iterate}\left(substitution, 2, v\right)\right))) \land ((\operatorname{OriginalAgree}\left(h, u, v\right)) \iff (\operatorname{ErasedAgree}\left(h + 1, \operatorname{iterate}\left(substitution, 2, u\right), \operatorname{iterate}\left(substitution, 2, v\right)\right))) \land ((\operatorname{OriginalAgree}\left(h, u, v\right)) \iff (\operatorname{SupportAgree}\left(h + 2, \operatorname{iterate}\left(substitution, 2, u\right), \operatorname{iterate}\left(substitution, 2, v\right)\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/OriginalVector/NativeErasedSupportKernels.two_step_prefix_kernel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Source is FreeMagma Bool, the finite nonempty ordered binary trees. The source leaf of(true) is alpha and of(false) is beta. The actual substitution rho sends alpha to beta and beta to mul(beta,alpha), and distributes over ordered branches. Addresses are Boolean lists, with false left and true right. OriginalAgree compares the complete four-valued readout through an inclusive natural radius.

After two substitutions every source has a branch root. The erased child replies of an original alpha, beta, and branch are respectively (leaf,leaf), (branch,leaf), and (branch,branch). They recover the original root type. Induction on the radius then transports labeled agreement one layer deeper and reflects erased agreement back to the original prefix. Below a recovered leaf the original replies are absent, even if substitution has created current descendants.

For every radius h and every pair of sources, the original labeled prefix has the same equality classes as the labeled or erased two-step prefix through h+1, and as the presence prefix through h+2. The root, left-right order, and source pair are the same throughout.

**Theorem 1.5 (All positive even epochs).**

$$\forall h: Nat, (\forall k: Nat, ((1 \leq k) \implies (\forall u: Source, (\forall v: Source, (((\operatorname{ErasedAgree}\left(h + k, \operatorname{iterate}\left(substitution, 2 \times k, u\right), \operatorname{iterate}\left(substitution, 2 \times k, v\right)\right)) \iff (\operatorname{OriginalAgree}\left(h, u, v\right))) \land ((\operatorname{SupportAgree}\left(h + k + 1, \operatorname{iterate}\left(substitution, 2 \times k, u\right), \operatorname{iterate}\left(substitution, 2 \times k, v\right)\right)) \iff (\operatorname{OriginalAgree}\left(h, u, v\right))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/OriginalVector/NativeErasedSupportKernels.even_epoch_support_kernel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At every certified epoch 2k with k at least one, the erased prefix through h+k and the presence prefix through h+k+1 each determine exactly the original labeled prefix through h. Iterating the labeled component of the two-step equality transports the radius through the preceding k-1 pairs of substitutions; the final two-step equality gives the erased and presence conclusions.

All natural radii and all finite sources are included, without a source-size promise. The statement compares observations at a fixed actual epoch on the original root. Sharpness of the presence radius follows from the existing native alpha-spine observation theorem: choose an original address of length h and put alpha and beta at that reached hole. Their original replies there differ while their presence tables agree through h+k.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/OriginalVector/NativeErasedSupportKernels.ErasedAgree`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/OriginalVector/NativeErasedSupportKernels.SupportAgree`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/OriginalVector/NativeErasedSupportKernels.erase`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/OriginalVector/NativeErasedSupportKernels.even_epoch_support_kernel`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/OriginalVector/NativeErasedSupportKernels.two_step_prefix_kernel`
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/DelayedOriginalReadout](../DelayedOriginalReadout.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/FiniteMenu/Kernel](../FiniteMenu/Kernel.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialDepth](../NativeSerialDepth.md)
