# Sharp native predecessor fibers

## Abstract

NativeSharpPredecessorFiber

**Theorem 1.1 (Right-Child Birth on Every Actual Transition).**

$$\forall q: Address, (\forall v: Source, ((\operatorname{isSome}\left(\operatorname{subtree}\left(\operatorname{append}\left(q, \operatorname{singleton}\left(true\right)\right), \operatorname{rho}\left(v\right)\right)\right)) \implies ((\operatorname{subtree}\left(\operatorname{append}\left(q, \operatorname{singleton}\left(true\right)\right), v\right) = none) \iff (\operatorname{subtree}\left(\operatorname{append}\left(q, \operatorname{singleton}\left(true\right)\right), \operatorname{rho}\left(v\right)\right) = \operatorname{some}\left(\operatorname{of}\left(true\right)\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/NativeSharpPredecessorFiber.right_birth` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every legal finite parent address q and every original source v, if its current right child is present, its predecessor right child is absent exactly when the current child is alpha. This theorem applies to all sources and addresses, independently of the comb witness family. Whole-row support repair uses it for either child together with equality of the two child-presence flags.

**Definition 1.2 (Native child-cut sites).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSharpPredecessorFiber.position`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeSharpPredecessorFiber.position` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For k=n+1, position i is hole n i followed by the true edge. The arbitrary-size right-comb context, its hole addresses and its complete address/suffix law are reused directly from FiniteHereditaryPatternRealization.B_T, hole, hole_locate and result. The unique hole/suffix law proves that this single finite public cut is prefix-free. No bound on n or source size is imposed.

**Definition 1.3 (One fixed public cut).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSharpPredecessorFiber.cut`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeSharpPredecessorFiber.cut` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The cut is the image of all Fin(n+1) indices under position. It is shared by every selector and every actual origin in the family.

**Definition 1.4 (Changing old constructors).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSharpPredecessorFiber.site`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeSharpPredecessorFiber.site` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A selected old site is beta. Every other old site is the ordered pair of alpha and an arbitrary native tag. After one genuine native update the selected site is the pair of beta and alpha, while an unselected site is the pair of beta and the native image of its tag. The uniform installation identity retains the whole common exterior, stopping at the right child of each site. Its contextual induction uses the existing comb rather than reproving its geometry.

**Definition 1.5 (Actual joint native witnesses).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSharpPredecessorFiber.origin`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeSharpPredecessorFiber.origin` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For any injective tag family z:Fin(k) to FreeMagma Bool and selector a:Option(Fin(k)), fill the existing comb by site(z i,a=some i). None selects no site. Some i selects exactly i. These are k+1 complete actual origins of the same native register at public current epoch one; every comparison is between complete jointly attained sources. Injectivity of substitution and exclusion of alpha from its image are reused from SourceTransportCentralizer.source_transport_centralizer and IntrinsicSubstitutionCoordinates.no_alpha. Hence the k hidden current values are pairwise distinct for every selector. The source's specified orbit tags rho^(i+1) alpha are an exact specialization, not a restriction on the theorem.

**Definition 1.6 (The complete common current row).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSharpPredecessorFiber.current`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeSharpPredecessorFiber.current` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Current is the entire canonical row of the none origin after one update. Equality is established through ActualCutPartitionDecoder.canonicalRow_record_iff, including the whole exterior and the ordered equality/disequality partition. Every child cut is reached. Old support is the full cut for none and the cut with position i erased for some i. The old selected beta is a concrete strict-prefix absence guard; canonicalRow_absent_guard preserves all other absent-cut guards.

**Definition 1.7 (Only occurring native class names).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSharpPredecessorFiber.className`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeSharpPredecessorFiber.className` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each site names its actual current class by classOrdinal at that site. The existing labels_canonical and classOrdinal_eq_iff identify the finite set of occurring names with the injective image of Fin(k). Raw first-occurrence ordinals need not be consecutive. Counts and supplementary labels use these occurring classes.

**Definition 1.8 (The entire actual current-row fiber).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSharpPredecessorFiber.ActualPredecessors`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeSharpPredecessorFiber.ActualPredecessors` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

ActualPredecessors contains every finite FreeMagma Bool source v whose native image has the common entire current row. There is no restriction to the selected witness family, its tags, size, inverse depth or a finite list of sources. At each right cut, old absence is equivalent to a current alpha value. The complete singleton partition permits at most one such value. Thus old support is exactly the full cut or one site erased. NativePredecessorRowRecovery.native_predecessor_row_recovery identifies old-row equality with old-support equality under the common current row. Every possible old row is consequently attained by exactly one family selector. The number of origins in this fiber is not claimed finite. When k is at least two, two different selected sites have the same number of old reached holes and newborn holes, but different predecessor rows. Retaining only the newborn count therefore cannot recover the predecessor.

**Definition 1.9 (Exact recovery with a supplement).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSharpPredecessorFiber.Encodable`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeSharpPredecessorFiber.Encodable` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Encodable quantifies a supplementary configuration for each compatible actual origin and one deterministic decoder taking only that configuration; the fixed complete base is the public cut, current row, origin-continuity condition and epoch one. Correctness is demanded on the entire actual fiber. The supplement may be selected from already acquired information. This mathematical existence statement supplies no source query, acquisition optimum, runtime semantic-alpha oracle, physical authentication or effective feasibility oracle. A larger accessible source-dependent base can reduce the fiber and its minimum.

**Definition 1.10 (All sharpness and capacity clauses).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSharpPredecessorFiber.Sharp`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeSharpPredecessorFiber.Sharp` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For k=n+1, Sharp requires prefix freedom, equality of all k+1 complete current rows, exactly k occurring classes, the full/one-erased old supports, distinct whole predecessor rows, equality of their finite image with the whole attained old-row image, and exactly k+1 image values. For every configuration count m, exact recovery exists precisely when k+1 is at most m. For every fixed binary width b, it exists precisely when Nat.clog 2 (k+1) is at most b. This is the integer ceiling of the binary logarithm, characterized by Nat.clog_le_iff_le_pow and Nat.le_pow_clog.

**Theorem 1.11 (The full native sharp predecessor fiber).**

$$\forall n: Nat, (\forall z: \operatorname{NativeTags}\left(n\right), ((\operatorname{Injective}\left(z\right)) \implies (\operatorname{Sharp}\left(n, z, \operatorname{oldRows}\left(n, z\right)\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/NativeSharpPredecessorFiber.native_sharp_predecessor_fiber` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The theorem holds for every n and every injective native tag family. In the displayed formula NativeTags(n) means Fin(n+1) to Source and oldRows(n,z) means the function a to canonicalRow(cut(n),origin(n,z,a)). The uniform installation identity handles changing old constructors under the same current child cut. The exact exterior and full partition then give the common canonical row before predecessor recovery or counting. NativeCutFibers.labels_canonical identifies occurring classes without consecutive-ordinal assumptions. The entire actual-fiber exhaustion and NativePredecessorRowRecovery supply sharp upper equality, not merely k+1 witnesses. Correct decoding implies an injection of the k+1 distinct old rows into configurations; FiniteIdentificationCapacityBound.finite_identification_capacity_bound supplies the lower bound. Conversely, choose the attained old-support selector and embed it into any sufficiently large finite configuration space. The decoder inverts that embedding and applies NativePredecessorRowRecovery.back to the public current row and the selected full or one-erased cut. It accesses no hidden native tag or newly acquired semantic value. Binary function-space cardinality and the pinned upper-logarithm equivalence supply both directions for bits. The same correct encoder satisfies FiniteIdentificationCapacityBound.cost_form: log base two of k+1 is at most the logarithm of its configuration capacity. Real.natCeil_logb_natCast identifies the integer minimum with the ceiling of the real binary logarithm. The configuration count excludes the public dictionary, cut addresses, current row, epoch, authentication, workspace, output and acquisition. These are source-specific deductions using existing context, finite identification and native recovery methods, with no literature-priority claim.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSharpPredecessorFiber.ActualPredecessors`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSharpPredecessorFiber.Encodable`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSharpPredecessorFiber.Sharp`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSharpPredecessorFiber.className`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSharpPredecessorFiber.current`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSharpPredecessorFiber.cut`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSharpPredecessorFiber.native_sharp_predecessor_fiber`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSharpPredecessorFiber.origin`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSharpPredecessorFiber.position`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSharpPredecessorFiber.right_birth`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSharpPredecessorFiber.site`
- Dependency: [D5/S3/Arith/FibonacciAtomic/FiniteHereditaryPatternRealization](../FiniteHereditaryPatternRealization.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/NativeCutFibers](NativeCutFibers.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/NativePositiveContextFiber](NativePositiveContextFiber.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/NativePredecessorRowRecovery](NativePredecessorRowRecovery.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/NativeSymbolicRecutting](NativeSymbolicRecutting.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/SourceCoordinates/IntrinsicSubstitutionCoordinates](../SourceCoordinates/IntrinsicSubstitutionCoordinates.md)
- Dependency: [D5/S3/ConceptDynamics/Experiment/FiniteIdentificationCapacityBound](../../../ConceptDynamics/Experiment/FiniteIdentificationCapacityBound.md)
