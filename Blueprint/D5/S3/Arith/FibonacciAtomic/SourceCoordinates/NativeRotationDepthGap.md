# Native Rotation and Complete Fiber Depth Extrema

## Abstract

One contextual rotation attains the entire Fibonacci word and geometry fiber depth range.

S is the actual FreeMagma Bool source: finite nonempty ordered binary trees. Alpha is the true leaf, beta the false leaf, and pair retains the original ordered brackets. The original substitution rho sends alpha to beta and beta to pair(beta,alpha). R(k,t) is its k-fold iterate, including k=0. T(n)=R(n,alpha); U(n) is the existing AncestorAreaInstability.rotated(n-3), with U(3)=pair(beta,pair(alpha,beta)). T(3)=pair(pair(beta,alpha),beta). The word w(t)=wd(t) retains every labelled leaf in its original order; ell(t) counts all leaves. G is the original five-coordinate geometry of that whole word. Depth and Q are the original intrinsic substitution coordinates, with Boolean true written 1 and false written 0.

**Definition 1.1 (One Contextual Associativity Step).**

$$\forall C: \operatorname{OutputContext}\left(\right), (\forall s: S, (\forall t: S, ((\operatorname{ContextRotation}\left(C, s, t\right)) \iff (\exists a: S, (\exists b: S, (\exists c: S, ((s = \operatorname{plug}\left(C, \operatorname{pair}\left(\operatorname{pair}\left(a, b\right), c\right)\right)) \land (t = \operatorname{plug}\left(C, \operatorname{pair}\left(a, \operatorname{pair}\left(b, c\right)\right)\right)))))))))$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/SourceCoordinates/NativeRotationDepthGap.ContextRotation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

C is the existing ActualLeafHistoryRigidity.OutputContext. Plugging its unique hole preserves every ordered sibling and label. ContextRotation uses one local associativity move.

**Definition 1.2 (Actual Undirected Rotation Graph).**

$$\forall s: S, (\forall t: S, ((\operatorname{Adj}\left(s, t\right)) \iff ((s \neq t) \land (\exists C: \operatorname{OutputContext}\left(\right), ((\operatorname{ContextRotation}\left(C, s, t\right)) \lor (\operatorname{ContextRotation}\left(C, t, s\right)))))))$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/SourceCoordinates/NativeRotationDepthGap.rotationGraph` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The graph has the entire actual source as its vertex set. Its edges are either orientation of a contextual ordered associativity step between distinct sources. d is the ordinary SimpleGraph.dist and Reachable is graph reachability. For disconnected pairs ordinary distance is zero; the universal metric claim retains Reachable.

**Definition 1.3 (Native Left Context).**

$$(\operatorname{C}\left(0\right) = \operatorname{hole}\left(\right)) \land (\forall k: \operatorname{Nat}\left(\right), (\operatorname{C}\left(k + 1\right) = \operatorname{left}\left(\operatorname{C}\left(k\right), \operatorname{T}\left(k + 2\right)\right)))$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/SourceCoordinates/NativeRotationDepthGap.leftContext` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

C(k) denotes leftContext(k). Its right siblings are the original T(k+2), while its hole follows k left edges. In addresses false means left.

**Theorem 1.4 (Single Rotation, Forward Transport, and Sharp Complete Fiber Bounds).**

$$(\forall n: \operatorname{Nat}\left(\right), ((3 \leq n) \implies ((\operatorname{holeAddress}\left(\operatorname{C}\left(n - 3\right)\right) = \operatorname{replicate}\left(n - 3, 0\right)) \land (\operatorname{plug}\left(\operatorname{C}\left(n - 3\right), \operatorname{T}\left(3\right)\right) = \operatorname{T}\left(n\right)) \land (\operatorname{plug}\left(\operatorname{C}\left(n - 3\right), \operatorname{U}\left(3\right)\right) = \operatorname{U}\left(n\right)) \land (\operatorname{ContextRotation}\left(\operatorname{C}\left(n - 3\right), \operatorname{T}\left(n\right), \operatorname{U}\left(n\right)\right)) \land (\operatorname{Adj}\left(\operatorname{T}\left(n\right), \operatorname{U}\left(n\right)\right)) \land (\operatorname{d}\left(\operatorname{T}\left(n\right), \operatorname{U}\left(n\right)\right) = 1) \land (\operatorname{w}\left(\operatorname{T}\left(n\right)\right) = \operatorname{w}\left(\operatorname{U}\left(n\right)\right)) \land (\operatorname{ell}\left(\operatorname{T}\left(n\right)\right) = \operatorname{fib}\left(n + 1\right)) \land (\operatorname{ell}\left(\operatorname{U}\left(n\right)\right) = \operatorname{fib}\left(n + 1\right)) \land (\operatorname{Q}\left(\operatorname{T}\left(n\right)\right) = (n, 1)) \land (\operatorname{Q}\left(\operatorname{U}\left(n\right)\right) = (0, 0)) \land (\forall j: \operatorname{Nat}\left(\right), ((\operatorname{w}\left(\operatorname{R}\left(j, \operatorname{T}\left(n\right)\right)\right) = \operatorname{w}\left(\operatorname{R}\left(j, \operatorname{U}\left(n\right)\right)\right)) \land (\operatorname{G}\left(\operatorname{w}\left(\operatorname{R}\left(j, \operatorname{T}\left(n\right)\right)\right)\right) = \operatorname{G}\left(\operatorname{w}\left(\operatorname{R}\left(j, \operatorname{U}\left(n\right)\right)\right)\right)) \land (\operatorname{depth}\left(\operatorname{R}\left(j, \operatorname{T}\left(n\right)\right)\right) = n + j) \land (\operatorname{depth}\left(\operatorname{R}\left(j, \operatorname{U}\left(n\right)\right)\right) = j))) \land (\forall s: S, ((\operatorname{w}\left(s\right) = \operatorname{w}\left(\operatorname{T}\left(n\right)\right)) \implies ((0 \leq \operatorname{depth}\left(s\right)) \land (\operatorname{depth}\left(s\right) \leq n)))) \land (\forall s: S, ((\operatorname{G}\left(\operatorname{w}\left(s\right)\right) = \operatorname{G}\left(\operatorname{w}\left(\operatorname{T}\left(n\right)\right)\right)) \implies ((0 \leq \operatorname{depth}\left(s\right)) \land (\operatorname{depth}\left(s\right) \leq n)))) \land (\operatorname{depth}\left(\operatorname{T}\left(n\right)\right) = n) \land (\operatorname{depth}\left(\operatorname{U}\left(n\right)\right) = 0)))) \land (\neg (\exists A: \operatorname{Real}\left(\right), (\forall s: S, (\forall t: S, ((\operatorname{w}\left(s\right) = \operatorname{w}\left(t\right)) \implies ((\operatorname{Reachable}\left(s, t\right)) \implies (\lvert \operatorname{real}\left(\operatorname{depth}\left(s\right)\right) - \operatorname{real}\left(\operatorname{depth}\left(t\right)\right) \rvert \leq (A) \cdot (\operatorname{real}\left(\operatorname{d}\left(s, t\right)\right)))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/SourceCoordinates/NativeRotationDepthGap.native_rotation_depth_gap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The structural induction on C(k) uses the source centralizer recurrence T(k+4)=pair(T(k+3),T(k+2)). It identifies C(k).plug(T(3)) with T(k+3) and C(k).plug(U(3)) with rotated(k), at the exact address L repeated k times. Thus the original three-leaf reassociation remains one edge at every n>=3. The existing AncestorAreaInstability.result supplies the whole-word equality, Fibonacci leaf count and the two endpoint depths. Unequal depths make the sources distinct, so adjacency gives distance exactly one.

The existing intrinsic coordinate composites identify the ray flag and supply the one-step coordinate transport. Iteration gives depths n+j and j. The original GeometryEntranceRatio.wd_substitution gives w(rho(t))=sigma(w(t)), so every common forward iterate has the same entire labelled word and hence the same G. No rotation-distance assertion is made about these common forward iterates.

For every actual ancestor p and exponent k, the composition transport and Fibonacci recurrence give ell(R(k,p))=fib(k+1) composition(p).1 + fib(k+2) composition(p).2, at least fib(k+1) because ell(p)>0. Applying this estimate to the realized maximal ancestor bounds every actual tree of length fib(n+1) by depth n, using strict Fibonacci growth for n>=3. Same words have the same length by FreeMagma.length_toFreeSemigroup. The original GeometryEntranceRatio.tree_length also fixes the length of every member of the complete same-G fiber. Both fibers therefore have minimum zero and maximum n, attained by these same U(n) and T(n). There is no restriction to the displayed family, selected shapes, or selected word representatives.

If a finite real coefficient A bounded depth differences for all same-word reachable pairs, these distance-one witnesses would give n<=A for every n>=3, contradicting unbounded natural numbers. The result connects native contextual rotation with the intrinsic depth coordinate. It is a repository-derived synthesis of the cited family and coordinate results, with no global priority claim, quotient adjacency, physical acquisition claim, or bound for arbitrary non-Fibonacci leaf counts.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/SourceCoordinates/NativeRotationDepthGap.ContextRotation`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/SourceCoordinates/NativeRotationDepthGap.leftContext`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/SourceCoordinates/NativeRotationDepthGap.native_rotation_depth_gap`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/SourceCoordinates/NativeRotationDepthGap.rotationGraph`
- Dependency: [D5/S3/Arith/FibonacciAtomic/ActualLeafHistoryRigidity](../ActualLeafHistoryRigidity.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/ActualObserverAbsorbingNormalization](../Observer/ActualObserverAbsorbingNormalization.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/SourceCoordinates/IntrinsicSubstitutionCoordinates](IntrinsicSubstitutionCoordinates.md)
