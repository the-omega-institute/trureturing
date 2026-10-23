# Total finite joint choice on the whole source fiber

## Abstract

NativeFiveHoleJointChoice

**Definition 1.1 (Inclusive absent-aware agreement).**

$$\forall h: Nat, (\forall u, v: Source, ((\operatorname{Agree}\left(h, u, v\right)) \iff (\forall a: Address, ((\operatorname{length}\left(a\right) \le h) \implies (\operatorname{readout}\left(a, u\right) = \operatorname{readout}\left(a, v\right))))))$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeFiveHoleJointChoice.Agree` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Agreement compares every address through the inclusive depth and all four replies: alpha, beta, branch and absent. It includes early leaves and their absent descendants. Constructor locality and original prefix locality preserve agreement under pairs and every fixed native substitution iterate.

**Definition 1.2 (Finite contact uses actual iterates).**

$$\forall n: Nat, (\operatorname{approximation}\left(n\right) = \operatorname{iterate}\left(\operatorname{F}\left(\right), n, \operatorname{of}\left(true\right)\right))$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeFiveHoleJointChoice.approximation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The finite base at depth h is the iterate at h+1. It agrees through h with its F image, by root agreement at zero and one-level constructor locality in the inductive step. Its right spine of length h+1 reaches the substitution iterate of alpha at that exponent. Original present transport is applied only to an already reached address. Substitution is never commuted with F.

**Definition 1.3 (Actual finite sources in both whole strata).**

$$\forall H: History, (\forall h: Nat, (\operatorname{Witness}\left(H, h\right) = \operatorname{Subtype}\left(\lambda p: \operatorname{Prod}\left(Source, Source\right), ((\operatorname{Stratum}\left(false, H, \operatorname{fst}\left(p\right)\right)) \land ((\operatorname{Stratum}\left(true, H, \operatorname{snd}\left(p\right)\right)) \land (\operatorname{Agree}\left(h, \operatorname{fst}\left(p\right), \operatorname{snd}\left(p\right)\right))))\right)))$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeFiveHoleJointChoice.Witness` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Both tables use the same independent live patterns at depth h+1: the contact iterate and a full branch tree of that depth. Reached spines and frontier_geometry prove liveness. Existing patternTerm, pattern_deep, original_fill_reply, pattern_evaluate and depthEquiv directly supply equality of readouts at every shorter address.

Simultaneous prefix separation supplies one explicit prefixTuple for each complete table in these common patterns. The two y values agree with the contact iterate, and the two z values with the branch base. Finite contact and locality give agreement between the first y and F of the second. Pairing all five holes yields the original sources with their complete labels and every protected-history occurrence.

**Definition 1.4 (Existence at a supplied finite depth).**

$$\forall H: History, (\forall h: Nat, ((\operatorname{J}\left(H, h\right)) \iff (\operatorname{Nonempty}\left(\operatorname{Witness}\left(H, h\right)\right))))$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeFiveHoleJointChoice.J` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

JointWitness contains the computed source pair and both original membership proofs. Its data use finite iterates, depth decompositions, finite separators and explicit frontier numbering. No noncomputable choice over an existence theorem selects the sources.

**Theorem 1.5 (Whole-stratum emptiness or joint witnesses at every depth).**

$$\forall H: OriginalHistory, (\forall supported: \operatorname{Supported}\left(H\right), ((\exists s: Bool, ((\forall u: Source, (\neg (\operatorname{Stratum}\left(s, \operatorname{subtype}\left(H, supported\right), u\right)))) \land (\neg (\operatorname{J}\left(\operatorname{subtype}\left(H, supported\right), 0\right))))) \lor (\forall h: Nat, (\operatorname{J}\left(\operatorname{subtype}\left(H, supported\right), h\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/NativeFiveHoleJointChoice.joint_finite_choice` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Choose computes both finite separator tests. Failure proves an entire original stratum empty. Success returns the explicit function from each supplied natural depth to JointWitness. The empty case excludes J at zero. Arbitrary epochs, repetitions, both guards, all six class comparisons, the full exterior and both complete partitions are retained.

This structural conclusion concerns the entire original raw/history fiber. It asserts no physical acquisition, resource bound, general solver, infinite completion interpretation or conclusion about other row pairs.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeFiveHoleJointChoice.Agree`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeFiveHoleJointChoice.J`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeFiveHoleJointChoice.Witness`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeFiveHoleJointChoice.approximation`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeFiveHoleJointChoice.joint_finite_choice`
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/NativeFiveHoleCompiler](NativeFiveHoleCompiler.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/NativeHistoryCells](NativeHistoryCells.md)
