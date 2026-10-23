# Infinite completion prefixes and finite simultaneous separation

## Abstract

NativeCompletionPrefixLifting

**Theorem 1.1 (The complete reply table is exactly a native filling cylinder).**

$$\forall h: Nat, (\forall T: CompletionTree, (\forall t: Source, ((\forall a: Address, ((\operatorname{length}\left(a\right) \le h) \implies (\operatorname{readout}\left(a, t\right) = \operatorname{completionReadout}\left(a, T\right)))) \iff (\exists w: \operatorname{Frontier}\left(\operatorname{cutoff}\left(h + 1, T\right)\right) \to Source, (t = \operatorname{fill}\left(\operatorname{cutoff}\left(h + 1, T\right), w\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/NativeCompletionPrefixLifting.prefix_cylinder` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

CompletionTree is the pinned Mathlib PFunctor.M for the native polynomial with shape Bool plus Unit. A Boolean shape is a leaf and has no children; the Unit shape is a branch with two ordered Boolean children. This is the unrestricted final coalgebra of consistent finite approximations. The theorem imposes no regularity, computability, finite-state representation or bound on the tree.

CompletionReadout recursively inspects the actual destructor. True leaves report alpha and false leaves report beta. False selects the left child and true selects the right child. Every word is a legal query; any nonempty word under a leaf returns absent. Embed uses the existing FreeMagma Bool Source and preserves its exact readout at every address. The arbitrary M-type reader never uses the upstream default-returning iselect API.

Cutoff d retains every leaf and ordered branch strictly above depth d, leaving a hole only at an originally reached depth-d position. A new depth/address induction proves cutoff equality if and only if all four-valued replies on all words of length less than d agree. The finite embedding's cutoff is exactly the existing decompose pattern. At d equal to h plus one this is precisely the inclusive prefix through depth h, including early terminal children and all absent descendants.

The existing depthEquiv inverse laws supply both directions of the cylinder. Every native filling of cutoff(h+1,T) has exactly the prescribed inclusive table; every finite tree with that table is such a filling. No inverse law, finite readout implementation or original-prefix locality proof is duplicated. No equality of the boundary replies at the unobserved exact depth h+1 is asserted.

**Theorem 1.2 (One finite tuple preserves independent infinite-tree prefixes).**

$$\forall k, r, m: Nat, (\forall L: \operatorname{List}\left(\operatorname{Prod}\left(\operatorname{RankedExpr}\left(k, r + m\right), \operatorname{RankedExpr}\left(k, r + m\right)\right)\right), (\forall n: \operatorname{Fin}\left(k\right) \to Nat, (\forall f: \operatorname{Fin}\left(r\right) \to Source, ((\exists w: \operatorname{Fin}\left(m\right) \to Source, (\forall e: \operatorname{Prod}\left(\operatorname{RankedExpr}\left(k, r + m\right), \operatorname{RankedExpr}\left(k, r + m\right)\right), ((e \in L) \implies (\operatorname{fixedEval}\left(n, f, w, \operatorname{fst}\left(e\right)\right) \neq \operatorname{fixedEval}\left(n, f, w, \operatorname{snd}\left(e\right)\right))))) \implies (\forall T: \operatorname{Fin}\left(m\right) \to CompletionTree, ((\forall i: \operatorname{Fin}\left(m\right), (\operatorname{HasInfiniteBranch}\left(\operatorname{T}\left(i\right)\right))) \implies (\forall h: \operatorname{Fin}\left(m\right) \to Nat, (\exists z: \operatorname{Fin}\left(m\right) \to Source, ((\forall i: \operatorname{Fin}\left(m\right), (\forall a: Address, ((\operatorname{length}\left(a\right) \le \operatorname{h}\left(i\right)) \implies (\operatorname{readout}\left(a, \operatorname{z}\left(i\right)\right) = \operatorname{completionReadout}\left(a, \operatorname{T}\left(i\right)\right))))) \land (\forall e: \operatorname{Prod}\left(\operatorname{RankedExpr}\left(k, r + m\right), \operatorname{RankedExpr}\left(k, r + m\right)\right), ((e \in L) \implies (\operatorname{fixedEval}\left(n, f, z, \operatorname{fst}\left(e\right)\right) \neq \operatorname{fixedEval}\left(n, f, z, \operatorname{snd}\left(e\right)\right)))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/NativeCompletionPrefixLifting.simultaneous_prefix_disequality` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The input fixes arbitrary natural ranks n and arbitrary finite coordinates f, together with one finite joint witness for the whole finite list of disequalities. RankedExpr and fixedEval are the existing native mixed-expression syntax and interpretation. The residual coordinates are partitioned into fixed Fin r and live Fin m coordinates by the existing sum equivalence. The fixed coordinates never change; repeated uses of a residual name use that same original coordinate and its same holes.

Each supplied completion has an actual infinite branch: there is a function from Nat to Bool whose finite initial word exists at every depth. A new induction on a present address gives a reached frontier position in each cutoff. Applying it to that supplied branch proves liveness at every cut without compactness or a new Koenig assumption. Infinity is not replaced by liveness at one requested depth.

For each independently chosen height h(i), use cutoff(h(i)+1,T(i)). Apply the existing simultaneous_prefix_separation once to the complete list and all these independent live patterns. Its canonical prefixTuple is a finite filling in every coordinate. The exact cylinder bridge transports these fillings to the original complete four-valued tables. The same tuple satisfies every listed disequality at the unchanged n and f.

The list may be empty or contain repetitions. Residual names may repeat or remain unused. There is no finite rank bound and no synchronization of the coordinate heights. When m is zero the live tuple is empty and the fixed f itself carries the supplied disequalities. When the list is empty every finite tuple extending the prescribed tables satisfies its empty conjunction.

This establishes the completion-tree prefix-preserving simultaneous disequality statement. It makes no claim about the full Functional Joint Contact theorem, Presburger elimination, acquisition costs or resource guarantees. The bridge and simultaneous conclusion are repository-derived applications of the pinned final-coalgebra machinery and the existing native finite separation theorem; no literature originality is claimed. An unknown audit continuation is not a theorem of undecidability or inexhaustibility.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeCompletionPrefixLifting.prefix_cylinder`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeCompletionPrefixLifting.simultaneous_prefix_disequality`
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/NativeSimultaneousPrefixSeparation](NativeSimultaneousPrefixSeparation.md)
