# Simultaneous finite prefix separation

## Abstract

NativeSimultaneousPrefixSeparation

**Theorem 1.1 (Independent live patterns preserve a finite conjunction).**

$$\forall k, r, m: Nat, (\forall L: \operatorname{List}\left(\operatorname{Prod}\left(\operatorname{RankedExpr}\left(k, r + m\right), \operatorname{RankedExpr}\left(k, r + m\right)\right)\right), (\forall P: (\operatorname{Fin}\left(k\right) \to Nat) \to Prop, (\forall n: \operatorname{Fin}\left(k\right) \to Nat, (\forall f: \operatorname{Fin}\left(r\right) \to Source, (\forall d: \operatorname{Fin}\left(m\right) \to Nat, (\forall p: (i: \operatorname{Fin}\left(m\right)) \to \operatorname{Pattern}\left(\operatorname{d}\left(i\right)\right), ((\forall i: \operatorname{Fin}\left(m\right), (\operatorname{Nonempty}\left(\operatorname{Frontier}\left(\operatorname{p}\left(i\right)\right)\right))) \implies ((\exists z: \operatorname{Fin}\left(m\right) \to Source, ((\operatorname{P}\left(n\right)) \land (\forall e: \operatorname{Prod}\left(\operatorname{RankedExpr}\left(k, r + m\right), \operatorname{RankedExpr}\left(k, r + m\right)\right), ((e \in L) \implies (\operatorname{fixedEval}\left(n, f, z, \operatorname{fst}\left(e\right)\right) \neq \operatorname{fixedEval}\left(n, f, z, \operatorname{snd}\left(e\right)\right)))))) \iff ((\operatorname{P}\left(n\right)) \land ((\forall i: \operatorname{Fin}\left(m\right), (\operatorname{fst}\left(\operatorname{decompose}\left(\operatorname{d}\left(i\right), \operatorname{prefixTuple}\left(n, f, d, p, L, i\right)\right)\right) = \operatorname{p}\left(i\right))) \land (\forall e: \operatorname{Prod}\left(\operatorname{RankedExpr}\left(k, r + m\right), \operatorname{RankedExpr}\left(k, r + m\right)\right), ((e \in L) \implies (\operatorname{fixedEval}\left(n, f, \operatorname{prefixTuple}\left(n, f, d, p, L\right), \operatorname{fst}\left(e\right)\right) \neq \operatorname{fixedEval}\left(n, f, \operatorname{prefixTuple}\left(n, f, d, p, L\right), \operatorname{snd}\left(e\right)\right))))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/NativeSimultaneousPrefixSeparation.simultaneous_prefix_separation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The input fixes an arbitrary rank vector n, finite coordinates f, an arbitrary rank policy P, and a finite list of decorated mixed expression pairs. The original residual domain is split into the fixed Fin r coordinates and the remaining Fin m coordinates by the executable sum equivalence. FixedExpr evaluates the fixed coordinates into grounds while retaining each live residual name and every native decoration. The policy P(n) is identical on both sides.

Each live original coordinate has its own depth and native pattern. A depth-zero pattern is one hole; a positive-depth leaf is that actual leaf and has no holes below it; a pair keeps the two ordered child patterns. HoleCount and HoleEquiv count and number these reached holes recursively, left before right. HoleNumbering combines the independent coordinate frontiers with the executable finSigmaFinEquiv. No choice of an equivalence from a finite type is used to compute the tuple.

PatternExpr replaces each reached hole by its own zero-decorated name. Repeated uses of an original residual always reuse that same pattern and the same hole names. Shift pushes the actual native substitution through a context, using the native pair homomorphism and addition of iterate exponents. Bind then satisfies the exact substitution/evaluation bridge. Expanded applies this bridge after fixing n and f, and ExpandedList preserves every listed occurrence.

If one expanded equality were universal on the entire independent hole product, the existing prefix identity reflection would make the original equality universal on every live residual valuation. This contradicts the supplied finite witness. Uniform residual realization is applied once to the entire expanded list, giving one common hole tuple. PrefixTuple fills each supplied pattern with its assigned coordinates of this same tuple. The exact depth decomposition returns each original pattern, including every early leaf and its absent descendants.

This proves the finite live-pattern construction. Its conclusion preserves the supplied patterns and all listed disequalities at the fixed arbitrary n and f, including zero dimensions and the empty list. The correspondence from an actual infinite completion tree and its finite inclusive reply prefix through depth h to a live Pattern(h+1), preserving early terminal children and absent regions, is not supplied by this theorem. That correspondence remains necessary for the full completion-tree formulation of Signed Local Prefix Lifting Lemma 2.1. A renamed live-pattern assumption does not discharge it.

The result concerns exact native whole-tree equalities and independent Cartesian hole fillings. It provides no acquisition, resource bound, arithmetic elimination, support closure or full Functional Joint Contact theorem. Unknown audit continuation does not assert emptiness or undecidability.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSimultaneousPrefixSeparation.simultaneous_prefix_separation`
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformResidualRealization](NativeUniformResidualRealization.md)
