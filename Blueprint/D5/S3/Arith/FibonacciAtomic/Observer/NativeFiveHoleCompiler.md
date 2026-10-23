# Exact finite compilation of whole five-hole strata

## Abstract

NativeFiveHoleCompiler

**Definition 1.1 (The entire finite negative table).**

$$\forall s: Bool, (\forall H: History, (\forall t: \operatorname{Fin}\left(2\right) \to Source, ((\operatorname{Negatives}\left(s, H, t\right)) \iff (\forall e: \operatorname{Prod}\left(Expr, Expr\right), ((e \in \operatorname{table}\left(s, H\right)) \implies (\operatorname{rankedEval}\left(\operatorname{ranks}\left(\right), t, \operatorname{fst}\left(e\right)\right) \neq \operatorname{rankedEval}\left(\operatorname{ranks}\left(\right), t, \operatorname{snd}\left(e\right)\right)))))))$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeFiveHoleCompiler.Negatives` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Expr is RankedExpr with zero ranks and two shared residual names Y,Z. FY and FZ pair the ground alpha with the corresponding residual at exponent one. The false side orders Y,Z,FY,FZ; the true side orders FY,Y,Z,FZ. Six contains comparisons (0,1),(0,2),(0,3),(1,2),(1,3),(2,3). Table then appends every occurrence of IndexedHistory, in its original order, shifting each corresponding hole expression by its supplied epoch. No repeated or redundant comparison is removed.

Shift transforms ground alpha as well as adding the residual exponent. The existing eval_shift supplies its evaluation law. The true-side conjunction explicitly permutes all six inequalities, reversing the necessary comparisons.

**Theorem 1.2 (Exact compilation on the original whole strata).**

$$\forall s: Bool, (\forall H: History, (\forall u: Source, ((\operatorname{Stratum}\left(s, H, u\right)) \iff (\exists t: \operatorname{Fin}\left(2\right) \to Source, ((u = \operatorname{source}\left(s, \operatorname{t}\left(0\right), \operatorname{t}\left(1\right)\right)) \land (\operatorname{Negatives}\left(s, H, t\right)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/NativeFiveHoleCompiler.stratum_compile_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Both directions start with the original Stratum. Raw-source extraction and full-label correspondence precede the compiler. Epoch-hole transport retains both guards, while exact list reconstruction preserves every original negative record.

**Theorem 1.3 (One finite structural test decides the entire table).**

$$\forall s: Bool, (\forall H: History, ((\operatorname{Negatives}\left(s, H, \operatorname{uniformSeparator}\left(\operatorname{table}\left(s, H\right)\right)\right)) \iff (\exists t: \operatorname{Fin}\left(2\right) \to Source, (\operatorname{Negatives}\left(s, H, t\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/NativeFiveHoleCompiler.separator_exact` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Uniform residual reflection makes every equality at the computed separator universal over all residual tuples. A failed comparison therefore excludes the whole stratum; a passing separator is an explicit finite seed for all its negatives. This finite test concerns these exact tables and asserts no general NSF solver.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeFiveHoleCompiler.Negatives`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeFiveHoleCompiler.separator_exact`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeFiveHoleCompiler.stratum_compile_iff`
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/NativeFiveHoleFiber](NativeFiveHoleFiber.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/NativeSimultaneousPrefixSeparation](NativeSimultaneousPrefixSeparation.md)
