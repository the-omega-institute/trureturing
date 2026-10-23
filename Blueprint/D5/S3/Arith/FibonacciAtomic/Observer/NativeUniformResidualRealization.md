# Uniform native residual realization

## Abstract

NativeUniformResidualRealization

**Theorem 1.1 (One tuple reflects a bounded syntax class).**

$$\forall m, M, d: Nat, (\forall A, B: \operatorname{MixedExpr}\left(\operatorname{Fin}\left(m\right)\right), ((\operatorname{weight}\left(A\right) \leq M) \implies ((\operatorname{weight}\left(B\right) \leq M) \implies ((\operatorname{decoration}\left(A\right) \leq d) \implies ((\operatorname{decoration}\left(B\right) \leq d) \implies ((\operatorname{eval}\left(\operatorname{separator}\left(m, M, d\right), A\right) = \operatorname{eval}\left(\operatorname{separator}\left(m, M, d\right), B\right)) \iff (\forall z: \operatorname{Fin}\left(m\right) \to Source, (\operatorname{eval}\left(z, A\right) = \operatorname{eval}\left(z, B\right)))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformResidualRealization.bounded_identity_reflection` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

MixedExpr uses arbitrary finite native grounds, decorated shared residual names and ordered pairs. Weight is the native constructor mass of a ground, zero on a decorated residual, and one plus the two child weights on a pair. Decoration is the largest fixed residual exponent. For weight bound M and decoration bound d, separator assigns name i the native iterate with exponent i times (d+1) of the existing comb of mass M+1. The unary operation is the interpreted native substitution, not a free constructor.

A closed expression has mass at most its weight. A live expression at the separator has mass at least M+1; a live pair has mass at least M+2. Native mass remains invariant under every substitution power. These bounds distinguish closed from live terms and residuals from live pairs. The existing right-spine clock and the disjoint decoration intervals distinguish residual names and exponents. Actual ordered-pair injectivity then permits structural recursion. Closed equalities remain semantic native equalities; no equality of their expression syntax is claimed.

**Theorem 1.2 (Rank instantiation preserves native evaluation).**

$$\forall k, m: Nat, (\forall n: \operatorname{Fin}\left(k\right) \to Nat, (\forall z: \operatorname{Fin}\left(m\right) \to Source, (\forall E: \operatorname{RankedExpr}\left(k, m\right), (\operatorname{eval}\left(z, \operatorname{instantiate}\left(n, E\right)\right) = \operatorname{rankedEval}\left(n, z, E\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformResidualRealization.instantiate_eval` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary dimensions k and m, an unbounded rank vector n, a native residual valuation z and a ranked expression E, evaluating the instantiated expression equals rankedEval n z E. Instantiation replaces each ranked leaf by the native iterate of alpha at its rank plus decoration; the residual leaves, arbitrary grounds and ordered pairs retain their original meanings.

The ranked-leaf equality is the addition law for native substitution iterates. The pair case combines the two child equalities. Uniform residual reflection uses this transport at the separator and at every residual valuation. Finite prefix separation also uses it after binding fixed residual coordinates to grounds and the remaining coordinates to their original residual names.

**Theorem 1.3 (The same tuple works at all atomic rank vectors).**

$$\forall k, m: Nat, (\forall L: \operatorname{List}\left(\operatorname{Prod}\left(\operatorname{RankedExpr}\left(k, m\right), \operatorname{RankedExpr}\left(k, m\right)\right)\right), (\forall n: \operatorname{Fin}\left(k\right) \to Nat, (\forall p: \operatorname{Prod}\left(\operatorname{RankedExpr}\left(k, m\right), \operatorname{RankedExpr}\left(k, m\right)\right), ((p \in L) \implies ((\operatorname{rankedEval}\left(n, \operatorname{uniformSeparator}\left(L\right), \operatorname{fst}\left(p\right)\right) = \operatorname{rankedEval}\left(n, \operatorname{uniformSeparator}\left(L\right), \operatorname{snd}\left(p\right)\right)) \iff (\forall z: \operatorname{Fin}\left(m\right) \to Source, (\operatorname{rankedEval}\left(n, z, \operatorname{fst}\left(p\right)\right) = \operatorname{rankedEval}\left(n, z, \operatorname{snd}\left(p\right)\right))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformResidualRealization.uniform_residual_reflection` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

RankedExpr is the existing MixedExpr on Fin k plus Fin m. The left summand denotes the shared atom T at rank n(j); its residual decoration c denotes T at rank n(j)+c. The right summand denotes the original residual z(i), with its original fixed native power. Grounds remain arbitrary finite trees. Instantiation replaces only the ranked summand by actual native ground trees. Their masses are zero at every rank, so instantiation preserves the input weight without any bound on rank or native leaf count.

ListWeight and listDecoration compute the maxima of both sides and all residual decorations. Every subexpression inherits the side bound because pairing increases weight. UniformSeparator is computed solely from this finite list and its residual dimension, before n is supplied. The list retains duplicates. The theorem quantifies over every unbounded shared rank vector and every listed pair. Empty lists, zero rank dimension, zero residual dimension, repeated names and unused names are all included.

**Theorem 1.4 (Separate nonidentities admit one common completion).**

$$\forall k, m: Nat, (\forall L: \operatorname{List}\left(\operatorname{Prod}\left(\operatorname{RankedExpr}\left(k, m\right), \operatorname{RankedExpr}\left(k, m\right)\right)\right), (\forall n: \operatorname{Fin}\left(k\right) \to Nat, ((\forall p: \operatorname{Prod}\left(\operatorname{RankedExpr}\left(k, m\right), \operatorname{RankedExpr}\left(k, m\right)\right), ((p \in L) \implies (\exists z: \operatorname{Fin}\left(m\right) \to Source, (\operatorname{rankedEval}\left(n, z, \operatorname{fst}\left(p\right)\right) \neq \operatorname{rankedEval}\left(n, z, \operatorname{snd}\left(p\right)\right))))) \iff (\forall p: \operatorname{Prod}\left(\operatorname{RankedExpr}\left(k, m\right), \operatorname{RankedExpr}\left(k, m\right)\right), ((p \in L) \implies (\operatorname{rankedEval}\left(n, \operatorname{uniformSeparator}\left(L\right), \operatorname{fst}\left(p\right)\right) \neq \operatorname{rankedEval}\left(n, \operatorname{uniformSeparator}\left(L\right), \operatorname{snd}\left(p\right)\right)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformResidualRealization.simultaneous_completion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each listed pair, a finite witness of disequality suffices. Uniform reflection makes the same precomputed tuple satisfy the entire finite conjunction. The witnesses in the premise may differ, whereas the conclusion uses exactly one tuple. NativeSimultaneousPrefixSeparation applies this consequence to the whole list after substituting independent prefix contexts. A joint finite witness therefore also gives this common completion, by taking that witness for each pair.

These statements concern exact finite trees and whole-tree equalities. They imply no Presburger elimination, acquisition port, resource optimum, physical realization or full Functional Joint Contact theorem. No bounded-rank or common-clock promise is imposed.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformResidualRealization.bounded_identity_reflection`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformResidualRealization.instantiate_eval`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformResidualRealization.simultaneous_completion`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformResidualRealization.uniform_residual_reflection`
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/NativePrefixIdentityReflection](NativePrefixIdentityReflection.md)
