# Functional native expressions and root links

## Abstract

OriginalFunctionalNormalization

**Theorem 1.1 (Distribution of every fixed native power).**

$$\forall k: Nat, (\forall m: Nat, (\forall mode: \operatorname{Function}\left(\operatorname{Fin}\left(k\right), Bool\right), (\forall p: \operatorname{Function}\left(\operatorname{Fin}\left(k\right), Nat\right), (\forall v: \operatorname{Function}\left(\operatorname{Fin}\left(m\right), CompletionTree\right), (\forall a: Nat, (\forall e: \operatorname{Expr}\left(k, m\right), (\operatorname{value}\left(mode, p, v, \operatorname{power}\left(a, e\right)\right) = \operatorname{rhoIterate}\left(a, \operatorname{value}\left(mode, p, v, e\right)\right))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/OriginalFunctionalNormalization.value_power` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In the formulas, Function(A,B) is the type of functions from A to B, and rhoIterate(a,X) is the a-fold native substitution of X. Expressions retain finite grounds, named parameter atoms, a literal Omega, decorated state variables and ordered pairs. A parameter name has its fixed finite or divergent mode. Literal Omega is available even when there are no parameters. The power operation distributes the actual native substitution over pairs, composes variable decorations, shifts finite atoms and evaluates finite grounds. It introduces no independent unary tree constructor.

**Theorem 1.2 (Simultaneous substitution preserves evaluation).**

$$\forall k: Nat, (\forall m: Nat, (\forall mode: \operatorname{Function}\left(\operatorname{Fin}\left(k\right), Bool\right), (\forall p: \operatorname{Function}\left(\operatorname{Fin}\left(k\right), Nat\right), (\forall v: \operatorname{Function}\left(\operatorname{Fin}\left(m\right), CompletionTree\right), (\forall s: \operatorname{Function}\left(\operatorname{Fin}\left(m\right), \operatorname{Expr}\left(k, m\right)\right), (\forall e: \operatorname{Expr}\left(k, m\right), (\operatorname{value}\left(mode, p, v, \operatorname{subst}\left(s, e\right)\right) = \operatorname{value}\left(mode, p, \operatorname{reconstruct}\left(mode, p, s, v\right), e\right))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/OriginalFunctionalNormalization.value_subst` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A reconstruction is one expression for each original state name. Simultaneous substitution evaluates that expression with the same valuation at every occurrence. Parameter names and their coincidences are retained; ordered pairs may evaluate to atomic values. FunctionalCase also retains the arithmetic guard and a finite family of expressions for every designated original residual.

**Theorem 1.3 (Exact elimination of all defining root links).**

$$\forall k: Nat, (\forall m: Nat, (\forall E: \operatorname{Definitions}\left(k, m\right), (\exists N: \operatorname{Definitions}\left(k, m\right), (\exists R: \operatorname{Function}\left(\operatorname{Fin}\left(m\right), \operatorname{Expr}\left(k, m\right)\right), ((\operatorname{PairGuarded}\left(N\right)) \land (\forall mode: \operatorname{Function}\left(\operatorname{Fin}\left(k\right), Bool\right), (\forall p: \operatorname{Function}\left(\operatorname{Fin}\left(k\right), Nat\right), (\forall u: \operatorname{Function}\left(\operatorname{Fin}\left(m\right), CompletionTree\right), ((\operatorname{Solution}\left(N, mode, p, u\right)) \implies (\operatorname{Solution}\left(E, mode, p, \operatorname{reconstruct}\left(mode, p, R, u\right)\right)))))) \land (\forall mode: \operatorname{Function}\left(\operatorname{Fin}\left(k\right), Bool\right), (\forall p: \operatorname{Function}\left(\operatorname{Fin}\left(k\right), Nat\right), (\forall v: \operatorname{Function}\left(\operatorname{Fin}\left(m\right), CompletionTree\right), ((\operatorname{Solution}\left(E, mode, p, v\right)) \implies ((\operatorname{Solution}\left(N, mode, p, v\right)) \land (\operatorname{reconstruct}\left(mode, p, R, v\right) = v)))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/OriginalFunctionalNormalization.root_link_normalization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A functional system has at most one defining expression for each state; undefined states remain unrestricted. The normalized system has no decorated variable as a defining root. Its remaining state occurrences are strictly below a pair. Every normalized solution reconstructs an original solution. Conversely, an original solution satisfies the normalized equations and is fixed by reconstruction. Substituting the same reconstruction into every designated residual preserves all original coordinates.

Eliminating a nonself link substitutes its decorated target everywhere and retains its reconstruction. A zero self-link imposes no condition and becomes free. A positive self-link forces the actual leafless Omega: iteration of its positive period and native eventual full prefixes exclude every leaf. Each elimination strictly decreases the finite set of root-link definitions. Thus normalization needs no supplied graph rank, finite expansion bound, solvability premise or fixed point.

The system and reconstruction depend on syntax alone, independently of natural parameter values. Both semantic directions hold for all finite state and parameter counts, including zero, with unrestricted completed free values. The arithmetic guard is retained as a condition on the original parameter tuple; it is never replaced by existence of a solution. This is a native semantic normalization result, with no external novelty claim.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/OriginalFunctionalNormalization.root_link_normalization`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/OriginalFunctionalNormalization.value_power`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/OriginalFunctionalNormalization.value_subst`
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/CompletionHomogeneousFixedPoints](../CompletionHomogeneousFixedPoints.md)
