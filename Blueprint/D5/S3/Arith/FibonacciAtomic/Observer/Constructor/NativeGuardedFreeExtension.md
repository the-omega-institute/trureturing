# Arbitrary free values have a unique guarded native extension

## Abstract

NativeGuardedFreeExtension

**Theorem 1.1 (Simultaneous existence and uniqueness on the unrestricted completion).**

$$\forall k: Nat, (\forall m: Nat, (\forall S: \operatorname{System}\left(k, m\right), (\forall p: \operatorname{Fin}\left(k\right) \to Nat, ((\operatorname{Guarded}\left(S\right)) \implies (\forall f: \operatorname{Fin}\left(m\right) \to CompletionTree, (\exists v: \operatorname{Fin}\left(m\right) \to CompletionTree, (((\operatorname{Satisfies}\left(S, p, v\right)) \land (\operatorname{Extends}\left(S, f, v\right))) \land (\forall w: \operatorname{Fin}\left(m\right) \to CompletionTree, (((\operatorname{Satisfies}\left(S, p, w\right)) \land (\operatorname{Extends}\left(S, f, w\right))) \implies (w = v))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeGuardedFreeExtension.guarded_extension` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

CompletionTree is the unrestricted native PFunctor.M completion. A finite system S has m states and at most one defining expression per state. Expressions are the existing distributed native syntax: a finite ground, a parameter token with a fixed natural offset, a nonnegative power of a named state, or an ordered pair. The first k tokens denote atomic(p(j)+c); the last token denotes Omega, independently of its offset. Thus parameter values are actual finite atoms, while Omega is the actual leafless completed tree. All repeated state and parameter names retain their shared values and all pair occurrences remain ordered.

Guarded(S) says precisely that no defining right side is a decorated state at its root. Every right side that depends on states therefore has an explicit pair root. Grounds and constant tokens need no recursive guard. This condition describes a normalized system; it does not assume that a transformation from an original system has already been proved.

For every natural parameter tuple p and every assignment f of arbitrary completed values, there exists exactly one state tuple v satisfying all definitions and agreeing with f at every undefined state. The supplied f is unrestricted: finite, infinite and non-rational free values are included. Values of f at defined states impose no extra condition. Empty state or parameter tuples have their literal meanings.

For existence, specialize each finite parameter token to its native finite ground and represent Omega by one extra undefined state. Prescribe the actual free values and Omega on that closed boundary. The native whole-system boundary extension gives a joint solution, and the specialization identity transports every original equation back to the parameter expression. No equation or auxiliary coordinate is discarded.

For uniqueness, compare two joint solutions with the same prescribed free values. Induction over every cutoff depth proves equality of all state prefixes simultaneously. The depth-zero cutoffs agree without a premise. At an undefined state the values agree by the boundary condition; at a constant right side they agree identically. At an explicit pair, the induction hypothesis on its children supplies the next cutoff because pairing gains one level. Native expression evaluation preserves equality of a cutoff, using the existing exact finite-prefix evaluator. Equality at every cutoff gives equality of every four-valued address reply, hence equality of the completed trees.

The theorem supplies the arbitrary-free-value guarded extension used in canonical finite-exception assignments. It asserts no root-link normalization, original-state reconstruction equivalence, atomic replacement, image-filter preservation or full finite-exception existence equivalence. Those conclusions require their own relations on the same original system and parameter.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeGuardedFreeExtension.guarded_extension`
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeFunctionalEffectivePrefix](NativeFunctionalEffectivePrefix.md)
