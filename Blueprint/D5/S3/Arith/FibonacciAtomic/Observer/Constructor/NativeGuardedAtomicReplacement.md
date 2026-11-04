# Bounded atomic terminals survive simultaneous free-value replacement

## Abstract

NativeGuardedAtomicReplacement

**Theorem 1.1 (Small finite atomic results depend only on small atomic free values).**

$$\forall k: Nat, (\forall m: Nat, (\forall S: \operatorname{System}\left(k, m\right), (\forall p: \operatorname{Fin}\left(k\right) \to Nat, ((\operatorname{Guarded}\left(S\right)) \implies (\forall v: \operatorname{Fin}\left(m\right) \to CompletionTree, (\forall w: \operatorname{Fin}\left(m\right) \to CompletionTree, ((\operatorname{Satisfies}\left(S, p, v\right)) \implies ((\operatorname{Satisfies}\left(S, p, w\right)) \implies (\forall B: Nat, ((\forall i: \operatorname{Fin}\left(m\right), ((\operatorname{at}\left(S, i\right) = none) \implies (\forall j: Nat, ((j \le B) \implies ((\operatorname{at}\left(v, i\right) = \operatorname{atomic}\left(j\right)) \implies (\operatorname{at}\left(w, i\right) = \operatorname{at}\left(v, i\right))))))) \implies (\forall E: \operatorname{Expression}\left(k, m\right), (\forall j: Nat, ((j \le B) \implies ((\operatorname{evaluate}\left(p, v, E\right) = \operatorname{atomic}\left(j\right)) \implies (\operatorname{evaluate}\left(p, w, E\right) = \operatorname{evaluate}\left(p, v, E\right))))))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeGuardedAtomicReplacement.atomic_replacement` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Use the actual unrestricted native completion, the distributed expressions and the optional guarded definitions of NativeGuardedFreeExtension. Fix one system S, one natural parameter tuple p and two simultaneous solutions v and w of all of its defining equations. They may differ at finite or arbitrary infinite values. The natural bound B imposes no restriction on either full solution or its state values.

Assume only that, whenever an undefined state has value atomic(j) in v with j at most B, its value in w is unchanged. Then every expression E whose value in v is atomic(j) with j at most B has that same value in w. Repeated state occurrences remain included. Any reconstruction already represented in this expression syntax is included; the theorem does not construct an original-to-normalized reconstruction map. Parameters, finite grounds, Omega, nonnegative decorators and ordered pairs have their actual native meanings in both evaluations.

An actual power rho(a,X) equal to atomic(j) has a unique finite atomic predecessor atomic(l), with l+a=j. Native finiteness reflection first makes X finite. The invariant gamma of its finite source is zero, so the existing atomic-rank classification identifies the source as atomic. Injectivity and composition of native iterates give the exact index equation. In particular the predecessor rank cannot exceed j.

A pair equal to atomic(j) has j=n+2 and children atomic(n+1) and atomic(n). Expression induction therefore propagates atomic bounds through the explicit pair skeleton and its decorated state occurrences. To compare states satisfying definitions, strong induction on the terminal rank unfolds their guarded defining right sides. A pair root strictly reduces the rank before any state dependency is compared. Constants are unchanged, and undefined states use the stated hypothesis. Thus an infinite recursive dependency cannot be hidden in a finite atomic terminal.

For a saturation mode with exceptional atoms through S+1, take B=S+1. A live free value lies outside that finite set, so it cannot occur in a dependency responsible for any accepted image terminal of threshold at most S. Replacing live free values by Omega therefore preserves each such terminal. This theorem supplies terminal preservation; acceptance of infinite recursive image parses requires the separate actual-image coinduction argument.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeGuardedAtomicReplacement.atomic_replacement`
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeGuardedFreeExtension](NativeGuardedFreeExtension.md)
