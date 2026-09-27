# Guarded Pair Crossings

## Abstract

Reduced crossings constrain guarded strand traces.

In a reduced adjacent-swap word the same pair of values cannot cross twice. A final-order guard consequently prevents the tracked value from stepping right.

**Theorem 1.1 (Guarded strand endpoint).**

$$\operatorname {Bounds}\left(n, i, t\right) \land i \le \operatorname {oneBased}\left(x\right) \land \operatorname {position}\left(n, t\right) = x \land \operatorname {Reduced}\left(n, b\right) \land \operatorname {prod}\left(n, b\right) \operatorname {position}\left(n, i\right) = x \land \operatorname {FinalPrefixGuard}\left(n, i, x, b\right) \implies \operatorname {leftOnly}\left(t, b\right) \land \operatorname {traceEnd}\left(t, b\right) = i$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Permutations/MamedeCrossing.guarded_walk_endpoint` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Bounds means 1<=i,t<=n+1, and oneBased(x)=x.val+1. FinalPrefixGuard requires every initial position r with r+1<i to finish strictly below x. The conclusion holds for the actual reduced word b, without assuming a decomposition of b.

## References

- Truth anchor: `D5/S1/Words/Permutations/MamedeCrossing.guarded_walk_endpoint`
- Dependency: [D5/S1/Words/Permutations/MamedeGuardedWalk](MamedeGuardedWalk.md)
- Dependency: [D5/S1/Words/Permutations/MamedeOrderChange](MamedeOrderChange.md)
