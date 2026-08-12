# The First Hole Is Bounded by the Budget, with Equality for Prefix Names

## Abstract

The first hole of a finite support never exceeds its budget, with equality exactly for prefix names.

**Theorem 1.1 (The first hole is at most the budget, and equals it iff the support is a prefix).**

$$\gamma(S) \le \lvert S\rvert \land (\gamma(S) = \lvert S\rvert \iff S = \operatorname{range}(\lvert S\rvert))$$

*Proof.* Machine-checked in Lean as `D5/S0/Naming/FirstHoleBound.firstHole_le_card_and_eq_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a finite support S of naturals with budget m = |S|, the first hole gamma(S) = min(N \ S) — the least natural NOT in S, i.e. the first unnamed coordinate — never exceeds the budget: gamma(S) <= |S|. Equality holds exactly when S is the prefix (initial segment) {0, ..., m-1} = range m. No nonemptiness hypothesis is needed: the empty support gives gamma(empty) = 0 = |empty| with empty = range 0.

The bound is a pigeonhole on the defining Nat.find: if gamma(S) exceeded |S|, then every m <= |S| would lie below the first hole and hence in S, so range (|S|+1) would be a subset of S, forcing |S|+1 <= |S|. In the equality case range |S| is a subset of S, and equal cardinalities upgrade the inclusion to S = range |S|; the converse is that the first hole of an initial segment {0, ..., c-1} is c.

Only this combinatorial first-hole characterization is recorded. The measure clause mu(G(t)) = n^(-|S|) (the volume sees only the budget, not the support position) and the metric formula diam(G(t)) = 2^(-gamma(S)) — whose equality case is read metrically as 'prefix names uniquely minimize the diameter' — are the atom's remaining, uncovered content.

## References

- Truth anchor: `D5/S0/Naming/FirstHoleBound.firstHole_le_card_and_eq_iff`
