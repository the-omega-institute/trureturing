# Reduced Moment Identities

## Abstract

Deleting one index converts its gap-weighted moment into a difference of two power sums, either over the reduced set or, under membership, the full set.

**Theorem 1.1 (Moment identity over the erased set).**

$$\begin{gathered}\forall iota: Type, [\operatorname{DecidableEq}\left(iota\right)],\\\forall R: Type, [\operatorname{CommRing}\left(R\right)],\\\forall S: \operatorname{Finset}\left(iota\right), i: iota,\\x: iota \to R, n: \mathbb{N},\\\sum_{j \in \operatorname{erase}\left(S, i\right)} x\left(j\right) \cdot {x\left(i\right) - x\left(j\right)} \cdot x\left(j\right)^{n} = x\left(i\right) \cdot \sum_{j \in \operatorname{erase}\left(S, i\right)} x\left(j\right)^{n + 1} - \sum_{j \in \operatorname{erase}\left(S, i\right)} x\left(j\right)^{n + 2}.\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S0/Asymptotics/ReducedMomentIdentity.reducedMoment_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

After the distinguished index is erased, distributing each term turns the gap-weighted moment into the distinguished value times the next power sum minus the following power sum.

The proposition motivating this statement appeared in commentary with positivity and order assumptions. This algebraic identity itself requires neither of those assumptions.

**Theorem 1.2 (Moment identity over the full set).**

$$\begin{gathered}\forall iota: Type, [\operatorname{DecidableEq}\left(iota\right)],\\\forall R: Type, [\operatorname{CommRing}\left(R\right)],\\\forall S: \operatorname{Finset}\left(iota\right), i: iota,\\x: iota \to R, n: \mathbb{N},\\i \in S \implies\\\sum_{j \in \operatorname{erase}\left(S, i\right)} x\left(j\right) \cdot {x\left(i\right) - x\left(j\right)} \cdot x\left(j\right)^{n} = x\left(i\right) \cdot \sum_{j \in S} x\left(j\right)^{n + 1} - \sum_{j \in S} x\left(j\right)^{n + 2}.\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S0/Asymptotics/ReducedMomentIdentity.reducedMoment_eq_of_mem` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

When the distinguished index belongs to the finite set, its gap is zero, so its summand contributes nothing and may be inserted into or removed from the sum.

For every other index, distributivity and the successor rules for powers reduce the summand to the displayed difference of full power sums.

## References

- Truth anchor: `D5/S0/Asymptotics/ReducedMomentIdentity.reducedMoment_eq`
- Truth anchor: `D5/S0/Asymptotics/ReducedMomentIdentity.reducedMoment_eq_of_mem`
