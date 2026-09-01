# Observer Collision Order

## Abstract

Observer collision order is the p-adic valuation, with a positive nontrivial witness.

**Theorem 1.1 (Collision order is the p-adic valuation and is realizable).**

$$\begin{gathered}(\forall p, r \in \mathbb{N},\\{}a, b \in \mathbb{Z},\\{}\operatorname{Prime}\left(p\right) \land \operatorname{precisionReading}\left(p, r, a\right) = \operatorname{precisionReading}\left(p, r, b\right) \land \operatorname{precisionReading}\left(p, r + 1, a\right) \neq \operatorname{precisionReading}\left(p, r + 1, b\right) \Rightarrow \operatorname{padicValInt}\left(p, a - b\right) = r) \land\\{}(\exists p, r \in \mathbb{N}, a, b \in \mathbb{Z},\\{}p = 2 \land r = 2 \land a = 0 \land b = 4 \land\\{}1 \leq r \land \operatorname{Prime}\left(p\right) \land \operatorname{precisionReading}\left(p, r, a\right) = \operatorname{precisionReading}\left(p, r, b\right) \land \operatorname{precisionReading}\left(p, r + 1, a\right) \neq \operatorname{precisionReading}\left(p, r + 1, b\right) \land\\{}\operatorname{padicValInt}\left(p, a - b\right) = r).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Congruence/ObserverCollisionOrder.observer_collision_order_eq_padic_valuation_and_exists` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a prime p, suppose two integer readings agree modulo p^r but disagree modulo p^(r + 1). Their difference is then divisible by p^r and not by p^(r + 1), so its p-adic valuation is r.

The proof imports the stronger precision-reading equivalence, which characterizes agreement at every precision by an inequality against padicValInt. It introduces no parallel collision-order or valuation definition.

The explicit readings a = 0 and b = 4 at p = 2 agree at order two and disagree at order three. This realizes the definition at the positive nontrivial order r = 2.

The source atom's separate golden-ramification sentence is not included: the atom supplies no self-contained number-field hypotheses from which that statement could be formalized.

## References

- Truth anchor: `D5/S3/Arith/Congruence/ObserverCollisionOrder.observer_collision_order_eq_padic_valuation_and_exists`
- Dependency: [D5/S3/Arith/Congruence/PadicPrecisionBlindSpot](PadicPrecisionBlindSpot.md)
