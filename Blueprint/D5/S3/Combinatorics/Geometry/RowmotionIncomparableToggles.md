# Commuting incomparable interval-closed toggles

## Abstract

Interval-closed toggles at incomparable elements commute in every partially ordered set.

Let P be any partially ordered set. A subset S is order-convex, written OrdConnected(S), when every point between two members of S also belongs to S. The operation toggle(x,S) is the existing interval-closed toggle: form the symmetric difference of S with the singleton containing x if that set is order-convex, and otherwise leave S unchanged. This legality condition is retained at both stages of each composition.

**Theorem 1.1 (Commutation at incomparable points).**

$$\forall P \in Type,\; [\operatorname{PartialOrder}\left(P\right)], \forall x \in P,\; \forall y \in P,\; \forall S \in \operatorname{Set}\left(P\right),\; ((\neg (x \le y)) \land ((\neg (y \le x)) \land (\operatorname{OrdConnected}\left(S\right)))) \Rightarrow (\operatorname{toggle}\left(x, \operatorname{toggle}\left(y, S\right)\right) = \operatorname{toggle}\left(y, \operatorname{toggle}\left(x, S\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/RowmotionIncomparableToggles.incomparable_toggles_commute` (`✓ std3`). ∎

*Citation.* Nadia Lafrenière, Joel Brewster Lewis, Erin McNicholas, Jessica Striker, Amanda Welch (2025). *Interval-closed set rowmotion and homomesy on products of two chains*. DOI: [10.48550/arXiv.2505.04000](https://doi.org/10.48550/arXiv.2505.04000). URL: <https://arxiv.org/abs/2505.04000v1>.

*Commentary.*

The incomparable-element direction of Lemma 1.8 of Lafreniere, Lewis, McNicholas, Striker and Welch, Interval-closed set rowmotion and homomesy on products of two chains, gives this commutation relation for finite partially ordered sets. The proof below also covers arbitrary partial orders and arbitrary order-convex subsets without a finiteness assumption.

Legality of a flip at x depends only on membership at points comparable with x, provided the starting set is order-convex. To see this, compare two order-convex sets agreeing at all those points. In a proposed interval after the flip, if an endpoint or the intermediate point equals x, all memberships needed for that case lie at points comparable with x and can be transferred. If none equals x, the interval follows from the order-convexity of the starting set. Thus legality transfers in both directions.

A toggle at y preserves order-convexity. When x and y are incomparable, it also preserves membership at every point comparable with x, so it preserves the legality of flipping x. Interchanging x and y gives the reverse statement. There are then four cases: if both flips are legal, the two singleton symmetric differences commute; if only one is legal, both compositions perform precisely that flip; and if neither is legal, both compositions retain S. The argument includes empty and infinite subsets.

## References

- Truth anchor: `D5/S3/Combinatorics/Geometry/RowmotionIncomparableToggles.incomparable_toggles_commute`
- Dependency: [D5/S3/Combinatorics/Geometry/RowmotionEndpointTransport](RowmotionEndpointTransport.md)
