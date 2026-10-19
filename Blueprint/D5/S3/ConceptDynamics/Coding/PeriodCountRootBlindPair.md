# A same-group pair of actual history systems

## Abstract

Ordinary periodic counts do not determine equivariant square roots even with a fixed deck group.

**Definition 1.1 (One original numbered loop).**

$$\forall H \in Type,\; [\operatorname{Group}\left(H\right)]\forall g \in H,\; \operatorname{loop}\left(g\right) = \operatorname{oneByOneMatrix}\left(\operatorname{single}\left(g, 1\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/PeriodCountRootBlindPair.loop` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

loop(g) is the one-by-one natural group-ring matrix whose only entry is single(g,1). It has one vertex and one numbered edge labelled g. expandedGraph and History are the existing repository structures; no new symbolic dynamics carrier is substituted.

**Definition 1.2 (Roots on all actual bilateral histories).**

$$\forall H \in Type,\; [\operatorname{Group}\left(H\right)]\forall g \in H, k \in Nat,\; \operatorname{HasEquivariantRoot}\left(g, k\right) = \operatorname{existsDeckEquivariantTimeRoot}\left(\operatorname{loop}\left(g\right), k\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/PeriodCountRootBlindPair.HasEquivariantRoot` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

existsDeckEquivariantTimeRoot(C,k) means there exists f:History(expandedGraph C)->History(expandedGraph C) such that f(groupHistory(C,a,x))=groupHistory(C,a,f(x)) for every a and x, and f iterated k times equals the original shift. Every base path of loop(g) is the same constant numbered edge. The equivalence from its LiftOrbit at d=1 to all actual histories transports actualAtlas. The exact root criterion therefore reduces to existence of b in H with b^k=g, for this entire system.

**Definition 1.3 (The same deck group in both systems).**

$$DeckGroup = \operatorname{Multiplicative}\left(\operatorname{Prod}\left(\operatorname{ZMod}\left(4\right), \operatorname{ZMod}\left(2\right)\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/PeriodCountRootBlindPair.DeckGroup` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

DeckGroup is C4 times C2, written multiplicatively. The labels are g=(2,0) and h=(0,1) in additive coordinates. Both have order two. The first is the square of (1,0); the second cannot be a square because the second coordinate of every square is zero.

**Definition 1.4 (The proposed sufficiency of ordinary period data).**

$$claim = \left(\forall g \in DeckGroup, h \in DeckGroup,\; ((\forall x \in \operatorname{History}\left(\operatorname{expandedGraph}\left(\operatorname{loop}\left(g\right)\right)\right),\; \operatorname{minimalPeriod}\left(\operatorname{shift}\left(\operatorname{expandedGraph}\left(\operatorname{loop}\left(g\right)\right)\right), x\right) = 2) \implies (((\forall x \in \operatorname{History}\left(\operatorname{expandedGraph}\left(\operatorname{loop}\left(h\right)\right)\right),\; \operatorname{minimalPeriod}\left(\operatorname{shift}\left(\operatorname{expandedGraph}\left(\operatorname{loop}\left(h\right)\right)\right), x\right) = 2) \implies (((\forall j \in Nat,\; ((\operatorname{Positive}\left(j\right)) \implies (\operatorname{NatCard}\left(\operatorname{TwistedPeriod}\left(\operatorname{loop}\left(g\right), 1, j\right)\right) = \operatorname{NatCard}\left(\operatorname{TwistedPeriod}\left(\operatorname{loop}\left(h\right), 1, j\right)\right)))) \implies ((\operatorname{HasEquivariantRoot}\left(g, 2\right) \iff \operatorname{HasEquivariantRoot}\left(h, 2\right))))))))\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/PeriodCountRootBlindPair.claim` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The claim universally quantifies g,h in this fixed DeckGroup. It assumes that every actual history in both systems has minimal period two, and asserts that equality of Nat.card(TwistedPeriod(loop(g),1,j)) and Nat.card(TwistedPeriod(loop(h),1,j)) for every positive natural j implies equivalence of HasEquivariantRoot(g,2) and HasEquivariantRoot(h,2). TwistedPeriod with twist 1 is exactly the actual fixed-history subtype for the jth iterate of shift.

**Theorem 1.5 (Equal periods and different actual square roots).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/PeriodCountRootBlindPair.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The proof supplies the two labels above and uses the complete actual atlas to prove that every history in each system has minimal period two. The existing twistedPeriod_card theorem counts actual histories, and the one-by-one matrix power has only single(g^j,1). Consequently both systems have eight fixed histories when j is even and zero when j is odd. The exact actual root criterion at d=1 gives a square root in the first system and excludes one in the second. The distinction concerns H-equivariant roots. It makes no claim that the second underlying ordinary permutation lacks a square root, and no claim about maps allowed to move between different base orbits.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Coding/PeriodCountRootBlindPair.DeckGroup`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PeriodCountRootBlindPair.HasEquivariantRoot`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PeriodCountRootBlindPair.claim`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PeriodCountRootBlindPair.loop`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PeriodCountRootBlindPair.result`
- Dependency: [D5/S3/ConceptDynamics/Coding/PrimitiveLiftRootCriterion](PrimitiveLiftRootCriterion.md)
