# Every finite F3-space with a prescribed opposite hole

## Abstract

Every finite F3-space with a prescribed opposite hole

**Theorem 1.1 (Every finite F3-space with a prescribed opposite hole).**

$$\forall (V:\operatorname{Type}),[\operatorname{AddCommGroup}(V)][\operatorname{Module}(\operatorname{ZMod}(3),V)][\operatorname{Finite}(V)]2\le \operatorname{finrank}(\operatorname{ZMod}(3),V)\Rightarrow \forall (x:V),x\neq 0\Rightarrow \operatorname{let} M=3^{\operatorname{finrank}(\operatorname{ZMod}(3),V)}-3;\exists (w:\mathbb{N}\to V),\operatorname{Injective}((i:\operatorname{Fin}(M)\mapsto \operatorname{w}(i)))\land \operatorname{range}((i:\operatorname{Fin}(M)\mapsto \operatorname{w}(i)))=\{y:V|y\neq 0\land y\neq x\land y\neq -x\}\land \operatorname{Injective}((k:\operatorname{Fin}(M)\mapsto \sum_{i<k}\operatorname{w}(i)))\land \sum_{i<M}\operatorname{w}(i)=0\land \forall (a:\mathbb{N}),\forall (b:\mathbb{N}),(a<b\land b\le M\land (a\neq 0\lor b\neq M))\Rightarrow \sum_{a\le i<b}\operatorname{w}(i)\neq 0$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Sequenceability/CharacteristicThreeOpposite.exists_opposite_ordering` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite vector space V over ZMod 3 of dimension at least two and every nonzero x in V, put M=3^finrank(V)-3. There is a natural-indexed word whose first M terms enumerate V minus {0,x,-x} exactly once. The first M coefficient-one prefixes, numbered 0 through M-1, are pairwise distinct; the full M-term prefix equals zero. Every proper nonempty interval [a,b) with 0<=a<b<=M and (a,b)!=(0,M) has nonzero sum. The only exempt interval is the whole word. Take r=finrank(V)-1 and the actual field K=GaloisField 3 r. Its cardinality is 3^r and its F3-dimension is r. Equal finite dimension gives an equivalence from K times F3 to V. The image of (0,1) is nonzero. The isomorphism between its one-dimensional span and the span of x extends to an automorphism of V, so composing gives an F3-linear equivalence sending (0,1) exactly to x. Its underlying additive equivalence transports the field ordering. Finally 3*(3^r-1)=3^finrank(V)-3. This includes dimension two with r=1 through the same proof, with no exceptional assumption.

## References

- Truth anchor: `D5/S1/Words/Sequenceability/CharacteristicThreeOpposite.exists_opposite_ordering`
- Dependency: [D5/S1/Words/Sequenceability/CharacteristicThreeOrdering](CharacteristicThreeOrdering.md)
