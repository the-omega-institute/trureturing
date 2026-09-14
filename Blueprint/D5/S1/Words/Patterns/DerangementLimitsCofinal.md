# No Largest Derangement Limit Below One

## Abstract

Bounded decreasing tails yield derangement limits cofinal below one.

The paragraph following Question 4.3 in Section 4 of `D5/L/Words/vatter2026assortment` asks: Is there a largest possible limit strictly less than 1? The question concerns arbitrary permutation classes, with no growth restriction. The construction below answers this question negatively. It gives limits arbitrarily close to one from below, without classifying all possible limits.

Perm(n) denotes Equiv.Perm(Fin(n)). Positions and values are numbered from zero; val is the underlying natural number of a Fin element or the underlying permutation of a subtype element, as appropriate. P(n,a) denotes tailPerm with the displayed assumption a<=n. C(k) denotes boundedTailClass(k). The containment relation Contains, the hereditary-class structure PermClass, the fixed-point-free predicate IsDerangement, and the real-valued ratio are those of `D5/S1/Words/Patterns/DerangementRatioNonconvergence`. Nonempty(S) means that the set S contains a permutation. Every cardinality is Fintype.card; all quotients of cardinalities or natural parameters in a real formula use their real casts.

**Definition 1.1 (The two-block permutation).**

$$\forall n: \mathbb{N}, \forall a: \mathbb{N}, a \le n \implies \operatorname{P}\left(n, a\right): \operatorname{Perm}\left(n\right) \land (\forall i: \operatorname{Fin}\left(n\right), \operatorname{val}\left(\operatorname{P}\left(n, a\right)\left(i\right)\right) = \operatorname{if} \operatorname{val}\left(i\right) < n - a \operatorname{then} a + \operatorname{val}\left(i\right) \operatorname{else} n - 1 - \operatorname{val}\left(i\right))$$

*Formalization.* `D5/S1/Words/Patterns/DerangementLimitsCofinal.tailPerm` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

In one-based notation this is (a+1,...,n,a,...,1). The head increases through the high values and the tail decreases through the low values. The inverse sends a value j to j-a when a<=j and to n-1-j otherwise. The two branches are inverse bijections on the corresponding disjoint intervals. Either block can be empty, and length zero is included.

**Theorem 1.2 (Patterns retain a bounded tail).**

$$\forall m: \mathbb{N}, \forall n: \mathbb{N}, \forall a: \mathbb{N}, a \le n \implies \forall \sigma: \operatorname{Perm}\left(m\right), \operatorname{Contains}\left(\sigma, \operatorname{P}\left(n, a\right)\right) \implies \exists t: \mathbb{N}, t \le m \land t \le a \land \sigma = \operatorname{P}\left(m, t\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Patterns/DerangementLimitsCofinal.pattern_tailPerm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let f be the order embedding selecting the pattern. There is a cut b such that f(i) is in the original head exactly when i<b. To obtain it, take the least b after which every selected position is in the tail; monotonicity of f makes every earlier selected position a head position. The m-b selected tail positions inject into the original a tail positions. For i<j, the selected values increase exactly when j<b. The permutation P(m,m-b) has precisely the same comparisons. Composing one permutation with the inverse of the other gives a strictly increasing self-map of a finite chain, which is the identity. Hence the pattern equals P(m,m-b).

**Definition 1.3 (The hereditary class).**

$$\begin{aligned}\forall k: \mathbb{N}, \operatorname{C}\left(k\right): \operatorname{PermClass}\\\forall k: \mathbb{N}, \forall n: \mathbb{N}, \operatorname{mem}\left(\operatorname{C}\left(k\right), n\right) = \{\pi: \operatorname{Perm}\left(n\right) \mid \exists a: \mathbb{N}, a \le n \land a \le k \land \pi = \operatorname{P}\left(n, a\right)\}\\\forall k: \mathbb{N}, \operatorname{downset}\left(\operatorname{C}\left(k\right)\right): \forall m: \mathbb{N}, \forall n: \mathbb{N}, \forall \sigma: \operatorname{Perm}\left(m\right), \forall \pi: \operatorname{Perm}\left(n\right), \pi \in \operatorname{mem}\left(\operatorname{C}\left(k\right), n\right) \implies \operatorname{Contains}\left(\sigma, \pi\right) \implies \sigma \in \operatorname{mem}\left(\operatorname{C}\left(k\right), m\right)\end{aligned}$$

*Formalization.* `D5/S1/Words/Patterns/DerangementLimitsCofinal.boundedTailClass` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Membership means being one of the permutations with tail length at most k. The preceding theorem supplies arbitrary-pattern closure: a contained pattern has tail length at most that of the containing permutation, and therefore still at most k. Membership concerns permutations themselves; different witnesses for a do not create distinct members.

**Theorem 1.4 (Exact eventual counts).**

$$\forall k: \mathbb{N}, \forall n: \mathbb{N}, 2 \times k + 2 < n \implies \operatorname{card}\left(\operatorname{mem}\left(\operatorname{C}\left(k\right), n\right)\right) = k + 1 \land \operatorname{card}\left(\{\pi: \operatorname{mem}\left(\operatorname{C}\left(k\right), n\right) \mid \operatorname{IsDerangement}\left(\operatorname{val}\left(\pi\right)\right)\}\right) = k$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Patterns/DerangementLimitsCofinal.boundedTailClass_counts` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

When n>2*k+2, every a from 0 through k has a nonempty head. Its first value is a, so these k+1 permutations are distinct and exhaust the slice. The parameter a=0 gives the identity, which has a fixed point because n>0. For a>0 a head position shifts upward by a. A tail position is at least n-a, whereas its value is less than a; the threshold separates these intervals. Thus precisely the k positive parameters give derangements. Bijections from Fin(k+1) and Fin(k) give the two displayed subtype counts. No distinctness claim is made at smaller lengths: P(n,n) and P(n,n-1) coincide when n>0.

**Theorem 1.5 (Attained limits are cofinal below one).**

$$\forall q: \mathbb{R}, q < 1 \implies \exists C: \operatorname{PermClass}, \exists l: \mathbb{R}, q < l \land l < 1 \land (\forall n: \mathbb{N}, \operatorname{Nonempty}\left(\operatorname{mem}\left(C, n\right)\right)) \land \operatorname{Tendsto}\left(\operatorname{ratio}\left(C\right), \operatorname{atTop}, \operatorname{nhds}\left(l\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Patterns/DerangementLimitsCofinal.exists_derangement_limit_between` (`✓ std3`). ∎

*Resolves.* `Problems/vatter-largest-derangement-limit-below-one` (refuted) by `D5/S1/Words/Patterns/DerangementLimitsCofinal.exists_derangement_limit_between`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"vatter-largest-derangement-limit-below-one","declaration_gid":"D5/S1/Words/Patterns/DerangementLimitsCofinal.exists_derangement_limit_between","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Vincent Vatter (2026). *An Assortment of Problems in Permutation Patterns: Unimodality, Equivalence, Derangements, and Sorting*. URL: <https://arxiv.org/abs/2602.16355>.

*Commentary.*

For a real q<1 choose a natural k greater than q/(1-q). Positive-denominator arithmetic gives q<k/(k+1)<1. Choose C(k) and this real limit. At every length P(n,0) is a member, so all slices are nonempty. The two exact counts make the ratio identically k/(k+1) for n>2*k+2, and eventual constancy gives convergence. Applying the theorem to any attained limit below one produces a larger attained limit still below one. These classes have eventually constant slice cardinality; the assertion is the arbitrary-class question. The cited source supplies the question; the construction and proof are derived here.

## References

- Truth anchor: `D5/S1/Words/Patterns/DerangementLimitsCofinal.boundedTailClass`
- Truth anchor: `D5/S1/Words/Patterns/DerangementLimitsCofinal.boundedTailClass_counts`
- Truth anchor: `D5/S1/Words/Patterns/DerangementLimitsCofinal.exists_derangement_limit_between`
- Truth anchor: `D5/S1/Words/Patterns/DerangementLimitsCofinal.pattern_tailPerm`
- Truth anchor: `D5/S1/Words/Patterns/DerangementLimitsCofinal.tailPerm`
- Dependency: [D5/S1/Words/Patterns/DerangementRatioNonconvergence](DerangementRatioNonconvergence.md)
- Narrative reference: [D5/S1/Words/Patterns/DerangementRatioNonconvergence](DerangementRatioNonconvergence.md)
