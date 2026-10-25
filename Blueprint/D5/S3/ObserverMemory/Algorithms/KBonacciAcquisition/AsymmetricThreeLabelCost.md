# Two queries separated by paid waiting

## Abstract

Asymmetric three-label phase sets have exact native paid cost.

**Theorem 1.1 (Exact cost for arbitrary asymmetric phase sets).**

$$(\forall (Y:\operatorname{Type}), ((\forall (g:\mathbb{N}), ((\forall (u:\mathbb{N}), ((\forall (p:\mathbb{N}), ((\forall (h:\mathbb{N}), ((\forall (r:\mathbb{N}), ((((2 \leq g \land (3 \leq u \land (u < p \land (\operatorname{Coprime}\left(u, p\right) \land (p = h \cdot u + r \land (1 \leq r \land r < u))))))) \implies ((\forall (HB:\operatorname{Finset}\left(\mathbb{N}\right)), ((\forall (HC:\operatorname{Finset}\left(\mathbb{N}\right)), ((((\operatorname{Nonempty}\left(HB\right) \land (\operatorname{Nonempty}\left(HC\right) \land (\operatorname{Disjoint}\left(HB, HC\right) \land (HB \subseteq \operatorname{Icc}\left(1, \operatorname{natSub}\left(u, r\right)\right) \land HC \subseteq \operatorname{Icc}\left(1, \operatorname{natSub}\left(u, 1\right)\right)))))) \implies ((\forall (A:Y), ((\forall (B:Y), ((\forall (C:Y), ((((A \neq B \land (A \neq C \land B \neq C))) \implies (\operatorname{let} k=\operatorname{natSub}\left(g \cdot p, 1\right) \operatorname{in} (\operatorname{let} m=g \cdot u \operatorname{in} ((\forall (f:\operatorname{Option}\left(\operatorname{LiveRecord}\left(k\right)\right) \to Y), ((\forall (v:\operatorname{ZMod}\left(2\right)), ((\forall (a:\operatorname{Bool}), ((((\forall (j:\operatorname{Fin}\left(p\right)), ((\forall (s:\mathbb{N}), (((s < k) \implies (f\left(\operatorname{some}\left((v,-\operatorname{cast}\left(\operatorname{val}\left(j\right) \cdot g, \operatorname{ZMod}\left(k + 1\right)\right),s)\right)\right) = \operatorname{if}\left(\operatorname{val}\left(j\right) \in HB, B, \operatorname{if}\left(\operatorname{val}\left(j\right) \in HC, C, A\right)\right)))))))) \implies ((\operatorname{OriginalFiberCost}\left(k, m, \operatorname{positivek}, a, f, v\right) = \operatorname{cast}\left(h + 1, \operatorname{ENat}\right) \land h + 1 = \operatorname{natDiv}\left(\operatorname{natSub}\left(p + u, 1\right), u\right))))))))))))))))))))))))))))))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/AsymmetricThreeLabelCost.original_asymmetric_three_label_cost` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let g be at least two, let 3 <= u < p with u and p coprime, and write p=hu+r with 1 <= r < u. Put T=gp, k=T-1 and m=gu. The nonempty disjoint finite sets HB and HC satisfy HB contained in [1,u-r] and HC contained in [1,u-1]. The labels A, B and C are pairwise distinct elements of an arbitrary type Y.

In the free initial value fiber v, every legal initial tail s<k at phase -jg modulo T has label B when j belongs to HB, label C when j belongs to HC, and A otherwise. The target f is unrestricted on the other value fiber and at rejection. The parameter a selects either all Boolean complete blocks or only internally admissible complete blocks. OriginalFiberCost ranges over every actual finite joint history in that alphabet, including the empty history. An initially rejected source returns f(none) for free.

The reader uses the original low-first kbonacci weights and their fixed mod-two output. Its archive contains only the free initial output, issued complete blocks and their own endpoint readings. The selector issues a fixed script and decodes only after its last endpoint. It has no reset, copy, intermediate observation or access to an unexecuted branch. Every issued complete block costs one.

For a set H, the pulse word has a one exactly at local positions jg-1 for j in H and zeros elsewhere. First issue the pulse word for HC, then exactly h-1 zero words, then the pulse word for r+HB. The first word starts and ends in zero. The final word starts in zero, and its pulse for j in HB has absolute position hm+(r+j)g-1=T+jg-1. Hence the first endpoint difference is the indicator of HC, and the last difference is the indicator of HB. The decoder returns C if the first difference is one, B if only the last difference is one, and A otherwise. The phase sets are disjoint, so this recovers the INITIAL label.

Every word has length m<k. The first zero clears any inherited legal tail, and each following word starts in zero, so the complete same-history execution is safe across every seam. The final pulse may occupy the last bit; the script stops there without a clearing fee. The uniform fee is h+1, including all waiting words. When h=1 there are no waiting words. The bounds also allow r=u-1 and all endpoints of both supports.

At tail zero the first window contains a source of each label: phase index zero gives A, any member of HB gives B, and any member of HC gives C. Its label image therefore has cardinality three. The original first-window waiting lower bound gives h+clog(2,3)-1=h+1 for either alphabet. Together with the literal script this proves the exact native cost. Since p=hu+r with 0<r<u, the natural quotient (p+u-1)/u equals h+1 and is the ceiling of p/u. The symbol positivek denotes the positivity proof supplied by the parameter inequalities.

## References

- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/AsymmetricThreeLabelCost.original_asymmetric_three_label_cost`
- Dependency: [D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/FiveLabelSeamCost](FiveLabelSeamCost.md)
