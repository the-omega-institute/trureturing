# Actual Complete Cycles

## Abstract

Actual least-cut cycles have exact finite-tuple probabilities and lose no mass under finite exhaustion.

U(n) is the finite set of literal permutations of Fin(n) avoiding 2413 and 3142. At a least direct or skew cut, a small left indecomposable factor is emitted; a small right factor is removed and the forced cut sign alternates. A complete cycle ends at the first left emission. It leaves an actual unrestricted separable permutation, on which the next cycle is parsed.

For natural K and H, Cycle(K,sign,H) contains right removals followed by one left emission, with at most H steps and each removed or emitted shape of length between 1 and K. The terminal shape has no proper cut of its sign. Family(K,H) also records the initial sign. Tuple(K,H,k) records k complete cycles, including the unique empty tuple for k=0. Its size is the sum of all removed and emitted lengths. Every fixed finite sequence of these nonempty shapes is represented once the two bounds are large enough.

Write T(K,H,k)=k*H*K+max(2*K,1). For n>T, Event(tuple,n) is the actual EndpointHistory.EventFor fiber, recursively restricted by the tuple event on the true remaining permutation. Success is the union of these finite tuple events. Failed is its literal complement for n>T and is the whole source for n<=T. The probability functions are the real masses under the uniform distribution on U(n), extended by zero below the threshold. No unsuccessful restricted leaf is assigned the mass of its full leaf.

In the statement, C=Tuple(K,H,k), T=T(K,H,k), s(c)=size(c), A(c,n) is the actual tuple event, and p(c,n) is its zero-extended probability. P(K,H,k,n) is the zero-extended success probability and F(K,H,k,n) is the actual failed event. An n>T quantifier includes its threshold guard. Size, bound and cycle-count variables range over natural numbers, epsilon ranges over the reals, and limits use the full sequence of natural n. The function event(c,n) in the last clause is the original history event for c in Family(K,H); FirstSuccess is the original classifier success kind.

**Theorem 1.1 (Exact finite tuples and finite-complement exhaustion).**

$$(\forall K,H,k, (\forall n>T, (\forall c,d\in C, (\forall x\in \operatorname{U}\left(n\right), (x\in \operatorname{A}\left(c, n\right) \land x\in \operatorname{A}\left(d, n\right)) \implies c=d)))) \land (\forall K,H,k, (\forall n>T, (\forall c\in C, 0<n-\operatorname{s}\left(c\right) \land \operatorname{card}\left(\operatorname{A}\left(c, n\right)\right)=\operatorname{card}\left(\operatorname{U}\left(n-\operatorname{s}\left(c\right)\right)\right) \land \operatorname{Pr}\left(\operatorname{A}\left(c, n\right)\right)=\frac{\operatorname{card}\left(\operatorname{U}\left(n-\operatorname{s}\left(c\right)\right)\right)}{\operatorname{card}\left(\operatorname{U}\left(n\right)\right)}))) \land (\forall K,H,k, (\forall c\in C, \lim_{n\to\infty}\operatorname{p}\left(c, n\right)=rho^{\operatorname{s}\left(c\right)})) \land (\forall K,H,k, (\forall n>T, \operatorname{card}\left(\operatorname{Success}\left(K, H, k, n\right)\right)=\sum_{c\in C}\operatorname{card}\left(\operatorname{U}\left(n-\operatorname{s}\left(c\right)\right)\right))) \land (\forall K,H,k, (\forall n, \operatorname{Pr}\left(\operatorname{F}\left(K, H, k, n\right)\right)=1-\operatorname{P}\left(K, H, k, n\right))) \land (\forall K,H,k, \lim_{n\to\infty}\operatorname{P}\left(K, H, k, n\right)=\sum_{c\in C}rho^{\operatorname{s}\left(c\right)}) \land (\forall k, (\forall epsilon>0, \exists K,H,N, (\forall n\geq N, \operatorname{Pr}\left(\operatorname{F}\left(K, H, k, n\right)\right)<epsilon))) \land (\forall k, (\forall c\in \operatorname{UnboundedTuple}\left(k\right), \exists K,H, (\exists d\in \operatorname{Tuple}\left(K, H, k\right), \operatorname{erase}\left(d\right)=c \land \lim_{n\to\infty}\operatorname{p}\left(d, n\right)=rho^{\operatorname{s}\left(c\right)}))) \land (\forall K,H, (\forall n>H\cdot K+\operatorname{max}\left(2\cdot K, 1\right), (\forall x\in \operatorname{U}\left(n\right), (\exists c\in \operatorname{Family}\left(K, H\right), x\in \operatorname{event}\left(c, n\right)) \iff \operatorname{FirstSuccess}\left(K, H, n, x\right))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Patterns/Separable/ActualCycles.actual_complete_cycles` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every K,H,k,n with n>T(K,H,k), two tuple events containing the same actual permutation have equal tuples. The remaining size n-size(tuple) is positive. Each event has exactly card(U(n-size(tuple))) members and the displayed exact probability. For every fixed tuple its extended probability converges, along all natural n, to rho^size(tuple), where rho=(sqrt(2)-1)^2.

The success event has cardinality equal to the sum, over all tuples, of card(U(n-size(tuple))). At every n the actual failed mass is 1 minus the extended success probability. For fixed K,H,k, the success probability converges to the finite sum of rho^size(tuple). For every fixed k and every real epsilon>0 there are K,H,N such that, for every n>=N, the actual failed mass is less than epsilon. An unbounded cycle type records arbitrary finite shapes before any cap is chosen. Every fixed tuple in that type has a finite bounded representation with the same shapes and a full-sequence probability limit rho raised to its total length. This includes k=0 and all empty finite families; all actual singleton conventions are retained.

A first-cycle event exists exactly when the original actual minimum-cut classifier, with target 1 and label threshold 0, returns its good success kind. All other classifier kinds retain their original restricted actual fibers. Unique parsing follows from the existing stable least-cut fibers. The history reconstruction bijection identifies each tuple fiber with its true remaining U(n-size(tuple)). The actual fixed-shift count ratio gives its full-sequence limit. If u(K) is the partial critical mass of nonempty U-shapes and j(K) that of the signed indecomposable shapes, the limiting tuple mass is (2*j(K)*sum(r<H,u(K)^r))^k. The shared actual-shape theorem gives u(K)->b and j(K)->(1-b)/2, with 0<b=sqrt(2)-1<1. First taking K large for fixed H, then H large, gives total mass one and hence the stated actual finite-complement bound.

This theorem concerns finite actual permutation experiments. It does not construct a common infinite execution, identify all position or label observations, prove conditional endpoint marks or a predictable hazard, or supply discrepancy and occupation estimates for the absolute-discrepancy application.

## References

- Truth anchor: `D5/S1/Words/Patterns/Separable/ActualCycles.actual_complete_cycles`
- Dependency: [D5/S1/Words/Patterns/Separable/ActualCountRatios](ActualCountRatios.md)
- Dependency: [D5/S1/Words/Patterns/Separable/StableEndpointCodes](StableEndpointCodes.md)
