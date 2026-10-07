# Uniform Support Signal on Legal Positive-End Words

## Abstract

Conditional resampling on the complete positive-End legal source detects every effective support coordinate.

Input(n) is Fin(n) to the existing five-window alphabet 000,100,010,101,001, with bits written from low to high and positions starting at zero. Positive(x) requires flattened-bit legality with initial bit false and a nonzero last window. Every null window retains its position. The source is the finite set of these actual words.

The existing Roles(n) has p<q<r. The priority teacher returns 1 when high(x(p)) and low(x(q)) hold, otherwise 2 when high(x(q)) and low(x(r)) hold, and otherwise 0. Its support is the union of {p,q} when p+1<q and {q,r} when q+1<r. This gives the four empty, first-edge, second-edge, and two-edge cases.

The completion fiber at I and x consists of positive legal words that agree with x at each position outside I. It contains x whenever x belongs to the source. signal(t,I) averages the indicator that the two teacher responses differ: first uniformly over this nonempty completion fiber, then uniformly over the complete source. Both averages are finite rational sums; coordinates within a word need not be independent.

**Theorem 1.1 (Disjoint support and a uniform lower bound).**

$$\forall \left(n: \mathbb{N}\right), \forall \left(t: \operatorname{Roles}\left(n\right)\right), \forall \left(I: \operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right)\right), 4 \leq n \implies \left(\left(\left(\operatorname{inter}\left(I, \operatorname{support}\left(t\right)\right)\right) = \emptyset \implies \operatorname{signal}\left(t, I\right) = 0\right) \land \left(\operatorname{Nonempty}\left(\operatorname{inter}\left(I, \operatorname{support}\left(t\right)\right)\right) \implies \frac{2}{3125} \leq \operatorname{signal}\left(t, I\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/LegalResamplingSupportSignal.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The bounds hold for every n at least four, every strict role triple and every set I of positions. Disjointness gives exact response equality. For a support position, neutral guards and the opposite endpoint can be fixed while retaining its original letter. Three original letters recover the preimage of this repair. Two available replacement letters give different responses in the same legal fiber. The squared-error decomposition of finite averages then transfers the singleton lower bound to any containing set.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/LegalResamplingSupportSignal.result`
- Dependency: [D5/S3/Arith/FibonacciAtomic/LegalPriorityTeacher](LegalPriorityTeacher.md)
