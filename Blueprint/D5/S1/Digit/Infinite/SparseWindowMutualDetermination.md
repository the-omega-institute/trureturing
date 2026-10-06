# Sparse Fibonacci Window Mutual Determination

## Abstract

Sparse natural Fibonacci windows have the same fibres precisely when their translated cuts agree.

Let X(L) be the binary words of length L with no adjacent ones. The Fibonacci numbers start with F(0)=0 and F(1)=1, and G(L)=F(L+2). The canonical value V(p) is the sum of the Fibonacci weights F(j+2) at the occupied positions j of p. The row zRow(n) is the canonical finite Fibonacci expansion of n, continued by zeros. P(L) takes its first L digits. All natural numbers here include zero.

For a finite set S of retained natural times, observations use ordinary addition on a single source. The tuple is a function on the subtype of times belonging to S, including the empty function when S is empty. Icc denotes an inclusive interval of natural indices.

$$
q_{L}(n) = \operatorname{P}\left(L, \operatorname{zRow}\left(n\right)\right), \sigma_{m,S}(n)(t) = q_{m}(n+t) (t \in S), \operatorname{K}\left(m, S\right) = \cup_{t \in S} \operatorname{Icc}\left(t+1, t+\operatorname{G}\left(m\right)\right)
$$

The range of an observation consists of its actual natural values. Write actual(n) for sigma(m,S,n), regarded as an element of that range with witness n, and val for the underlying value of a range element. Equiv denotes a bijection with a specified inverse.

**Theorem 1.1 (Canonical natural digits).**

Lean statement: `D5/S1/Digit/Infinite/SparseWindowMutualDetermination.natural_row_raw_data`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Infinite/SparseWindowMutualDetermination.natural_row_raw_data` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural n, the raw digits of its Zeckendorf expansion have value n. At every position their real coefficient equals the Boolean digit of zRow(n).

**Theorem 1.2 (Natural row phase).**

Lean statement: `D5/S1/Digit/Infinite/SparseWindowMutualDetermination.natural_row_phase`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Infinite/SparseWindowMutualDetermination.natural_row_phase` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural n, the phase of zRow(n) is n times the golden ratio modulo one. The equality identifies natural digit observations with circle rotation.

**Theorem 1.3 (Natural phases avoid positive cuts).**

Lean statement: `D5/S1/Digit/Infinite/SparseWindowMutualDetermination.natural_phase_avoids_cut`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Infinite/SparseWindowMutualDetermination.natural_phase_avoids_cut` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural n and every positive cut index k, the phase n times the golden ratio modulo one differs from E(k). Irrationality excludes equality.

**Theorem 1.4 (Natural labels and cylinder arcs).**

Lean statement: `D5/S1/Digit/Infinite/SparseWindowMutualDetermination.natural_window_arc`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Infinite/SparseWindowMutualDetermination.natural_window_arc` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive width L, natural n, and legal word p of width L, q(L,n)=p if and only if the phase of zRow(n) belongs to the open cylinder arc A(p). Natural rows avoid the endpoint alternatives of the closed cylinder.

**Theorem 1.5 (Equal cut sets, equal natural fibres, and the canonical actual-image bijection).**

$$\forall m,M \in \mathbb{N}, \forall S \in \operatorname{Finset}\left(\mathbb{N}\right), (1 \le m \land m \le M) \Rightarrow (((\forall a,b \in \mathbb{N}, (q_{M}(a) = q_{M}(b) \iff \sigma_{m,S}(a) = \sigma_{m,S}(b))) \iff \operatorname{K}\left(m, S\right) = \operatorname{Icc}\left(1, \operatorname{G}\left(M\right)\right)) \land (\operatorname{K}\left(m, S\right) = \operatorname{Icc}\left(1, \operatorname{G}\left(M\right)\right) \Rightarrow (\operatorname{card}\left(\operatorname{range}\left(q_{M}\right)\right) = \operatorname{G}\left(M\right) \land \operatorname{card}\left(\operatorname{range}\left(\sigma_{m,S}\right)\right) = \operatorname{G}\left(M\right) \land (\exists e \in \operatorname{Equiv}\left(\operatorname{X}\left(M\right), \operatorname{range}\left(\sigma_{m,S}\right)\right), (\forall p \in \operatorname{X}\left(M\right), \operatorname{val}\left(e\left(p\right)\right) = \sigma_{m,S}(\operatorname{V}\left(p\right))) \land (\forall n \in \mathbb{N}, \operatorname{val}\left(e\left(q_{M}(n)\right)\right) = \sigma_{m,S}(n)) \land (\forall n \in \mathbb{N}, e^{-1}(\operatorname{actual}\left(n\right)) = q_{M}(n)))))).$$

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Infinite/SparseWindowMutualDetermination.sparse_window_mutual_determination` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive pair of widths m at most M and every finite S, equality of the translated query-cut indices with the target-cut indices is equivalent to equality of the two natural fibre relations. Under this cut equality both actual ranges have G(M) elements. The displayed bijection sends p to sigma(m,S,V(p)); its inverse on an actual observation returns the target window of that same source.

The phase of the canonical row n is n times the golden ratio modulo one. Translation by t is therefore addition of t times that ratio on the circle. Positive cut indices are distinct, and every natural row avoids them. The natural rotation visits every nonempty open arc above every natural bound. A chart centered at a chosen cut has its seam half a turn away. Small open collars on its two sides have different native window labels, including at the exterior seam. A missing target cut yields two arbitrarily late natural sources with equal query tuples and different targets. An extra query cut yields equal targets and different query tuples.

Cut coverage forces time zero to be observed. For m at least two, this coordinate provides a common real interval of length at most alpha squared, where alpha is the reciprocal golden ratio. Its length plus that of any query arc is at most alpha squared plus alpha, which equals one. Two points in the common interval with the same query label consequently use the same integer lift of that query arc. A target boundary between the points would then be a query cut inside its own open query arc, a contradiction.

For m=1 and M at least two, coverage additionally forces time one or time two to be observed. A one at either of the paired times gives a short anchor, and the common-lift argument allows length sum equal to one. If both paired bits are zero, the signed value lies in (alpha squared minus alpha cubed, alpha squared) for times {0,1}, and in (-alpha cubed, alpha squared minus alpha cubed) for times {0,2}. These are short anchors as well. For m=M=1 the observed time-zero coordinate already gives the target. No assertion that arbitrary binary tuples have connected fibres is used; the all-zero fibre for times {0,4} can be disconnected.

Each target label occupies one connected open real interval. When the query cuts are target cuts, no translated query cut lies inside that interval. The disjoint open query-label sets then force each coordinate to remain constant throughout it, giving prediction. Canonical re-encoding gives q(L,V(p))=p, and the Zeckendorf sum bound gives V(p)<G(L). Together with V(q(L,n))=n for n<G(L), these identities identify X(L) with Fin(G(L)). Fibre equality factors the target through the actual sparse observation, while prediction identifies its image with the displayed V representatives. This establishes both cardinalities and the forward and inverse identities.

## References

- Truth anchor: `D5/S1/Digit/Infinite/SparseWindowMutualDetermination.natural_phase_avoids_cut`
- Truth anchor: `D5/S1/Digit/Infinite/SparseWindowMutualDetermination.natural_row_phase`
- Truth anchor: `D5/S1/Digit/Infinite/SparseWindowMutualDetermination.natural_row_raw_data`
- Truth anchor: `D5/S1/Digit/Infinite/SparseWindowMutualDetermination.natural_window_arc`
- Truth anchor: `D5/S1/Digit/Infinite/SparseWindowMutualDetermination.sparse_window_mutual_determination`
- Dependency: [D5/S1/Digit/Infinite/WindowCylinderPartition](WindowCylinderPartition.md)
