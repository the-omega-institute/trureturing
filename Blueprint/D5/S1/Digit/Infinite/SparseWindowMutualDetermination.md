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

**Theorem 1.5 (Distinct indexed cuts).**

Lean statement: `D5/S1/Digit/Infinite/SparseWindowMutualDetermination.cut_injective`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Infinite/SparseWindowMutualDetermination.cut_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The map E from natural cut indices to the circle is injective.

**Theorem 1.6 (Late visits to open sets).**

Lean statement: `D5/S1/Digit/Infinite/SparseWindowMutualDetermination.natural_phase_visit`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Infinite/SparseWindowMutualDetermination.natural_phase_visit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every nonempty open circle set U and natural bound B, some natural n greater than B has golden phase in U.

**Theorem 1.7 (Translation of natural phases).**

Lean statement: `D5/S1/Digit/Infinite/SparseWindowMutualDetermination.natural_phase_translate`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Infinite/SparseWindowMutualDetermination.natural_phase_translate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For all natural n and t, the phase of zRow(n+t) is the phase of zRow(n) plus t times the golden ratio modulo one.

**Theorem 1.8 (The phases of the two endpoint rows).**

Lean statement: `D5/S1/Digit/Infinite/SparseWindowMutualDetermination.endpoint_phase`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Infinite/SparseWindowMutualDetermination.endpoint_phase` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive cut index k, both endpoint rows eMinus(k) and ePlus(k) have phase E(k).

**Theorem 1.9 (Open arcs avoid their native cuts).**

Lean statement: `D5/S1/Digit/Infinite/SparseWindowMutualDetermination.window_arc_avoids_cut`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Infinite/SparseWindowMutualDetermination.window_arc_avoids_cut` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive width L, each open window arc avoids E(k) whenever 1 is at most k and k is at most G(L).

**Theorem 1.10 (Window arcs are open).**

Lean statement: `D5/S1/Digit/Infinite/SparseWindowMutualDetermination.window_arc_isOpen`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Infinite/SparseWindowMutualDetermination.window_arc_isOpen` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every width L and legal word p, its cylinder arc A(p) is open on the circle.

**Theorem 1.11 (The inverse golden ratio).**

Lean statement: `D5/S1/Digit/Infinite/SparseWindowMutualDetermination.golden_inverse_data`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Infinite/SparseWindowMutualDetermination.golden_inverse_data` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The inverse golden ratio alpha is strictly between zero and one and satisfies alpha squared plus alpha equals one.

**Theorem 1.12 (Length of the signed interval).**

Lean statement: `D5/S1/Digit/Infinite/SparseWindowMutualDetermination.signed_interval_length`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Infinite/SparseWindowMutualDetermination.signed_interval_length` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The right endpoint b of the signed series range is a+1, where a is its left endpoint.

**Theorem 1.13 (Open arcs cover every regular point).**

Lean statement: `D5/S1/Digit/Infinite/SparseWindowMutualDetermination.window_arc_cover`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Infinite/SparseWindowMutualDetermination.window_arc_cover` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each positive width L and circle point outside B(L), some legal L-word has an open cylinder arc containing that point.

**Theorem 1.14 (Labels on the two sides of a cut).**

Lean statement: `D5/S1/Digit/Infinite/SparseWindowMutualDetermination.window_cut_orientation`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Infinite/SparseWindowMutualDetermination.window_cut_orientation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive L and 1 at most k at most G(L), the upper endpoint of the eMinus(k) label and the lower endpoint of the ePlus(k) label both project to E(k).

**Theorem 1.15 (Integer differences of equal circle points).**

Lean statement: `D5/S1/Digit/Infinite/SparseWindowMutualDetermination.circle_integer_offset`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Infinite/SparseWindowMutualDetermination.circle_integer_offset` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If two real numbers have equal images modulo one, their difference is an integer.

**Theorem 1.16 (Integers have zero circle phase).**

Lean statement: `D5/S1/Digit/Infinite/SparseWindowMutualDetermination.circle_integer_zero`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Infinite/SparseWindowMutualDetermination.circle_integer_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every integer, regarded as a real number, projects to zero modulo one.

**Theorem 1.17 (Open collars at a window cut).**

Lean statement: `D5/S1/Digit/Infinite/SparseWindowMutualDetermination.window_cut_collar`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Infinite/SparseWindowMutualDetermination.window_cut_collar` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive L and 1 at most k at most G(L), there are a real lift c of E(k) and a radius delta strictly between zero and one half. The real interval (c-delta,c) projects into the eMinus(k) window arc, and (c,c+delta) projects into the ePlus(k) window arc.

**Theorem 1.18 (Late natural sources on both sides).**

Lean statement: `D5/S1/Digit/Infinite/SparseWindowMutualDetermination.natural_phase_visit_sides`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Infinite/SparseWindowMutualDetermination.natural_phase_visit_sides` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a real c, a radius strictly between zero and one half, an open circle neighborhood U of c, and any natural bound B, two natural sources greater than B have phases in U with real lifts in the respective open left and right intervals.

**Theorem 1.19 (Translation of cut indices).**

Lean statement: `D5/S1/Digit/Infinite/SparseWindowMutualDetermination.translated_cut`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Infinite/SparseWindowMutualDetermination.translated_cut` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For natural t and j, E(t+j) plus the golden phase of t equals E(j).

**Theorem 1.20 (Translated cuts and index intervals).**

Lean statement: `D5/S1/Digit/Infinite/SparseWindowMutualDetermination.translated_cut_mem`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Infinite/SparseWindowMutualDetermination.translated_cut_mem` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For natural L, t and k, E(k) plus the golden phase of t belongs to B(L) exactly when k is in the inclusive interval from t+1 to t+G(L).

**Theorem 1.21 (Missing target cuts).**

Lean statement: `D5/S1/Digit/Infinite/SparseWindowMutualDetermination.missing_cut_witness`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Infinite/SparseWindowMutualDetermination.missing_cut_witness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For 1 at most m at most M, a finite S, 1 at most k at most G(M) with k outside K(m,S), and every natural bound B, two sources greater than B have the same sparse tuple and different M-windows.

**Theorem 1.22 (Extra observation cuts).**

Lean statement: `D5/S1/Digit/Infinite/SparseWindowMutualDetermination.extra_cut_witness`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Infinite/SparseWindowMutualDetermination.extra_cut_witness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For 1 at most m at most M, a finite S, an index k in K(m,S) outside the target cut interval, and every natural bound B, two sources greater than B have the same M-window and different sparse tuples.

**Theorem 1.23 (Equal cut sets, equal natural fibres, and the canonical actual-image bijection).**

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

- Truth anchor: `D5/S1/Digit/Infinite/SparseWindowMutualDetermination.circle_integer_offset`
- Truth anchor: `D5/S1/Digit/Infinite/SparseWindowMutualDetermination.circle_integer_zero`
- Truth anchor: `D5/S1/Digit/Infinite/SparseWindowMutualDetermination.cut_injective`
- Truth anchor: `D5/S1/Digit/Infinite/SparseWindowMutualDetermination.endpoint_phase`
- Truth anchor: `D5/S1/Digit/Infinite/SparseWindowMutualDetermination.extra_cut_witness`
- Truth anchor: `D5/S1/Digit/Infinite/SparseWindowMutualDetermination.golden_inverse_data`
- Truth anchor: `D5/S1/Digit/Infinite/SparseWindowMutualDetermination.missing_cut_witness`
- Truth anchor: `D5/S1/Digit/Infinite/SparseWindowMutualDetermination.natural_phase_avoids_cut`
- Truth anchor: `D5/S1/Digit/Infinite/SparseWindowMutualDetermination.natural_phase_translate`
- Truth anchor: `D5/S1/Digit/Infinite/SparseWindowMutualDetermination.natural_phase_visit`
- Truth anchor: `D5/S1/Digit/Infinite/SparseWindowMutualDetermination.natural_phase_visit_sides`
- Truth anchor: `D5/S1/Digit/Infinite/SparseWindowMutualDetermination.natural_row_phase`
- Truth anchor: `D5/S1/Digit/Infinite/SparseWindowMutualDetermination.natural_row_raw_data`
- Truth anchor: `D5/S1/Digit/Infinite/SparseWindowMutualDetermination.natural_window_arc`
- Truth anchor: `D5/S1/Digit/Infinite/SparseWindowMutualDetermination.signed_interval_length`
- Truth anchor: `D5/S1/Digit/Infinite/SparseWindowMutualDetermination.sparse_window_mutual_determination`
- Truth anchor: `D5/S1/Digit/Infinite/SparseWindowMutualDetermination.translated_cut`
- Truth anchor: `D5/S1/Digit/Infinite/SparseWindowMutualDetermination.translated_cut_mem`
- Truth anchor: `D5/S1/Digit/Infinite/SparseWindowMutualDetermination.window_arc_avoids_cut`
- Truth anchor: `D5/S1/Digit/Infinite/SparseWindowMutualDetermination.window_arc_cover`
- Truth anchor: `D5/S1/Digit/Infinite/SparseWindowMutualDetermination.window_arc_isOpen`
- Truth anchor: `D5/S1/Digit/Infinite/SparseWindowMutualDetermination.window_cut_collar`
- Truth anchor: `D5/S1/Digit/Infinite/SparseWindowMutualDetermination.window_cut_orientation`
- Dependency: [D5/S1/Digit/Infinite/WindowCylinderPartition](WindowCylinderPartition.md)
- Dependency: [D5/S1/Phase/Basic](../../Phase/Basic.md)
