# Cylinder packing and short-return width

## Abstract

Signed cylinder packing and width bounds for short returns in paired components.

The return graph may be any finite quiver. The width theorem uses the signed golden-base cylinders with the fixed contraction and guard endpoints of the original digit system.

**Lemma 1.1 (Phase divisibility bounds the synchronization length).**

$$\forall a \in \mathbb{N},\; \forall b \in \mathbb{N},\; \forall n \in \mathbb{N},\; \forall p \in \mathbb{N},\; \left(0 < p \land \left(p \mid a \land \left(p \mid b \land \left(a \le n \land b \le 2 \cdot n - 1\right)\right)\right)\right) \Rightarrow lcm\left(a, b\right) \le p \cdot \lfloor\frac{n}{p}\rfloor \cdot \lfloor\frac{2 \cdot n - 1}{p}\rfloor$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/ReturnWords/ShortReturnWidthTransport.synchronized_length_le_phase_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Writing a=p alpha and b=p gamma gives lcm(a,b)=p lcm(alpha,gamma). The quotient bounds and the Mathlib product bound give the estimate. Zero lengths are allowed. This arithmetic helper is used by short_return_width_lower_bound.

**Lemma 1.2 (The contraction ratio decreases with the positive scale).**

$$\forall g \in \mathbb{R},\; \forall L \in \mathbb{N},\; \forall M \in \mathbb{N},\; \left(0 < g \land \left(g < 1 \land \left(0 < L \land L \le M\right)\right)\right) \Rightarrow \frac{g^{M}}{1 - g^{M}} \le \frac{g^{L}}{1 - g^{L}}$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/ReturnWords/ShortReturnWidthTransport.contraction_ratio_antitone` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Power order and positive-denominator fraction comparison give this helper. Equality of scales is included. It is used by short_return_width_lower_bound.

**Lemma 1.3 (Arithmetic transport of a supplied packing inequality).**

$$\forall a \in \mathbb{N},\; \forall b \in \mathbb{N},\; \forall n \in \mathbb{N},\; \forall p \in \mathbb{N},\; \forall g \in \mathbb{R},\; \forall d \in \mathbb{R},\; \forall w \in \mathbb{R},\; \left(0 < g \land \left(g < 1 \land \left(0 \le d \land \left(\left(0 < p \land \left(p \mid a \land \left(p \mid b \land \left(a \le n \land b \le 2 \cdot n - 1\right)\right)\right)\right) \land \left(0 < a \land \left(0 < b \land g^{lcm\left(a, b\right)} \cdot d \le \left(1 - g^{lcm\left(a, b\right)}\right) \cdot w\right)\right)\right)\right)\right)\right) \Rightarrow \frac{g^{p \cdot \lfloor\frac{n}{p}\rfloor \cdot \lfloor\frac{2 \cdot n - 1}{p}\rfloor}}{1 - g^{p \cdot \lfloor\frac{n}{p}\rfloor \cdot \lfloor\frac{2 \cdot n - 1}{p}\rfloor}} \cdot d \le w$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/ReturnWords/ShortReturnWidthTransport.short_return_width_lower_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This arithmetic helper assumes packing at the actual LCM, divides by its positive denominator, and applies the LCM and ratio helpers. The width theorem uses the packing of the synchronized returns on the original component.

**Theorem 1.4 (A shortest return and a failing simple-path test).**

Lean statement: `D5/S1/Words/ReturnWords/ShortReturnWidthTransport.exists_bounded_detecting_returns`

*Proof.* Machine-checked in Lean as `D5/S1/Words/ReturnWords/ShortReturnWidthTransport.exists_bounded_detecting_returns` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In any incoherent finite cyclic strongly connected component with n vertices, fix a base vertex. There is a shortest positive return of length at most n. Choose simple paths to and from each vertex with length less than n, using empty paths at the base. A positive test return of length at most 2n−1 has a different label word after synchronization with the shortest return.

A test joins the two paths at a vertex or inserts one actual directed edge between them. If every nonempty test agreed with the shortest return, the least period of its repeated word would divide the lengths of those test returns. The vertex and edge tests then give a phase and determine the label on each edge, implying coherence.

**Theorem 1.5 (Width at every basepoint of an incoherent cyclic component).**

Lean statement: `D5/S1/Words/ReturnWords/ShortReturnWidthTransport.width_at_incoherent_basepoint`

*Proof.* Machine-checked in Lean as `D5/S1/Words/ReturnWords/ShortReturnWidthTransport.width_at_incoherent_basepoint` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix a vertex of a finite cyclic strongly connected component that is incoherent for a single-symbol edge label. Let n be its vertex count. Assume a positive phase modulus p with increment one on every edge and a contraction 0 < g < 1. A nondegenerate guard interval has width d and a closed piece has width w. For every return C of length L, its map has slope (−g)^L and sends the piece into itself. Returns of equal length with distinct label words send the open guard interval to disjoint images.

Set M equal to $p \cdot \lfloor\frac{n}{p}\rfloor \cdot \lfloor\frac{2 \cdot n - 1}{p}\rfloor$. Then w is at least $\frac{g^{M}}{1 - g^{M}} \cdot d$.

In a component of n vertices, find two actual returns at the given basepoint with different synchronized label words. Their positive lengths are at most n and 2n−1. Short paths to and from each vertex define a bounded return test. If every test agreed with a short reference return, the reference word’s least period would define a phase and a label at every edge. That would give coherence for the component.

The independently supplied phase has modulus p and increases by one on every edge. It divides both return lengths. At their least common multiple the two whole guard cylinders have disjoint interiors, while the two original-piece images belong to the original piece. Their common slope can have either sign. Comparing endpoints yields the packing inequality at the least common multiple and hence the stated uniform bound.

The statement takes the original piece and guard intervals, their affine return maps, and the separation of whole guard cylinders as premises. Application to Proposition 51.3 requires deriving those premises and the second-label phase from the original legal graph.

**Theorem 1.6 (Disjoint open cylinders for distinct legal words).**

Lean statement: `D5/S1/Words/ReturnWords/ShortReturnWidthTransport.legal_word_open_cylinders_disjoint`

*Proof.* Machine-checked in Lean as `D5/S1/Words/ReturnWords/ShortReturnWidthTransport.legal_word_open_cylinders_disjoint` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Two distinct words of the same length start in a common guard. Each word is legal through its own terminal guard. The image of the open interval of the first terminal guard under its word map is disjoint from the corresponding open image for the second word.

At the first differing label, the open images lie in distinct intervals of the original five-branch partition. A common preceding label determines the next guard and acts by an injective affine map. Closed cylinders can share endpoints.

**Theorem 1.7 (Width bound using the original first-projection edges).**

Lean statement: `D5/S1/Words/ReturnWords/ShortReturnWidthTransport.width_at_original_first_piece`

*Proof.* Machine-checked in Lean as `D5/S1/Words/ReturnWords/ShortReturnWidthTransport.width_at_original_first_piece` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix a vertex of a finite cyclic strongly connected component with incoherent first labels. Its first pieces have ordered endpoints. Each arrow satisfies the legality and whole-interval containment tests of the original endpoint graph. Assume a positive phase modulus p with increment one on each arrow. Take n to be the component size, d the full guard width at the base vertex, w the width of its first piece, and g the positive contraction magnitude of the original three-bit deletion.

Set M equal to $p \cdot \lfloor\frac{n}{p}\rfloor \cdot \lfloor\frac{2 \cdot n - 1}{p}\rfloor$. Then w is at least $\frac{g^{M}}{1 - g^{M}} \cdot d$.

Edge containment gives the affine transport of each original piece along a full return, and the guard law makes its output word legal. The open-cylinder theorem supplies separation for the synchronized returns in the width argument. The next two results supply the phase from the original second-label projection and apply it jointly.

**Theorem 1.8 (A singleton projection supplies a common label phase).**

Lean statement: `D5/S1/Words/ReturnWords/ShortReturnWidthTransport.singleton_projection_phases`

*Proof.* Machine-checked in Lean as `D5/S1/Words/ReturnWords/ShortReturnWidthTransport.singleton_projection_phases` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A finite cyclic strongly connected component projects to the original endpoint graph, with one fixed label on each projected arrow. If one projected piece is a singleton in its guard interval, there is a positive phase modulus p bounded by the component size. The label depends only on the phase at the source, and each edge advances that phase by one.

Any return word prepends to the legal encodings of the singleton, preserving its guard and scalar. This is an injection because the same prefix has a unique deleted tail. The signed-series fiber classification makes the encoding fiber finite, so the injection is surjective. Both synchronized words must then be prefixes of one actual encoding and agree because they have the same length. Coherence supplies the bounded phase.

**Theorem 1.9 (The short-return width bound for a paired component with a singleton projection).**

Lean statement: `D5/S1/Words/ReturnWords/ShortReturnWidthTransport.paired_singleton_short_return_width`

*Proof.* Machine-checked in Lean as `D5/S1/Words/ReturnWords/ShortReturnWidthTransport.paired_singleton_short_return_width` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Suppose a finite cyclic strongly connected component projects along each of its two labelings to legal original endpoint-graph edges. Assume first-label incoherence, ordered endpoints of the first pieces, and a singleton second piece in its guard interval at some vertex. Write n for the size of the same component in both projections. There is one positive modulus p at most n, with a second-label phase that advances by one on each edge and determines its second label.

Set M equal to $p \cdot \lfloor\frac{n}{p}\rfloor \cdot \lfloor\frac{2 \cdot n - 1}{p}\rfloor$. At every vertex, the first-piece width is at least $\frac{g^{M}}{1 - g^{M}} \cdot d$, where d is the full first guard width and g is the contraction magnitude.

The singleton projection supplies the phase, and the first edges supply the legal return words, piece containment and full-cylinder separation. Proposition 51.3 uses these edge laws on its supplied paired component for any admissible endpoint set. Reachability or a particular endpoint color assignment is outside the width calculation.

## References

- Truth anchor: `D5/S1/Words/ReturnWords/ShortReturnWidthTransport.contraction_ratio_antitone`
- Truth anchor: `D5/S1/Words/ReturnWords/ShortReturnWidthTransport.exists_bounded_detecting_returns`
- Truth anchor: `D5/S1/Words/ReturnWords/ShortReturnWidthTransport.legal_word_open_cylinders_disjoint`
- Truth anchor: `D5/S1/Words/ReturnWords/ShortReturnWidthTransport.paired_singleton_short_return_width`
- Truth anchor: `D5/S1/Words/ReturnWords/ShortReturnWidthTransport.short_return_width_lower_bound`
- Truth anchor: `D5/S1/Words/ReturnWords/ShortReturnWidthTransport.singleton_projection_phases`
- Truth anchor: `D5/S1/Words/ReturnWords/ShortReturnWidthTransport.synchronized_length_le_phase_bound`
- Truth anchor: `D5/S1/Words/ReturnWords/ShortReturnWidthTransport.width_at_incoherent_basepoint`
- Truth anchor: `D5/S1/Words/ReturnWords/ShortReturnWidthTransport.width_at_original_first_piece`
- Dependency: [D5/S1/Digit/Infinite/FixedTailClosedBudget](../../Digit/Infinite/FixedTailClosedBudget.md)
- Dependency: [D5/S1/Digit/Infinite/OddColorThreeSource](../../Digit/Infinite/OddColorThreeSource.md)
- Dependency: [D5/S1/Words/ReturnWords/CoherentReturnPathTemplates](CoherentReturnPathTemplates.md)
