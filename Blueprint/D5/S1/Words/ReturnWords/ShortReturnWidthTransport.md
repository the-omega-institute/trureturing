# Finite packing and short return width transport

## Abstract

Finite interval chains, affine packing, and conditional short-return width estimates.

There are k+1 interval starts x(0),...,x(k). Adjacent separation accumulates to k times the separation, including the degenerate case k=0. The affine application separates full length-d intervals from the width-w images that lie in the parent. Natural division is floor division, and natural subtraction is truncated at zero.

**Lemma 1.1 (Accumulate local separation along a finite chain).**

$$\forall k \in \mathbb{N},\; \forall x \in \mathbb{N} \to \mathbb{R},\; \forall delta \in \mathbb{R},\; \forall ell \in \mathbb{R},\; \forall u \in \mathbb{R},\; \forall w \in \mathbb{R},\; \left(u \le x\left(0\right) \land \left(\left(\forall i \in \mathbb{N},\; i < k \Rightarrow x\left(i\right) + delta \le x\left(i + 1\right)\right) \land x\left(k\right) + ell \le u + w\right)\right) \Rightarrow k \cdot delta + ell \le w$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/ReturnWords/ShortReturnWidthTransport.finite_interval_chain_packing` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Induct on m<=k to prove x(0)+m delta<=x(m). The successor step combines the induction inequality with the local edge at m. At m=k the two parent endpoint bounds give k delta+ell<=w. All real delta and ell are allowed; their nonnegative instances have the interval interpretation. This estimate is used by affine_cylinder_chain_packing.

**Lemma 1.2 (Pack affine interval images using a separate separation scale).**

$$\forall k \in \mathbb{N},\; \forall L \in \mathbb{N},\; \forall g \in \mathbb{R},\; \forall d \in \mathbb{R},\; \forall w \in \mathbb{R},\; \forall u \in \mathbb{R},\; \forall x \in \mathbb{N} \to \mathbb{R},\; \left(0 < g \land \left(0 \le w \land \left(\left(\forall i \in \mathbb{N},\; i \le k \Rightarrow Icc\left(u + g^{L} \cdot x\left(i\right), u + g^{L} \cdot \left(x\left(i\right) + w\right)\right) \subseteq Icc\left(u, u + w\right)\right) \land \left(\forall i \in \mathbb{N},\; i < k \Rightarrow x\left(i\right) + d \le x\left(i + 1\right)\right)\right)\right)\right) \Rightarrow k \cdot g^{L} \cdot d \le \left(1 - g^{L}\right) \cdot w$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/ReturnWords/ShortReturnWidthTransport.affine_cylinder_chain_packing` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Set q=g^L and y(i)=u+q x(i). Whole-interval inclusion supplies the parent bounds for y(0) and y(k)+q w; the scaled adjacent inequalities supply y(i)+q d<=y(i+1). The finite chain estimate gives k q d+q w<=w, hence k q d<=(1-q)w. For k=1 this is q d<=(1-q)w, the two-cylinder packing inequality. For d>=0 the separate intervals [x(i),x(i)+d] have disjoint interiors; inclusion is required only for the width-w images. Negative d is also allowed algebraically, and no contraction upper bound is needed here. This estimate supplies short_return_width_lower_bound_of_chain.

**Lemma 1.3 (Phase divisibility bounds the synchronization length).**

$$\forall a \in \mathbb{N},\; \forall b \in \mathbb{N},\; \forall n \in \mathbb{N},\; \forall p \in \mathbb{N},\; \left(0 < p \land \left(p \mid a \land \left(p \mid b \land \left(a \le n \land b \le 2 \cdot n - 1\right)\right)\right)\right) \Rightarrow lcm\left(a, b\right) \le p \cdot \lfloor\frac{n}{p}\rfloor \cdot \lfloor\frac{2 \cdot n - 1}{p}\rfloor$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/ReturnWords/ShortReturnWidthTransport.synchronized_length_le_phase_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Writing a=p alpha and b=p gamma gives lcm(a,b)=p lcm(alpha,gamma). The quotient bounds and the Mathlib product bound give the estimate. Zero lengths are allowed. This arithmetic helper is used by short_return_width_lower_bound.

**Lemma 1.4 (The contraction ratio decreases with the positive scale).**

$$\forall g \in \mathbb{R},\; \forall L \in \mathbb{N},\; \forall M \in \mathbb{N},\; \left(0 < g \land \left(g < 1 \land \left(0 < L \land L \le M\right)\right)\right) \Rightarrow \frac{g^{M}}{1 - g^{M}} \le \frac{g^{L}}{1 - g^{L}}$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/ReturnWords/ShortReturnWidthTransport.contraction_ratio_antitone` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Power order and positive-denominator fraction comparison give this helper. Equality of scales is included. It is used by short_return_width_lower_bound.

**Lemma 1.5 (Arithmetic transport of a supplied packing inequality).**

$$\forall a \in \mathbb{N},\; \forall b \in \mathbb{N},\; \forall n \in \mathbb{N},\; \forall p \in \mathbb{N},\; \forall g \in \mathbb{R},\; \forall d \in \mathbb{R},\; \forall w \in \mathbb{R},\; \left(0 < g \land \left(g < 1 \land \left(0 \le d \land \left(\left(0 < p \land \left(p \mid a \land \left(p \mid b \land \left(a \le n \land b \le 2 \cdot n - 1\right)\right)\right)\right) \land \left(0 < a \land \left(0 < b \land g^{lcm\left(a, b\right)} \cdot d \le \left(1 - g^{lcm\left(a, b\right)}\right) \cdot w\right)\right)\right)\right)\right)\right) \Rightarrow \frac{g^{p \cdot \lfloor\frac{n}{p}\rfloor \cdot \lfloor\frac{2 \cdot n - 1}{p}\rfloor}}{1 - g^{p \cdot \lfloor\frac{n}{p}\rfloor \cdot \lfloor\frac{2 \cdot n - 1}{p}\rfloor}} \cdot d \le w$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/ReturnWords/ShortReturnWidthTransport.short_return_width_lower_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This arithmetic helper assumes packing at the actual LCM, divides by its positive denominator, and applies the LCM and ratio helpers. It is used by short_return_width_lower_bound_of_chain, which derives the packing premise from interval inclusion and adjacent separation.

**Theorem 1.6 (Transport the accumulated packing estimate to the uniform scale).**

$$\forall a \in \mathbb{N},\; \forall b \in \mathbb{N},\; \forall n \in \mathbb{N},\; \forall p \in \mathbb{N},\; \forall k \in \mathbb{N},\; \forall g \in \mathbb{R},\; \forall d \in \mathbb{R},\; \forall w \in \mathbb{R},\; \forall u \in \mathbb{R},\; \forall x \in \mathbb{N} \to \mathbb{R},\; \left(0 < g \land \left(g < 1 \land \left(0 \le d \land \left(0 \le w \land \left(\left(0 < p \land \left(p \mid a \land \left(p \mid b \land \left(a \le n \land b \le 2 \cdot n - 1\right)\right)\right)\right) \land \left(0 < a \land \left(0 < b \land \left(\left(\forall i \in \mathbb{N},\; i \le k \Rightarrow Icc\left(u + g^{lcm\left(a, b\right)} \cdot x\left(i\right), u + g^{lcm\left(a, b\right)} \cdot \left(x\left(i\right) + w\right)\right) \subseteq Icc\left(u, u + w\right)\right) \land \left(\forall i \in \mathbb{N},\; i < k \Rightarrow x\left(i\right) + d \le x\left(i + 1\right)\right)\right)\right)\right)\right)\right)\right)\right)\right) \Rightarrow \frac{g^{p \cdot \lfloor\frac{n}{p}\rfloor \cdot \lfloor\frac{2 \cdot n - 1}{p}\rfloor}}{1 - g^{p \cdot \lfloor\frac{n}{p}\rfloor \cdot \lfloor\frac{2 \cdot n - 1}{p}\rfloor}} \cdot k \cdot d \le w$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/ReturnWords/ShortReturnWidthTransport.short_return_width_lower_bound_of_chain` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Put L=lcm(a,b) and M=p floor(n/p) floor((2n-1)/p). Applying the affine packing theorem derives k g^L d<=(1-g^L)w from the interval hypotheses. The arithmetic helpers give L<=M and decrease the ratio, yielding w>=k g^M d/(1-g^M). The k=1 specialization recovers the two-cylinder width bound. The cardinality factor retains the full chain estimate; no packing inequality is assumed as a premise of this chain application.

The chain statement uses abstract intervals with positive affine orientation. The full guard cylinders supply separation, and the smaller images supply containment in the original piece.

**Theorem 1.7 (Width at every basepoint of an incoherent cyclic component).**

Lean statement: `D5/S1/Words/ReturnWords/ShortReturnWidthTransport.width_at_incoherent_basepoint`

*Proof.* Machine-checked in Lean as `D5/S1/Words/ReturnWords/ShortReturnWidthTransport.width_at_incoherent_basepoint` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix a vertex of a finite cyclic strongly connected component that is incoherent for a single-symbol edge label. Let n be its vertex count. Assume a positive phase modulus p with increment one on every edge and a contraction 0 < g < 1. A nondegenerate guard interval has width d and a closed piece has width w. For every return C of length L, its map has slope (−g)^L and sends the piece into itself. Returns of equal length with distinct label words send the open guard interval to disjoint images.

Set M equal to $p \cdot \lfloor\frac{n}{p}\rfloor \cdot \lfloor\frac{2 \cdot n - 1}{p}\rfloor$. Then w is at least $\frac{g^{M}}{1 - g^{M}} \cdot d$.

In a component of n vertices, find two actual returns at the given basepoint with different synchronized label words. Their positive lengths are at most n and 2n−1. Short paths to and from each vertex define a bounded return test. If every test agreed with a short reference return, the reference word’s least period would define a phase and a label at every edge. That would give coherence for the component.

The independently supplied phase has modulus p and increases by one on every edge. It divides both return lengths. At their least common multiple the two whole guard cylinders have disjoint interiors, while the two original-piece images belong to the original piece. Their common slope can have either sign. Comparing endpoints yields the packing inequality at the least common multiple and hence the stated uniform bound.

The statement takes the original piece and guard intervals, their affine return maps, and the separation of whole guard cylinders as premises. Application to Proposition 51.3 requires deriving those premises and the second-label phase from the original legal graph.

**Theorem 1.8 (Disjoint open cylinders for distinct legal words).**

Lean statement: `D5/S1/Words/ReturnWords/ShortReturnWidthTransport.legal_word_open_cylinders_disjoint`

*Proof.* Machine-checked in Lean as `D5/S1/Words/ReturnWords/ShortReturnWidthTransport.legal_word_open_cylinders_disjoint` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Two distinct words of the same length start in a common guard. Each word is legal through its own terminal guard. The image of the open interval of the first terminal guard under its word map is disjoint from the corresponding open image for the second word.

At the first differing label, the open images lie in distinct intervals of the original five-branch partition. A common preceding label determines the next guard and acts by an injective affine map. Closed cylinders can share endpoints.

**Theorem 1.9 (Width bound using the original first-projection edges).**

Lean statement: `D5/S1/Words/ReturnWords/ShortReturnWidthTransport.width_at_original_first_piece`

*Proof.* Machine-checked in Lean as `D5/S1/Words/ReturnWords/ShortReturnWidthTransport.width_at_original_first_piece` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix a vertex of a finite cyclic strongly connected component with incoherent first labels. Assume each arrow projects to an edge of the original endpoint graph with that label, and assume a positive phase modulus p with increment one on each arrow. Take n to be the component size, d the full guard width at the base vertex, w the width of its first piece, and g the positive contraction magnitude of the original three-bit deletion.

Set M equal to $p \cdot \lfloor\frac{n}{p}\rfloor \cdot \lfloor\frac{2 \cdot n - 1}{p}\rfloor$. Then w is at least $\frac{g^{M}}{1 - g^{M}} \cdot d$.

Edge containment gives the affine transport of each original piece along a full return, and the guard law makes its output word legal. The open-cylinder theorem supplies separation for the synchronized returns in the width argument. The next two results supply the phase from the original second-label projection and apply it jointly.

**Theorem 1.10 (A singleton projection supplies a common label phase).**

Lean statement: `D5/S1/Words/ReturnWords/ShortReturnWidthTransport.singleton_projection_phases`

*Proof.* Machine-checked in Lean as `D5/S1/Words/ReturnWords/ShortReturnWidthTransport.singleton_projection_phases` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A finite cyclic strongly connected component projects to the original endpoint graph, with one fixed label on each projected arrow. If one projected piece is a singleton, there is a positive phase modulus p bounded by the component size. The label depends only on the phase at the source, and each edge advances that phase by one.

Any return word prepends to the legal encodings of the singleton, preserving its guard and scalar. This is an injection because the same prefix has a unique deleted tail. The signed-series fiber classification makes the encoding fiber finite, so the injection is surjective. Both synchronized words must then be prefixes of one actual encoding and agree because they have the same length. Coherence supplies the bounded phase.

**Theorem 1.11 (The short-return width bound for a paired component with a singleton projection).**

Lean statement: `D5/S1/Words/ReturnWords/ShortReturnWidthTransport.paired_singleton_short_return_width`

*Proof.* Machine-checked in Lean as `D5/S1/Words/ReturnWords/ShortReturnWidthTransport.paired_singleton_short_return_width` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Suppose a finite cyclic strongly connected component projects along each of its two labelings to legal original endpoint-graph edges. Assume first-label incoherence and a singleton second piece at some vertex. Write n for the size of the same component in both projections. There is one positive modulus p at most n, with a second-label phase that advances by one on each edge and determines its second label.

Set M equal to $p \cdot \lfloor\frac{n}{p}\rfloor \cdot \lfloor\frac{2 \cdot n - 1}{p}\rfloor$. At every vertex, the first-piece width is at least $\frac{g^{M}}{1 - g^{M}} \cdot d$, where d is the full first guard width and g is the contraction magnitude.

The singleton projection supplies the phase, and the first edges supply the legal return words, piece containment and full-cylinder separation. This uses the supplied paired component of Proposition 51.3. Reachability or a particular endpoint color assignment is outside the width calculation.

## References

- Truth anchor: `D5/S1/Words/ReturnWords/ShortReturnWidthTransport.affine_cylinder_chain_packing`
- Truth anchor: `D5/S1/Words/ReturnWords/ShortReturnWidthTransport.contraction_ratio_antitone`
- Truth anchor: `D5/S1/Words/ReturnWords/ShortReturnWidthTransport.finite_interval_chain_packing`
- Truth anchor: `D5/S1/Words/ReturnWords/ShortReturnWidthTransport.legal_word_open_cylinders_disjoint`
- Truth anchor: `D5/S1/Words/ReturnWords/ShortReturnWidthTransport.paired_singleton_short_return_width`
- Truth anchor: `D5/S1/Words/ReturnWords/ShortReturnWidthTransport.short_return_width_lower_bound`
- Truth anchor: `D5/S1/Words/ReturnWords/ShortReturnWidthTransport.short_return_width_lower_bound_of_chain`
- Truth anchor: `D5/S1/Words/ReturnWords/ShortReturnWidthTransport.singleton_projection_phases`
- Truth anchor: `D5/S1/Words/ReturnWords/ShortReturnWidthTransport.synchronized_length_le_phase_bound`
- Truth anchor: `D5/S1/Words/ReturnWords/ShortReturnWidthTransport.width_at_incoherent_basepoint`
- Truth anchor: `D5/S1/Words/ReturnWords/ShortReturnWidthTransport.width_at_original_first_piece`
- Dependency: [D5/S1/Digit/Infinite/FixedTailClosedBudget](../../Digit/Infinite/FixedTailClosedBudget.md)
- Dependency: [D5/S1/Digit/Infinite/OddColorThreeSource](../../Digit/Infinite/OddColorThreeSource.md)
- Dependency: [D5/S1/Words/ReturnWords/CoherentReturnPathTemplates](CoherentReturnPathTemplates.md)
