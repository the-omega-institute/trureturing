# Boundary-word encoding

## Abstract

Boundary-word encoding of stress-three rectangles.

**Definition 1.1 (Six-letter words).**

$$\forall n: \mathbb{N}, \operatorname{Word}\left(n\right) = \operatorname{Fin}\left(n+1\right) \to \operatorname{Fin}\left(6\right)$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235301Encoding.Word` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The length includes the initial letter.

**Definition 1.2 (Legal crossing).**

$$\forall p: \mathbb{N}, \forall q: \mathbb{N}, \forall a: \operatorname{Fin}\left(6\right), \forall b: \operatorname{Fin}\left(6\right), \forall c: \operatorname{Fin}\left(6\right), \forall d: \operatorname{Fin}\left(6\right), \operatorname{Cross}\left(p, q, a, b, c, d\right) \iff (\mathrm{let} x := \operatorname{mod}\left(\operatorname{val}\left(a\right)+\operatorname{val}\left(c\right)+3\cdot p\cdot q, 6\right); \mathrm{let} y := \operatorname{mod}\left(\operatorname{val}\left(a\right)+\operatorname{val}\left(d\right)+3\cdot p\cdot (1-q), 6\right); \mathrm{let} z := \operatorname{mod}\left(\operatorname{val}\left(b\right)+\operatorname{val}\left(c\right)+3\cdot (1-p)\cdot q, 6\right); \mathrm{let} t := \operatorname{mod}\left(\operatorname{val}\left(b\right)+\operatorname{val}\left(d\right)+3\cdot (1-p)\cdot (1-q), 6\right); x<4 \land y<4 \land z<4 \land t<4 \land \lvert x+t-(y+z) \rvert = 3)$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235301Encoding.Cross` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The four residues reconstruct one block. The parity complements use natural subtraction, and the diagonal difference is taken over the integers.

**Definition 1.3 (Normalized boundary words).**

$$\forall h: \mathbb{N}, \forall w: \mathbb{N}, \forall r: \operatorname{Word}\left(h\right), \forall c: \operatorname{Word}\left(w\right), \operatorname{CodeOK}\left(r, c\right) \iff (c\left(0\right) = 0 \land \forall i: \operatorname{Fin}\left(h\right), \forall j: \operatorname{Fin}\left(w\right), \operatorname{Cross}\left(\operatorname{mod}\left(\operatorname{val}\left(i\right), 2\right), \operatorname{mod}\left(\operatorname{val}\left(j\right), 2\right), r\left(\operatorname{castSucc}\left(i\right)\right), r\left(\operatorname{succ}\left(i\right)\right), c\left(\operatorname{castSucc}\left(j\right)\right), c\left(\operatorname{succ}\left(j\right)\right)\right))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235301Encoding.CodeOK` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The column word starts at zero. Every consecutive row and column edge must cross legally.

**Lemma 1.4 (Parity at the next index).**

$$\forall n: \mathbb{N}, \operatorname{mod}\left((n+1), 2\right) = 1-\operatorname{mod}\left(n, 2\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235301Encoding.next_parity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Both sides are natural numbers.

**Theorem 1.5 (Counting by boundary words).**

$$\forall h: \mathbb{N}, \forall w: \mathbb{N}, 0<h \implies 0<w \implies \operatorname{C}\left(3, 3, h, w\right) = \operatorname{card}\left(\{u: \operatorname{Word}\left(h\right) \times \operatorname{Word}\left(w\right) \mid \operatorname{CodeOK}\left(u.1, u.2\right)\}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235301Encoding.count_codes` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Here card is Nat.card. Currying identifies the indexed rectangle with a function of two coordinates. Subtracting three times the index product modulo six gives vanishing mixed differences, so the two normalized boundary words determine the grid.

**Theorem 1.6 (Transposition).**

$$\forall h: \mathbb{N}, \forall w: \mathbb{N}, \operatorname{C}\left(3, 3, h, w\right) = \operatorname{C}\left(3, 3, w, h\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235301Encoding.count_symm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Swapping the row and column preserves the diagonal difference and is its own inverse.

## References

- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235301Encoding.CodeOK`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235301Encoding.Cross`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235301Encoding.Word`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235301Encoding.count_codes`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235301Encoding.count_symm`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235301Encoding.next_parity`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235280A235310Alphabet](HardinA235280A235310Alphabet.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235289Alphabet](HardinA235289Alphabet.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235289Recurrence](HardinA235289Recurrence.md)
