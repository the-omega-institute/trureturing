# Sun's Circular Primitive Permutation Conjecture Is False

## Abstract

Over the field of eleven elements, offset two forces the vertices two and nine to share their two cyclic neighbours. A cycle of length ten cannot contain this configuration.

**Definition 1.1 (Circular primitive permutation).**

$$claim \Leftrightarrow \left(\forall F \in \mathrm{Type},\; [\operatorname{Field}\left(F\right)] [\operatorname{Fintype}\left(F\right)] [\operatorname{DecidableEq}\left(F\right)] 7 < \operatorname{FintypeCard}\left(F\right) \Rightarrow \left(\forall a \in F,\; \exists e \in \operatorname{Fin}\left(\operatorname{FintypeCard}\left(F\right) - 1\right) \equiv \{ x : F | x \ne 0 \} ,\; \forall i \in \operatorname{Fin}\left(\operatorname{FintypeCard}\left(F\right) - 1\right),\; \operatorname{IsPrimitiveRoot}\left(a + \operatorname{val}\left(\operatorname{e}\left(i\right)\right) \cdot \operatorname{val}\left(\operatorname{e}\left(\operatorname{finRotate}\left(\operatorname{FintypeCard}\left(F\right) - 1, i\right)\right)\right), \operatorname{FintypeCard}\left(F\right) - 1\right)\right)\right)$$

*Formalization.* `D5/S3/Arith/SunCircularPrimitivePermutationRefutation.claim` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Zhi-Wei Sun, Some new problems in additive combinatorics, arXiv:1309.1679, Conjecture 3.8, asserts this property for every finite field of order greater than seven and every offset. The equivalence lists each nonzero element once. The rotation advances one position and takes the last position to the first. A root of exact order q minus one generates the multiplicative group of a field of order q.

**Theorem 1.2 (The two-neighbour obstruction).**

$$\forall A \in \mathrm{Type},\; [\operatorname{DecidableEq}\left(A\right)] \forall m \in \mathrm{Nat},\; \forall e \in \operatorname{Fin}\left(m\right) \equiv A,\; \forall u \in A,\; \forall w \in A,\; \forall S \in \operatorname{Finset}\left(A\right),\; \left(4 < m \land \left(u \ne w \land \left(\operatorname{card}\left(S\right) \le 2 \land \left(\left(\operatorname{e}\left(\operatorname{finRotate}\left(m, \operatorname{symm}\left(e, u\right)\right)\right) \in S \land \operatorname{e}\left(\operatorname{symm}\left(\operatorname{finRotate}\left(m\right), \operatorname{symm}\left(e, u\right)\right)\right) \in S\right) \land \left(\operatorname{e}\left(\operatorname{finRotate}\left(m, \operatorname{symm}\left(e, w\right)\right)\right) \in S \land \operatorname{e}\left(\operatorname{symm}\left(\operatorname{finRotate}\left(m\right), \operatorname{symm}\left(e, w\right)\right)\right) \in S\right)\right)\right)\right)\right) \Rightarrow \mathrm{False}$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/SunCircularPrimitivePermutationRefutation.twin_neighbour_obstruction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Write p and r for the positions of two distinct vertices. Each vertex has two distinct cyclic neighbours. If both pairs lie in a common set of at most two elements, the neighbour pairs coincide. Matching successors or predecessors forces p to equal r. The remaining matching interchanges predecessors and successors and would force the cycle length to divide four. Both alternatives are impossible when the length is greater than four.

**Theorem 1.3 (Failure over the field of eleven elements).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/SunCircularPrimitivePermutationRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/sun-2013-circular-primitive-permutation-refutation` (refuted) by `D5/S3/Arith/SunCircularPrimitivePermutationRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"sun-2013-circular-primitive-permutation-refutation","declaration_gid":"D5/S3/Arith/SunCircularPrimitivePermutationRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Commentary.*

In the field of eleven elements, an element outside the set containing two, six, seven and eight is zero or has second or fifth power one, so it cannot have order ten. Distinct cyclic positions have distinct vertices. With offset two, the neighbours of both two and nine must therefore lie in the set containing three and eight. Commutativity gives the same restriction for predecessors as for successors. The two-neighbour obstruction excludes the required circular permutation of the ten nonzero elements.

## References

- Truth anchor: `D5/S3/Arith/SunCircularPrimitivePermutationRefutation.claim`
- Truth anchor: `D5/S3/Arith/SunCircularPrimitivePermutationRefutation.result`
- Truth anchor: `D5/S3/Arith/SunCircularPrimitivePermutationRefutation.twin_neighbour_obstruction`
