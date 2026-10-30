# Typed two-loop source correspondence

## Abstract

The entire actual shared-name two-loop source and its ordered histories.

**Theorem 1.1 (Exhaustive legal words and native totals).**

$$\forall h: \mathbb{R}, \forall C, E: \operatorname{Vector}, (\operatorname{Injective}\left(\operatorname{word}\right)) \land ((\forall w: \operatorname{List}\left(\operatorname{Name}\right), \forall z: \operatorname{Vertex}, \operatorname{execute}\left(\operatorname{p}, w\right) = \operatorname{some}\left(z\right) \iff \exists u: \operatorname{History}, (\operatorname{word}\left(u\right) = w) \land (\operatorname{endpoint}\left(u\right) = z)) \land ((\forall u: \operatorname{History}, (\operatorname{execute}\left(\operatorname{p}, \operatorname{word}\left(u\right)\right) = \operatorname{some}\left(\operatorname{endpoint}\left(u\right)\right)) \land (\operatorname{accumulate}\left(h, C, E, \operatorname{p}, \operatorname{word}\left(u\right)\right) = \operatorname{some}\left(\operatorname{native}\left(h, C, E, u\right)\right))) \land (\forall x, y: \operatorname{Vertex}, \operatorname{SameResponses}\left(h, C, E, x, y\right) \iff x = y)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Completion/TypedCocycleSource.source_correspondence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

There is one type, vertices p, s, t, and exactly the transitions p-a-p, p-c-s, s-a-s, s-e-t. The two loop edges have the identical operation name a. All other transitions reject and t is terminal. The complete response retains current readouts, ordered success records with name, successor and edge vector, and the first illegal attempt. The theorem proves that equality of every complete continuation response is exactly equality of states: the empty response separates distinct vertices and deterministic execution supplies identical later responses from equal vertices. No reset, failure, archive or Stop operation is added.

History.pre m, History.mid m n and History.terminal m n represent exactly a^m, a^m c a^n and a^m c a^n e, for arbitrary natural counts. The theorem proves injectivity of the ordered word map and equivalence between execution of any finite root word and existence of its normal form. Therefore every finite cut, the empty word, c, ce, zero counts and terminal histories are included.

The accumulator follows the four source edges. At p the a vector is (h,h); at s it is (h,2h); the c and e vectors are the fixed C and E. The theorem derives the normal-form totals from this accumulator: (hm,hm), C+h(m+n,m+2n), and C+E+h(m+n,m+2n). Offsets are allowed to be arbitrary real pairs; positive h,C,E give the specified native source.

This is a mathematical model with fixed native vectors and exact named execution. It supplies no physical calibration or acquisition of the source state. The proof uses induction on execution and the unique separating c position; the sharp-cost theorem consumes its injectivity bridge to recover original ordered words.

## References

- Truth anchor: `D5/S3/Observer/Completion/TypedCocycleSource.source_correspondence`
