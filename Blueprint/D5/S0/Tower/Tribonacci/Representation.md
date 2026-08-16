# Tribonacci Representation

## Abstract

Admissible Tribonacci words uniquely encode their full initial natural intervals.

Position i carries the frozen Tribonacci weight T(i+2), fixing the basis as 1, 2, 4, 7, 13, and so on. The no-111 condition makes every fixed length layer a canonical integer representation system.

**Definition 1.1 (Tribonacci integer decoding).**

$$\operatorname{decode}\left(\mathit{name}\right) = \operatorname{weightedTribonacciSum}\left(\mathit{name}\right)$$

*Formalization.* `D5/S0/Tower/Tribonacci/Representation.decode` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The definition sums T(i+2) exactly at the true positions of an admissible word and reuses the frozen Tribonacci sequence.

**Theorem 1.2 (Tribonacci decoding upper bound).**

$$\forall Q \in N,\; \forall name \in \operatorname{TribonacciName}\left(Q\right),\; \operatorname{LessThan}\left(\operatorname{decode}\left(\mathit{name}\right), \operatorname{T}\left(Q + 2\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/Tribonacci/Representation.decode_lt_tribonacci` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Removing three highest positions leaves a shorter admissible prefix. At most two of the removed positions are true, and the frozen three-term recurrence closes the strict bound.

**Theorem 1.3 (Exact maximum Tribonacci decoding value).**

$$\forall Q \in N,\; \operatorname{Maximum}\left(\operatorname{decodeAtLength}\left(Q\right)\right) = \operatorname{T}\left(Q + 2\right) - 1$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/Tribonacci/Representation.decode_max_value` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The upper bound is attained because bounded decoding is surjective; therefore the largest legal value is exactly T(Q+2) minus one.

**Theorem 1.4 (Tribonacci decoding is injective).**

$$\forall Q \in N,\; \operatorname{Injective}\left(\operatorname{decodeAtLength}\left(Q\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/Tribonacci/Representation.decode_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Induction compares the highest digits. Unequal highest digits are separated by the strict prefix bound; equal digits cancel and reduce to the shorter names.

**Theorem 1.5 (Every bounded natural has a Tribonacci name).**

$$\forall Q \in N,\; \forall n \in \operatorname{Fin}\left(\operatorname{T}\left(Q + 2\right)\right),\; \exists name \in \operatorname{TribonacciName}\left(Q\right),\; \operatorname{decode}\left(\mathit{name}\right) = n$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/Tribonacci/Representation.exists_decode_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The injective bounded decoder has the same finite cardinality on both sides by the frozen Tribonacci name-count theorem, so it is surjective onto the complete initial interval.

**Theorem 1.6 (Bounded Tribonacci decoding is bijective).**

$$\forall Q \in N,\; \operatorname{Bijective}\left(\operatorname{decodeFin}\left(Q\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/Tribonacci/Representation.decode_bijective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Combining injectivity with the exact cardinality identity gives the full existence-and-uniqueness statement at every length.

**Definition 1.7 (Tribonacci decoding equivalence).**

$$\forall Q \in N,\; \operatorname{Equiv}\left(\operatorname{TribonacciName}\left(Q\right), \operatorname{Fin}\left(\operatorname{T}\left(Q + 2\right)\right)\right)$$

*Formalization.* `D5/S0/Tower/Tribonacci/Representation.decodeEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The equivalence packages the bounded decoder and its proved inverse without choosing a second ordering of the admissible words.

**Theorem 1.8 (Tribonacci encoder makes the greedy choice).**

$$\forall Q \in N,\; \forall n \in \operatorname{Fin}\left(\operatorname{T}\left(Q + 1 + 2\right)\right),\; \operatorname{Iff}\left(\operatorname{highestDigit}\left(\operatorname{encode}\left(n\right)\right) = 1, \operatorname{LessEqual}\left(\operatorname{T}\left(Q + 2\right), n\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/Tribonacci/Representation.encode_last_eq_true_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The inverse selects the highest available weight exactly when that weight does not exceed the target, recording the usual greedy construction as a theorem.

## References

- Truth anchor: `D5/S0/Tower/Tribonacci/Representation.decode`
- Truth anchor: `D5/S0/Tower/Tribonacci/Representation.decodeEquiv`
- Truth anchor: `D5/S0/Tower/Tribonacci/Representation.decode_bijective`
- Truth anchor: `D5/S0/Tower/Tribonacci/Representation.decode_injective`
- Truth anchor: `D5/S0/Tower/Tribonacci/Representation.decode_lt_tribonacci`
- Truth anchor: `D5/S0/Tower/Tribonacci/Representation.decode_max_value`
- Truth anchor: `D5/S0/Tower/Tribonacci/Representation.encode_last_eq_true_iff`
- Truth anchor: `D5/S0/Tower/Tribonacci/Representation.exists_decode_eq`
- Dependency: [D5/S0/Tower/Tribonacci/Names](Names.md)
