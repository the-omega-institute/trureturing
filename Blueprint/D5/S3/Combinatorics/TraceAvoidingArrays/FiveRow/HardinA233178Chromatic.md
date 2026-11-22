# Literal columns and continuation counts

## Abstract

The exact three-label transfer on the five-row horizontal and diagonal exclusion graph.

A column is encoded in base three, with row r stored in digit r. Bond tests precisely the pairs of rows at distance at most one across consecutive columns. The strip has free boundaries and has no within-column bonds.

**Definition 1.1 (moves).**

$$\forall (p: \operatorname{HardinA233178Chromatic}.\operatorname{Column}), ((\operatorname{HardinA233178Chromatic}.\operatorname{moves}\left(p\right): \operatorname{List}\left(\operatorname{HardinA233178Chromatic}.\operatorname{Column}\right)) = \operatorname{List}.\operatorname{filter}\left((\lambda (q: \operatorname{HardinA233178Chromatic}.\operatorname{Column})\mapsto \operatorname{decide}\left(\operatorname{HardinA233178Chromatic}.\operatorname{Bond}\left(p, q\right)\right)), \operatorname{List}.\operatorname{finRange}\left(243\right)\right))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/FiveRow/HardinA233178Chromatic.moves` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each entry lists the codes of all legal successor columns.

**Definition 1.2 (table).**

$$\forall (k: \operatorname{Fin}\left(12\right)), ((\operatorname{HardinA233178Chromatic}.\operatorname{table}\left(k\right): \operatorname{HardinA233178Chromatic}.\operatorname{Column} \to \operatorname{Int}) = \operatorname{Matrix}.\operatorname{mulVec}\left((\operatorname{HardinA233178Chromatic}.\operatorname{T})^{\operatorname{Fin}.\operatorname{val}\left(k\right)}, (1: \operatorname{HardinA233178Chromatic}.\operatorname{Column} \to \operatorname{Int})\right))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/FiveRow/HardinA233178Chromatic.table` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Rows are indexed by the number of extra columns and columns by the boundary code.

**Definition 1.3 (coefficients).**

$$(\operatorname{HardinA233178Chromatic}.\operatorname{coefficients}: \operatorname{Fin}\left(10\right) \to \operatorname{Int}) = \operatorname{Matrix}.\operatorname{vecCons}\left((-36), \operatorname{Matrix}.\operatorname{vecCons}\left(72, \operatorname{Matrix}.\operatorname{vecCons}\left(192, \operatorname{Matrix}.\operatorname{vecCons}\left((-514), \operatorname{Matrix}.\operatorname{vecCons}\left(93, \operatorname{Matrix}.\operatorname{vecCons}\left(417, \operatorname{Matrix}.\operatorname{vecCons}\left((-163), \operatorname{Matrix}.\operatorname{vecCons}\left((-97), \operatorname{Matrix}.\operatorname{vecCons}\left(31, \operatorname{Matrix}.\operatorname{vecCons}\left(6, \operatorname{Matrix}.\operatorname{vecEmpty}\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/FiveRow/HardinA233178Chromatic.coefficients` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The coefficients are listed in order of increasing power.

**Theorem 1.4 (step_fast).**

$$\forall (w: \operatorname{HardinA233178Chromatic}.\operatorname{Column} \to \operatorname{Int}), (\forall (p: \operatorname{HardinA233178Chromatic}.\operatorname{Column}), (\operatorname{Matrix}.\operatorname{mulVec}\left(\operatorname{HardinA233178Chromatic}.\operatorname{T}, w\right)\left(p\right) = \operatorname{List}.\operatorname{sum}\left(\operatorname{List}.\operatorname{map}\left(w, \operatorname{HardinA233178Chromatic}.\operatorname{moves}\left(p\right)\right)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/FiveRow/HardinA233178Chromatic.step_fast` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Matrix action at a boundary is the sum over its legal successors.

**Theorem 1.5 (powers_table).**

$$\forall (k: \operatorname{Fin}\left(12\right)), (\operatorname{Matrix}.\operatorname{mulVec}\left((\operatorname{HardinA233178Chromatic}.\operatorname{T})^{\operatorname{Fin}.\operatorname{val}\left(k\right)}, (1: \operatorname{HardinA233178Chromatic}.\operatorname{Column} \to \operatorname{Int})\right) = \operatorname{HardinA233178Chromatic}.\operatorname{table}\left(k\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/FiveRow/HardinA233178Chromatic.powers_table` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The tabulated row is the continuation vector at the specified exponent.

**Definition 1.6 (Column).**

$$\operatorname{HardinA233178Chromatic}.\operatorname{Column} = \operatorname{Fin}\left(243\right)$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/FiveRow/HardinA233178Chromatic.Column` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Five-row column codes in base three.

**Definition 1.7 (colour).**

$$\forall (p: \operatorname{HardinA233178Chromatic}.\operatorname{Column}), (\forall (r: \operatorname{Fin}\left(5\right)), (\operatorname{Fin}.\operatorname{val}\left((\operatorname{HardinA233178Chromatic}.\operatorname{colour}\left(p, r\right): \operatorname{Fin}\left(3\right))\right) = \operatorname{Nat}.\operatorname{mod}\left(\operatorname{Nat}.\operatorname{div}\left(\operatorname{Fin}.\operatorname{val}\left(p\right), (3)^{\operatorname{Fin}.\operatorname{val}\left(r\right)}\right), 3\right)))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/FiveRow/HardinA233178Chromatic.colour` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Nat.div takes the natural quotient and Nat.mod takes its remainder modulo three.

**Definition 1.8 (Bond).**

$$\forall (p: \operatorname{HardinA233178Chromatic}.\operatorname{Column}), (\forall (q: \operatorname{HardinA233178Chromatic}.\operatorname{Column}), (\operatorname{HardinA233178Chromatic}.\operatorname{Bond}\left(p, q\right) \Leftrightarrow (\forall (r: \operatorname{Fin}\left(5\right)), (\forall (s: \operatorname{Fin}\left(5\right)), ((\operatorname{Fin}.\operatorname{val}\left(r\right) \le \operatorname{Fin}.\operatorname{val}\left(s\right) + 1 \land \operatorname{Fin}.\operatorname{val}\left(s\right) \le \operatorname{Fin}.\operatorname{val}\left(r\right) + 1) \Rightarrow \operatorname{HardinA233178Chromatic}.\operatorname{colour}\left(p, r\right) \ne \operatorname{HardinA233178Chromatic}.\operatorname{colour}\left(q, s\right))))))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/FiveRow/HardinA233178Chromatic.Bond` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each entry differs from the entries at the same or adjacent rows of the next column.

**Definition 1.9 (instDecidableBond).**

$$\forall (p: \operatorname{HardinA233178Chromatic}.\operatorname{Column}), (\forall (q: \operatorname{HardinA233178Chromatic}.\operatorname{Column}), ((\operatorname{HardinA233178Chromatic}.\operatorname{instDecidableBond}\left(p, q\right): \operatorname{Decidable}\left(\operatorname{HardinA233178Chromatic}.\operatorname{Bond}\left(p, q\right)\right))))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/FiveRow/HardinA233178Chromatic.instDecidableBond` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The legal-bond predicate is decidable by checking the finitely many row pairs.

**Definition 1.10 (T).**

$$\forall (p: \operatorname{HardinA233178Chromatic}.\operatorname{Column}), (\forall (q: \operatorname{HardinA233178Chromatic}.\operatorname{Column}), ((\operatorname{HardinA233178Chromatic}.\operatorname{T}\left(p, q\right): \operatorname{Int}) = \operatorname{if} \operatorname{HardinA233178Chromatic}.\operatorname{Bond}\left(p, q\right) \operatorname{then} 1 \operatorname{else} 0))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/FiveRow/HardinA233178Chromatic.T` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Rows index the current column and columns index its successor.

**Definition 1.11 (v).**

$$\forall (n: \operatorname{Nat}), ((\operatorname{HardinA233178Chromatic}.\operatorname{v}\left(n\right): \operatorname{HardinA233178Chromatic}.\operatorname{Column} \to \operatorname{Int}) = \operatorname{Matrix}.\operatorname{mulVec}\left((\operatorname{HardinA233178Chromatic}.\operatorname{T})^{n}, (1: \operatorname{HardinA233178Chromatic}.\operatorname{Column} \to \operatorname{Int})\right))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/FiveRow/HardinA233178Chromatic.v` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each coordinate counts continuations of the specified length from its boundary column.

**Theorem 1.12 (result).**

$$\forall (w: \operatorname{HardinA233178Chromatic}.\operatorname{Column} \to \operatorname{Int}), (\forall (n: \operatorname{Nat}), (\operatorname{dotProduct}\left(w, \operatorname{HardinA233178Chromatic}.\operatorname{v}\left(n + 11\right)\right) = 6 \cdot \operatorname{dotProduct}\left(w, \operatorname{HardinA233178Chromatic}.\operatorname{v}\left(n + 10\right)\right) + 31 \cdot \operatorname{dotProduct}\left(w, \operatorname{HardinA233178Chromatic}.\operatorname{v}\left(n + 9\right)\right) - 97 \cdot \operatorname{dotProduct}\left(w, \operatorname{HardinA233178Chromatic}.\operatorname{v}\left(n + 8\right)\right) - 163 \cdot \operatorname{dotProduct}\left(w, \operatorname{HardinA233178Chromatic}.\operatorname{v}\left(n + 7\right)\right) + 417 \cdot \operatorname{dotProduct}\left(w, \operatorname{HardinA233178Chromatic}.\operatorname{v}\left(n + 6\right)\right) + 93 \cdot \operatorname{dotProduct}\left(w, \operatorname{HardinA233178Chromatic}.\operatorname{v}\left(n + 5\right)\right) - 514 \cdot \operatorname{dotProduct}\left(w, \operatorname{HardinA233178Chromatic}.\operatorname{v}\left(n + 4\right)\right) + 192 \cdot \operatorname{dotProduct}\left(w, \operatorname{HardinA233178Chromatic}.\operatorname{v}\left(n + 3\right)\right) + 72 \cdot \operatorname{dotProduct}\left(w, \operatorname{HardinA233178Chromatic}.\operatorname{v}\left(n + 2\right)\right) - 36 \cdot \operatorname{dotProduct}\left(w, \operatorname{HardinA233178Chromatic}.\operatorname{v}\left(n + 1\right)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/FiveRow/HardinA233178Chromatic.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The finite vector relation propagates to all subsequent exponents by TransferMatrix.scalarRelationShift.

## References

- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/FiveRow/HardinA233178Chromatic.Bond`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/FiveRow/HardinA233178Chromatic.Column`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/FiveRow/HardinA233178Chromatic.T`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/FiveRow/HardinA233178Chromatic.coefficients`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/FiveRow/HardinA233178Chromatic.colour`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/FiveRow/HardinA233178Chromatic.instDecidableBond`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/FiveRow/HardinA233178Chromatic.moves`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/FiveRow/HardinA233178Chromatic.powers_table`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/FiveRow/HardinA233178Chromatic.result`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/FiveRow/HardinA233178Chromatic.step_fast`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/FiveRow/HardinA233178Chromatic.table`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/FiveRow/HardinA233178Chromatic.v`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/TransferMatrix](../TransferMatrix.md)
