# Literal columns and continuation counts

## Abstract

The exact three-label transfer on the five-row horizontal and diagonal exclusion graph.

A column is encoded in base three, with row r stored in digit r. Bond tests precisely the pairs of rows at distance at most one across consecutive columns. No condition is imposed within a column, or between the first and last columns.

**Definition 1.1 (The five literal row entries).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233178Chromatic.colour`

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233178Chromatic.colour` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The base-three digits of an integer below 243 give the five independent row entries, in their original row order.

**Definition 1.2 (Horizontal and diagonal exclusion).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233178Chromatic.Bond`

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233178Chromatic.Bond` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every entry in one column differs from the entries in the next column at the same row and either adjacent row.

**Definition 1.3 (Exact transfer matrix).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233178Chromatic.T`

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233178Chromatic.T` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The integer matrix has an entry one precisely for a legal pair of consecutive columns, and zero otherwise.

**Definition 1.4 (Continuation readout).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233178Chromatic.v`

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233178Chromatic.v` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The nth transfer power applied to the constant one vector counts n-column continuations of a specified boundary column.

**Theorem 1.5 (Continuation recurrence beyond the transient).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233178Chromatic.result`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233178Chromatic.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every integer vector w and every natural n, put b(k)=dotProduct(w,v(k)). Then b(n+11)=6*b(n+10)+31*b(n+9)-97*b(n+8)-163*b(n+7) +417*b(n+6)+93*b(n+5)-514*b(n+4)+192*b(n+3)+72*b(n+2)-36*b(n+1). The proof checks the finite continuation certificate and applies the existing TransferMatrix.scalarRelationShift theorem. This is an auxiliary three-label result; it does not by itself prove the normalized six-colour A233178 recurrence.

## References

- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233178Chromatic.Bond`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233178Chromatic.T`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233178Chromatic.colour`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233178Chromatic.result`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233178Chromatic.v`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/TransferMatrix](TransferMatrix.md)
