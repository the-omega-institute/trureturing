# Hardin's three-column binary strips

## Abstract

The literal three-column binary strip count and Hardin's order-twenty recurrence.

OEIS A240514, revision 6, NAME: "Number of nX3 0..1 arrays with no element equal to exactly two horizontal and vertical neighbors, with new values 0..1 introduced in row major order." The entry has no page numbers. Rows and columns are labeled. All four orthogonal neighbors are counted when in the board; the boundaries are open and there are no diagonals. For a binary alphabet the row-major introduction convention is equivalent to a false first entry. The value true need not occur.

**Definition 1.1 (Horizontal neighbors).**

$$\forall r: (\operatorname{Fin}\left(3\right)) \to Bool, (\forall j: \operatorname{Fin}\left(3\right), (\operatorname{horizontal}\left(r, j\right) = (\operatorname{if} (0 < \operatorname{val}\left(j\right)) \operatorname{then} \operatorname{equalBit}\left(r\left(\operatorname{val}\left(j\right) - 1\right), r\left(j\right)\right) \operatorname{else} 0) + (\operatorname{if} (\operatorname{val}\left(j\right) + 1 < 3) \operatorname{then} \operatorname{equalBit}\left(r\left(\operatorname{val}\left(j\right) + 1\right), r\left(j\right)\right) \operatorname{else} 0)))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA240514Strip.horizontal` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2014). *OEIS A240514: three-column binary strips with no exactly-two equal neighbors*. URL: <https://oeis.org/A240514>.

*Commentary.*

The two conditional indicators count precisely the left and right neighbors that remain within the three columns. The equalBit indicator is the public indicator from HardinA240513Ladder: it is one for equal bits and zero otherwise.

**Definition 1.2 (An end row).**

$$\forall r: (\operatorname{Fin}\left(3\right)) \to Bool, (\forall s: (\operatorname{Fin}\left(3\right)) \to Bool, (\operatorname{Boundary}\left(r, s\right) \iff (\forall j: \operatorname{Fin}\left(3\right), (\operatorname{horizontal}\left(r, j\right) + \operatorname{equalBit}\left(s\left(j\right), r\left(j\right)\right) \neq 2))))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA240514Strip.Boundary` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2014). *OEIS A240514: three-column binary strips with no exactly-two equal neighbors*. URL: <https://oeis.org/A240514>.

*Commentary.*

Boundary r s checks the horizontal neighbors of row r and its single adjacent row s.

**Definition 1.3 (An interior row).**

$$\forall r: (\operatorname{Fin}\left(3\right)) \to Bool, (\forall s: (\operatorname{Fin}\left(3\right)) \to Bool, (\forall t: (\operatorname{Fin}\left(3\right)) \to Bool, (\operatorname{Interior}\left(r, s, t\right) \iff (\forall j: \operatorname{Fin}\left(3\right), (\operatorname{horizontal}\left(s, j\right) + \operatorname{equalBit}\left(r\left(j\right), s\left(j\right)\right) + \operatorname{equalBit}\left(t\left(j\right), s\left(j\right)\right) \neq 2)))))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA240514Strip.Interior` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2014). *OEIS A240514: three-column binary strips with no exactly-two equal neighbors*. URL: <https://oeis.org/A240514>.

*Commentary.*

Interior r s t checks row s between r and t. The middle column can have four neighbors, and either outer column can have three.

**Definition 1.4 (The literal filtered count).**

$$\forall n: Nat, (\operatorname{a}\left(n\right) = \operatorname{card}\left(\{A: (\operatorname{Fin}\left(n\right) \times \operatorname{Fin}\left(3\right)) \to Bool \mid (\exists i: \operatorname{Fin}\left(n\right), ((\operatorname{val}\left(i\right) = 0) \land (A\left((i, 0)\right) = false))) \land (\forall i: \operatorname{Fin}\left(n\right), (\forall j: \operatorname{Fin}\left(3\right), (\operatorname{horizontal}\left((\lambda c \mapsto A\left((i, c)\right)), j\right) + (\operatorname{if} (0 < \operatorname{val}\left(i\right)) \operatorname{then} \operatorname{equalBit}\left(A\left((\operatorname{val}\left(i\right) - 1, j)\right), A\left((i, j)\right)\right) \operatorname{else} 0) + (\operatorname{if} (\operatorname{val}\left(i\right) + 1 < n) \operatorname{then} \operatorname{equalBit}\left(A\left((\operatorname{val}\left(i\right) + 1, j)\right), A\left((i, j)\right)\right) \operatorname{else} 0) \neq 2)))\}\right))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA240514Strip.a` (`✓ std3`).

*Citation.* R. H. Hardin; OEIS Foundation Inc. (2014). *OEIS A240514: three-column binary strips with no exactly-two equal neighbors*. URL: <https://oeis.org/A240514>.

*Commentary.*

The set in this cardinality is the filter of every function from Fin n × Fin 3 to Bool. The displayed predicate expands the local board condition: horizontal neighbors and in-bounds preceding and succeeding rows contribute their equal-bit indicators. The first-row existential requires A(0,0) = false at every positive height; it makes the empty-board count zero. The first six positive counts are 3, 6, 10, 28, 73 and 196.

**Definition 1.5 (The continuation operator).**

$$\forall w: ((\operatorname{Fin}\left(3\right)) \to Bool) \to ((\operatorname{Fin}\left(3\right)) \to Bool) \to Int, (\forall r: (\operatorname{Fin}\left(3\right)) \to Bool, (\forall s: (\operatorname{Fin}\left(3\right)) \to Bool, (\operatorname{step}\left(w, r, s\right) = \sum_{t: (\operatorname{Fin}\left(3\right)) \to Bool} ((\operatorname{if} (\operatorname{Interior}\left(r, s, t\right)) \operatorname{then} w\left(s, t\right) \operatorname{else} 0)))))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA240514Strip.step` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2014). *OEIS A240514: three-column binary strips with no exactly-two equal neighbors*. URL: <https://oeis.org/A240514>.

*Commentary.*

Each successor sums over all eight choices for the next row t. Its coefficient is one precisely when the middle row satisfies the local condition.

**Definition 1.6 (Continuation vectors).**

$$\begin{aligned}\forall r: (\operatorname{Fin}\left(3\right)) \to Bool, (\forall s: (\operatorname{Fin}\left(3\right)) \to Bool, (\operatorname{v}\left(0, r, s\right) = (\operatorname{if} (\operatorname{Boundary}\left(s, r\right)) \operatorname{then} 1 \operatorname{else} 0)))\\\forall k: Nat, (\forall r: (\operatorname{Fin}\left(3\right)) \to Bool, (\forall s: (\operatorname{Fin}\left(3\right)) \to Bool, (\operatorname{v}\left(k + 1, r, s\right) = \operatorname{step}\left(\operatorname{v}\left(k\right), r, s\right))))\end{aligned}$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA240514Strip.v` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2014). *OEIS A240514: three-column binary strips with no exactly-two equal neighbors*. URL: <https://oeis.org/A240514>.

*Commentary.*

The terminal vector checks the final row boundary. The vector v k counts continuations by k further rows after an ordered initial row pair.

**Theorem 1.7 (The finite vector identity).**

$$\forall r: (\operatorname{Fin}\left(3\right)) \to Bool, (\forall s: (\operatorname{Fin}\left(3\right)) \to Bool, (\operatorname{v}\left(20, r, s\right) = 4 \cdot \operatorname{v}\left(19, r, s\right) - 3 \cdot \operatorname{v}\left(18, r, s\right) - 2 \cdot \operatorname{v}\left(17, r, s\right) + 2 \cdot \operatorname{v}\left(16, r, s\right) + 2 \cdot \operatorname{v}\left(15, r, s\right) - 7 \cdot \operatorname{v}\left(14, r, s\right) - 8 \cdot \operatorname{v}\left(13, r, s\right) + 15 \cdot \operatorname{v}\left(12, r, s\right) + 4 \cdot \operatorname{v}\left(11, r, s\right) - 8 \cdot \operatorname{v}\left(10, r, s\right) - 4 \cdot \operatorname{v}\left(9, r, s\right) + 15 \cdot \operatorname{v}\left(8, r, s\right) + 8 \cdot \operatorname{v}\left(7, r, s\right) - 7 \cdot \operatorname{v}\left(6, r, s\right) - 2 \cdot \operatorname{v}\left(5, r, s\right) + 2 \cdot \operatorname{v}\left(4, r, s\right) + 2 \cdot \operatorname{v}\left(3, r, s\right) - 3 \cdot \operatorname{v}\left(2, r, s\right) - 4 \cdot \operatorname{v}\left(1, r, s\right) - \operatorname{v}\left(0, r, s\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA240514Strip.finite_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2014). *OEIS A240514: three-column binary strips with no exactly-two equal neighbors*. URL: <https://oeis.org/A240514>.

*Commentary.*

The identity holds on all sixty-four ordered pairs of three-bit rows. An integer table for continuation lengths zero through twenty is checked against the terminal boundary and every transfer step by kernel reduction. The displayed relation is checked on that table. Applying the linear continuation operator propagates it to every later length.

**Theorem 1.8 (The signed recurrence).**

$$\forall n: Nat, ((21 \leq n) \implies ((\operatorname{a}\left(n\right): Int) = 4 \cdot (\operatorname{a}\left(n - 1\right): Int) - 3 \cdot (\operatorname{a}\left(n - 2\right): Int) - 2 \cdot (\operatorname{a}\left(n - 3\right): Int) + 2 \cdot (\operatorname{a}\left(n - 4\right): Int) + 2 \cdot (\operatorname{a}\left(n - 5\right): Int) - 7 \cdot (\operatorname{a}\left(n - 6\right): Int) - 8 \cdot (\operatorname{a}\left(n - 7\right): Int) + 15 \cdot (\operatorname{a}\left(n - 8\right): Int) + 4 \cdot (\operatorname{a}\left(n - 9\right): Int) - 8 \cdot (\operatorname{a}\left(n - 10\right): Int) - 4 \cdot (\operatorname{a}\left(n - 11\right): Int) + 15 \cdot (\operatorname{a}\left(n - 12\right): Int) + 8 \cdot (\operatorname{a}\left(n - 13\right): Int) - 7 \cdot (\operatorname{a}\left(n - 14\right): Int) - 2 \cdot (\operatorname{a}\left(n - 15\right): Int) + 2 \cdot (\operatorname{a}\left(n - 16\right): Int) + 2 \cdot (\operatorname{a}\left(n - 17\right): Int) - 3 \cdot (\operatorname{a}\left(n - 18\right): Int) - 4 \cdot (\operatorname{a}\left(n - 19\right): Int) - (\operatorname{a}\left(n - 20\right): Int)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA240514Strip.result` (`✓ std3`). ∎

*Resolves.* `Problems/hardin240514` (proved) by `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA240514Strip.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"hardin240514","declaration_gid":"D5/S3/Combinatorics/TraceAvoidingArrays/HardinA240514Strip.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2014). *OEIS A240514: three-column binary strips with no exactly-two equal neighbors*. URL: <https://oeis.org/A240514>.

*Commentary.*

The FORMULA field of OEIS A240514, revision 6, labels this twenty-term recurrence Empirical. All counts are cast from natural numbers to integers before multiplication or subtraction. The index is a natural number at least twenty-one, equivalently a positive integer in that range. Splitting a finite board into its initial two rows and remaining rows gives a continuation count. Induction on the remaining length identifies it with v. The first-row boundary and first-entry constraint define a weighted sum of v, which therefore equals a(k+2). The finite vector identity and linearity yield the recurrence for heights at least twenty-two. The same checked continuation table and the literal singleton count a(1)=3 give the height-twenty-one boundary case.

## References

- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA240514Strip.Boundary`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA240514Strip.Interior`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA240514Strip.a`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA240514Strip.finite_certificate`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA240514Strip.horizontal`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA240514Strip.result`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA240514Strip.step`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA240514Strip.v`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA240513Ladder](HardinA240513Ladder.md)
