# Hardin and Barker's binary ladder formulas

## Abstract

Literal two-column binary ladder counts, their recurrence and formal generating series.

OEIS A240513, revision 11, NAME: "Number of n X 2 0..1 arrays with no element equal to exactly two horizontal and vertical neighbors, with new values 0..1 introduced in row major order." The entry has no page numbers. Rows and columns are labeled, boundaries are open, and diagonal cells are not neighbors. For a binary alphabet, introduction of new values in row-major order means precisely that the first entry is zero. The value one need not occur.

**Definition 1.1 (The equal-bit indicator).**

$$\forall x: Bool, (\forall y: Bool, (\operatorname{equalBit}\left(x, y\right) = \operatorname{if} (x = y) \operatorname{then} 1 \operatorname{else} 0))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA240513Ladder.equalBit` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2014). *OEIS A240513: binary ladders with no exactly-two equal neighbors*. URL: <https://oeis.org/A240513>.

*Commentary.*

The natural-valued indicator is one for equal bits and zero otherwise. It contributes one for each equal-valued neighbor in the local conditions.

**Definition 1.2 (A binary row).**

$$Row = (\operatorname{Fin}\left(2\right)) \to Bool$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA240513Ladder.Row` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2014). *OEIS A240513: binary ladders with no exactly-two equal neighbors*. URL: <https://oeis.org/A240513>.

*Commentary.*

A row assigns a bit to each of the two labeled columns. There are four rows and sixteen ordered row-pair states.

**Definition 1.3 (The boundary-row condition).**

$$\forall r: Row, (\forall s: Row, (\operatorname{Boundary}\left(r, s\right) \iff (\forall j: \operatorname{Fin}\left(2\right), (\operatorname{equalBit}\left(r\left(\operatorname{rev}\left(j\right)\right), r\left(j\right)\right) + \operatorname{equalBit}\left(s\left(j\right), r\left(j\right)\right) \neq 2))))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA240513Ladder.Boundary` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2014). *OEIS A240513: binary ladders with no exactly-two equal neighbors*. URL: <https://oeis.org/A240513>.

*Commentary.*

Boundary r s checks row r when s is its only neighboring row. The other column and the adjacent row provide its two possible neighbors.

**Definition 1.4 (The interior-row condition).**

$$\forall r: Row, (\forall s: Row, (\forall t: Row, (\operatorname{Interior}\left(r, s, t\right) \iff (\forall j: \operatorname{Fin}\left(2\right), (\operatorname{equalBit}\left(s\left(\operatorname{rev}\left(j\right)\right), s\left(j\right)\right) + \operatorname{equalBit}\left(r\left(j\right), s\left(j\right)\right) + \operatorname{equalBit}\left(t\left(j\right), s\left(j\right)\right) \neq 2)))))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA240513Ladder.Interior` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2014). *OEIS A240513: binary ladders with no exactly-two equal neighbors*. URL: <https://oeis.org/A240513>.

*Commentary.*

Interior r s t checks the middle row s between r and t. The sum of its three equal-bit indicators must differ from two at each column.

**Definition 1.5 (The continuation step).**

$$\forall w: (Row) \to (Row) \to Int, (\forall r: Row, (\forall s: Row, (\operatorname{step}\left(w, r, s\right) = \sum_{t: Row} (\operatorname{if} (\operatorname{Interior}\left(r, s, t\right)) \operatorname{then} w\left(s, t\right) \operatorname{else} 0))))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA240513Ladder.step` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2014). *OEIS A240513: binary ladders with no exactly-two equal neighbors*. URL: <https://oeis.org/A240513>.

*Commentary.*

For an integer-valued function w on row pairs, step w r s sums w s t over all four rows t satisfying Interior r s t. Rows failing that condition contribute zero.

**Definition 1.6 (The continuation vectors).**

$$\begin{aligned}\forall r: Row, (\forall s: Row, (\operatorname{v}\left(0, r, s\right) = \operatorname{if} (\operatorname{Boundary}\left(s, r\right)) \operatorname{then} 1 \operatorname{else} 0))\\\forall k: Nat, (\forall r: Row, (\forall s: Row, (\operatorname{v}\left(k + 1, r, s\right) = \operatorname{step}\left(\operatorname{v}\left(k\right), r, s\right))))\end{aligned}$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA240513Ladder.v` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2014). *OEIS A240513: binary ladders with no exactly-two equal neighbors*. URL: <https://oeis.org/A240513>.

*Commentary.*

The zero-length continuation checks the terminal boundary row s against r. Each successor applies step to the previous vector, so v k r s counts the legal choices of k further rows with integer values.

**Definition 1.7 (The literal array count).**

$$\forall n: Nat, (\operatorname{a}\left(n\right) = \operatorname{card}\left(\{A: (\operatorname{Fin}\left(n\right) \times \operatorname{Fin}\left(2\right)) \to Bool \mid (\exists i: \operatorname{Fin}\left(n\right), ((\operatorname{val}\left(i\right) = 0) \land (A\left((i, 0)\right) = false))) \land (\forall p: \operatorname{Fin}\left(n\right) \times \operatorname{Fin}\left(2\right), (\operatorname{card}\left(\{q: \operatorname{Fin}\left(n\right) \times \operatorname{Fin}\left(2\right) \mid (((\operatorname{val}\left(p.1\right) = \operatorname{val}\left(q.1\right)) \land ((\operatorname{val}\left(p.2\right) = \operatorname{val}\left(q.2\right) + 1) \lor (\operatorname{val}\left(q.2\right) = \operatorname{val}\left(p.2\right) + 1))) \lor ((\operatorname{val}\left(p.2\right) = \operatorname{val}\left(q.2\right)) \land ((\operatorname{val}\left(p.1\right) = \operatorname{val}\left(q.1\right) + 1) \lor (\operatorname{val}\left(q.1\right) = \operatorname{val}\left(p.1\right) + 1)))) \land (A\left(q\right) = A\left(p\right))\}\right) \neq 2))\}\right))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA240513Ladder.a` (`✓ std3`).

*Citation.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2014). *OEIS A240513: binary ladders with no exactly-two equal neighbors*. URL: <https://oeis.org/A240513>.

*Commentary.*

The cell type is Fin n × Fin 2 and each board is a function from this type to Bool. False is zero. The displayed finite-set cardinality is the filter cardinality in a: its local neighbor count adds the equal-valued cell in the other column, the previous row when the row index is positive, and the next row when that row remains in the board. In width two, Fin.rev exchanges the two columns. The existential first-row condition makes a 0 = 0; for every positive height it is exactly A(0,0) = false. In height one the two choices for the other entry are both legal, so a 1 = 2.

**Theorem 1.8 (The finite continuation identity).**

$$\forall r: (\operatorname{Fin}\left(2\right)) \to Bool, (\forall s: (\operatorname{Fin}\left(2\right)) \to Bool, (\operatorname{v}\left(5, r, s\right) = 2 \cdot \operatorname{v}\left(4, r, s\right) + \operatorname{v}\left(3, r, s\right) - \operatorname{v}\left(2, r, s\right) - 2 \cdot \operatorname{v}\left(1, r, s\right) + \operatorname{v}\left(0, r, s\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA240513Ladder.finite_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2014). *OEIS A240513: binary ladders with no exactly-two equal neighbors*. URL: <https://oeis.org/A240513>.

*Commentary.*

Here r and s range over binary rows Fin 2 → Bool. The integer continuation vector starts with v 0 r s = 1 when the last row s satisfies its boundary condition against r, and zero otherwise. Its step sums v k s t over the binary rows t for which s satisfies its interior condition against r and t. The equality holds on every ordered row pair. Applying this same linear step propagates the equality to every shift; taking the boundary-weighted total then gives the recurrence in result. The finite equality is checked by kernel reduction.

**Theorem 1.9 (The signed recurrence and formal generating function).**

$$(\forall n: Nat, ((6 \leq n) \implies ((\operatorname{a}\left(n\right): Int) = 2 \cdot (\operatorname{a}\left(n - 1\right): Int) + (\operatorname{a}\left(n - 2\right): Int) - (\operatorname{a}\left(n - 3\right): Int) - 2 \cdot (\operatorname{a}\left(n - 4\right): Int) + (\operatorname{a}\left(n - 5\right): Int)))) \land ((1 - \operatorname{PowerSeries.X}) \cdot (1 - \operatorname{PowerSeries.X} - 2 \cdot \operatorname{PowerSeries.X}^{2} - \operatorname{PowerSeries.X}^{3} + \operatorname{PowerSeries.X}^{4}) \cdot \operatorname{PowerSeries.mk}\left((\lambda k: Nat \mapsto (\operatorname{a}\left(k\right): Int))\right) = \operatorname{PowerSeries.X} \cdot (2 - \operatorname{PowerSeries.X}) \cdot (1 - \operatorname{PowerSeries.X}^{2} - 2 \cdot \operatorname{PowerSeries.X}^{3}))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA240513Ladder.result` (`✓ std3`). ∎

*Resolves.* `Problems/hardin240513` (proved) by `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA240513Ladder.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"hardin240513","declaration_gid":"D5/S3/Combinatorics/TraceAvoidingArrays/HardinA240513Ladder.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2014). *OEIS A240513: binary ladders with no exactly-two equal neighbors*. URL: <https://oeis.org/A240513>.

*Commentary.*

OEIS A240513, revision 11, first FORMULA: "Empirical: a(n) = 2*a(n-1) + a(n-2) - a(n-3) - 2*a(n-4) + a(n-5)." Its second FORMULA, attributed to Colin Barker, is "Empirical g.f.: x*(2 - x)*(1 - x^2 - 2*x^3) / ((1 - x)*(1 - x - 2*x^2 - x^3 + x^4))." The recurrence holds for every natural n at least six, after casting all counts to integers. The series is PowerSeries.mk of these integer coefficients. Its constant coefficient is zero, so it is the source's series beginning at height one. The denominator has constant coefficient one; the asserted identity clears that denominator and requires no convergence assumption.

An internal state is an ordered pair of binary rows, giving sixteen states without a symmetry quotient. A boundary row compares its two available neighbors, and an interior row compares its three available neighbors. Splitting the finite function space at the first row gives the continuation sum. Induction on the number of remaining rows proves that this sum counts the literal boards, including the first-entry constraint and both end boundaries. The terminal continuation vectors satisfy v5 = 2 v4 + v3 - v2 - 2 v1 + v0 at every state. Linearity propagates this identity to all subsequent vectors. The initial counts 0, 2, 3, 6, 10, 21 and 42 supply the height-six case and the low coefficients. Comparing coefficients of the formal series proves the displayed product identity.

## References

- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA240513Ladder.Boundary`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA240513Ladder.Interior`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA240513Ladder.Row`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA240513Ladder.a`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA240513Ladder.equalBit`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA240513Ladder.finite_certificate`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA240513Ladder.result`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA240513Ladder.step`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA240513Ladder.v`
