# Hardin and Barker's four-column king configurations

## Abstract

Corner-occupied configurations of non-attacking kings on four-column strips.

OEIS A228502, revision 12, NAME: "Number of n X 4 binary arrays with top left value 1 and no two ones adjacent horizontally, vertically, diagonally or antidiagonally." Rows and columns are labeled and the boundary is open. True denotes an occupied cell. The distance Nat.dist is absolute difference on natural numbers, and king adjacency is exactly maximum coordinate distance one. The projections p.1 and p.2 are row and column indices; val is the natural-valued projection from Fin.

**Definition 1.1 (The literal filtered board count).**

$$\forall n: Nat, (\operatorname{a}\left(n\right) = \operatorname{Finset.card}\left(\operatorname{Finset.filter}\left((\lambda A: (\operatorname{Fin}\left(n\right) \times \operatorname{Fin}\left(4\right)) \to Bool \mapsto ((\exists i: \operatorname{Fin}\left(n\right), ((\operatorname{val}\left(i\right) = 0) \land (A\left((i, 0)\right) = true))) \land (\forall p: \operatorname{Fin}\left(n\right) \times \operatorname{Fin}\left(4\right), (\forall q: \operatorname{Fin}\left(n\right) \times \operatorname{Fin}\left(4\right), ((p \neq q) \implies ((\operatorname{max}\left(\operatorname{dist}\left(\operatorname{val}\left(p.1\right), \operatorname{val}\left(q.1\right)\right), \operatorname{dist}\left(\operatorname{val}\left(p.2\right), \operatorname{val}\left(q.2\right)\right)\right) = 1) \implies (\neg ((A\left(p\right) = true) \land (A\left(q\right) = true))))))))), \operatorname{Finset.univ}\right)\right))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA228502Kings.a` (`✓ std3`).

*Citation.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A228502: corner-occupied non-attacking kings on four-column strips*. URL: <https://oeis.org/A228502>.

*Commentary.*

The filter ranges over every function from Fin n × Fin 4 to Bool. Its first conjunct requires an occupied cell in column zero of row zero. The existential row index makes a 0 = 0, since Fin 0 has no elements. For positive n it is exactly A(0,0) = true. Its second conjunct forbids two true values on distinct cells at king distance one, including diagonal contacts. No modular arithmetic or division is used. Natural subtraction in the recurrence indices is truncated subtraction; all subtraction between counts is performed after casting to integers.

**Definition 1.2 (Binary rows).**

$$Row = (\operatorname{Fin}\left(4\right)) \to Bool$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA228502Kings.Row` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A228502: corner-occupied non-attacking kings on four-column strips*. URL: <https://oeis.org/A228502>.

*Commentary.*

A row assigns a Boolean to each of four columns. There are sixteen such functions. The row representation is used to calculate the board count.

**Definition 1.3 (Exclusion within one row).**

$$\forall r: Row, (\operatorname{ValidRow}\left(r\right) \iff (\forall j: \operatorname{Fin}\left(4\right), (\forall k: \operatorname{Fin}\left(4\right), ((\operatorname{dist}\left(\operatorname{val}\left(j\right), \operatorname{val}\left(k\right)\right) = 1) \implies ((r\left(j\right) = true) \implies (r\left(k\right) = false))))))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA228502Kings.ValidRow` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A228502: corner-occupied non-attacking kings on four-column strips*. URL: <https://oeis.org/A228502>.

*Commentary.*

A valid row has no occupied pair in consecutive columns. Exactly eight rows are valid: the empty row, the four singleton rows, and the three pairs of zero-based columns {0,2}, {0,3} and {1,3}.

**Definition 1.4 (Exclusion between consecutive rows).**

$$\forall r: Row, (\forall s: Row, (\operatorname{Compatible}\left(r, s\right) \iff (\forall j: \operatorname{Fin}\left(4\right), (\forall k: \operatorname{Fin}\left(4\right), ((\operatorname{dist}\left(\operatorname{val}\left(j\right), \operatorname{val}\left(k\right)\right) \leq 1) \implies ((r\left(j\right) = true) \implies (s\left(k\right) = false)))))))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA228502Kings.Compatible` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A228502: corner-occupied non-attacking kings on four-column strips*. URL: <https://oeis.org/A228502>.

*Commentary.*

Compatibility forbids occupied cells in consecutive rows whose column distance is zero or one. This accounts for vertical and both diagonal contacts. Rows at distance at least two impose no constraints on each other.

**Definition 1.5 (The linear continuation operator).**

$$\forall w: (Row) \to Int, (\forall r: Row, (\operatorname{step}\left(w, r\right) = \operatorname{if} (\operatorname{ValidRow}\left(r\right)) \operatorname{then} \sum_{s: Row} (\operatorname{if} (\operatorname{Compatible}\left(r, s\right)) \operatorname{then} w\left(s\right) \operatorname{else} 0) \operatorname{else} 0))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA228502Kings.step` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A228502: corner-occupied non-attacking kings on four-column strips*. URL: <https://oeis.org/A228502>.

*Commentary.*

For a valid current row r, step w r sums w s over compatible next rows s. An invalid current row contributes zero. This is an integer-linear operator on functions of the sixteen binary rows.

**Definition 1.6 (Continuation counts).**

$$\begin{aligned}\forall r: Row, (\operatorname{v}\left(0, r\right) = \operatorname{if} (\operatorname{ValidRow}\left(r\right)) \operatorname{then} 1 \operatorname{else} 0)\\\forall k: Nat, (\forall r: Row, (\operatorname{v}\left(k + 1, r\right) = \operatorname{step}\left(\operatorname{v}\left(k\right), r\right)))\end{aligned}$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA228502Kings.v` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A228502: corner-occupied non-attacking kings on four-column strips*. URL: <https://oeis.org/A228502>.

*Commentary.*

The initial vector is the indicator of valid rows. The value v k r counts the ways to append k rows after r while keeping the whole strip free of attacking occupied cells. An invalid row r always contributes zero.

**Theorem 1.7 (The four-step continuation identity).**

$$\forall r: Row, (\operatorname{v}\left(4, r\right) = 2 \cdot \operatorname{v}\left(3, r\right) + 7 \cdot \operatorname{v}\left(2, r\right) - 2 \cdot \operatorname{v}\left(1, r\right) - 3 \cdot \operatorname{v}\left(0, r\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA228502Kings.finite_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A228502: corner-occupied non-attacking kings on four-column strips*. URL: <https://oeis.org/A228502>.

*Commentary.*

The displayed equality holds for every one of the sixteen binary rows. Applying the same linear continuation operator propagates it to every shift. The invalid rows contribute zero on both sides.

**Theorem 1.8 (The recurrence and formal generating series).**

$$(\forall n: Nat, ((5 \leq n) \implies ((\operatorname{a}\left(n\right): Int) = 2 \cdot (\operatorname{a}\left(n - 1\right): Int) + 7 \cdot (\operatorname{a}\left(n - 2\right): Int) - 2 \cdot (\operatorname{a}\left(n - 3\right): Int) - 3 \cdot (\operatorname{a}\left(n - 4\right): Int)))) \land ((1 - 2 \cdot \operatorname{PowerSeries.X} - 7 \cdot \operatorname{PowerSeries.X}^{2} + 2 \cdot \operatorname{PowerSeries.X}^{3} + 3 \cdot \operatorname{PowerSeries.X}^{4}) \cdot \operatorname{PowerSeries.mk}\left((\lambda n: Nat \mapsto ((\operatorname{a}\left(n\right): Int)))\right) = \operatorname{PowerSeries.X} \cdot (1 - \operatorname{PowerSeries.X}) \cdot (3 + 2 \cdot \operatorname{PowerSeries.X}))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA228502Kings.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A228502: corner-occupied non-attacking kings on four-column strips*. URL: <https://oeis.org/A228502>.

*Commentary.*

OEIS A228502, revision 12, first FORMULA: "Empirical: a(n) = 2*a(n-1) + 7*a(n-2) - 2*a(n-3) - 3*a(n-4)." Its second FORMULA is "Empirical g.f.: x*(1 - x)*(3 + 2*x) / (1 - 2*x - 7*x^2 + 2*x^3 + 3*x^4)." The generating function is attributed to Colin Barker. The recurrence holds at every height n at least five. PowerSeries.mk assigns the integer count a n to coefficient n; since a 0 = 0, this series begins at degree one. The formal product identity clears a denominator with constant coefficient one and needs no convergence hypothesis.

Splitting a board into its first row and its remaining rows preserves the literal king-adjacency predicate: only the first two rows can interact across the split. The equivalence between functions on the cell product and functions of rows, followed by the first-row decomposition of finite function spaces, expresses the count as the sum of v k r over rows r with r 0 = true, at height k + 1. Induction on k proves this equality for every height, including height one. The finite four-step identity and linearity yield the recurrence. The initial counts at heights zero through four are 0, 3, 5, 29 and 87; coefficient comparison with these initial values proves the formal product identity.

## References

- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA228502Kings.Compatible`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA228502Kings.Row`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA228502Kings.ValidRow`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA228502Kings.a`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA228502Kings.finite_certificate`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA228502Kings.result`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA228502Kings.step`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA228502Kings.v`
