# Hardin and Barker's binary ladder formulas

## Abstract

Literal two-column binary ladder counts, their recurrence and formal generating series.

OEIS A240513, revision 11, NAME: "Number of n X 2 0..1 arrays with no element equal to exactly two horizontal and vertical neighbors, with new values 0..1 introduced in row major order." The entry has no page numbers. Rows and columns are labeled, boundaries are open, and diagonal cells are not neighbors. For a binary alphabet, introduction of new values in row-major order means precisely that the first entry is zero. The value one need not occur.

**Definition 1.1 (The literal array count).**

$$\forall n: Nat, (\operatorname{a}\left(n\right) = \operatorname{card}\left(\{A: (\operatorname{Fin}\left(n\right) \times \operatorname{Fin}\left(2\right)) \to Bool \mid (\exists i: \operatorname{Fin}\left(n\right), ((\operatorname{val}\left(i\right) = 0) \land (A\left((i, 0)\right) = false))) \land (\forall p: \operatorname{Fin}\left(n\right) \times \operatorname{Fin}\left(2\right), (\operatorname{card}\left(\{q: \operatorname{Fin}\left(n\right) \times \operatorname{Fin}\left(2\right) \mid (((\operatorname{val}\left(p.1\right) = \operatorname{val}\left(q.1\right)) \land ((\operatorname{val}\left(p.2\right) = \operatorname{val}\left(q.2\right) + 1) \lor (\operatorname{val}\left(q.2\right) = \operatorname{val}\left(p.2\right) + 1))) \lor ((\operatorname{val}\left(p.2\right) = \operatorname{val}\left(q.2\right)) \land ((\operatorname{val}\left(p.1\right) = \operatorname{val}\left(q.1\right) + 1) \lor (\operatorname{val}\left(q.1\right) = \operatorname{val}\left(p.1\right) + 1)))) \land (A\left(q\right) = A\left(p\right))\}\right) \neq 2))\}\right))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA240513Ladder.a` (`✓ std3`).

*Citation.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2014). *OEIS A240513: binary ladders with no exactly-two equal neighbors*. URL: <https://oeis.org/A240513>.

*Commentary.*

The cell type is Fin n × Fin 2 and each board is a function from this type to Bool. False is zero. The displayed finite-set cardinality is the filter cardinality in a: its local neighbor count adds the equal-valued cell in the other column, the previous row when the row index is positive, and the next row when that row remains in the board. In width two, Fin.rev exchanges the two columns. The existential first-row condition makes a 0 = 0; for every positive height it is exactly A(0,0) = false. In height one the two choices for the other entry are both legal, so a 1 = 2.

**Theorem 1.2 (The finite continuation identity).**

$$\forall r: (\operatorname{Fin}\left(2\right)) \to Bool, (\forall s: (\operatorname{Fin}\left(2\right)) \to Bool, (\operatorname{v}\left(5, r, s\right) = 2 \cdot \operatorname{v}\left(4, r, s\right) + \operatorname{v}\left(3, r, s\right) - \operatorname{v}\left(2, r, s\right) - 2 \cdot \operatorname{v}\left(1, r, s\right) + \operatorname{v}\left(0, r, s\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA240513Ladder.finite_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2014). *OEIS A240513: binary ladders with no exactly-two equal neighbors*. URL: <https://oeis.org/A240513>.

*Commentary.*

Here r and s range over binary rows Fin 2 → Bool. The integer continuation vector starts with v 0 r s = 1 when the last row s satisfies its boundary condition against r, and zero otherwise. Its step sums v k s t over the binary rows t for which s satisfies its interior condition against r and t. The equality holds on every ordered row pair. Applying this same linear step propagates the equality to every shift; taking the boundary-weighted total then gives the recurrence in result. The finite equality is checked by kernel reduction.

**Theorem 1.3 (The signed recurrence and formal generating function).**

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

- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA240513Ladder.a`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA240513Ladder.finite_certificate`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA240513Ladder.result`
