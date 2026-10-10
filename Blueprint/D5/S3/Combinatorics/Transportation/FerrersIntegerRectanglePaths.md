# Integer rectangle paths with structural zeros

## Abstract

Nonnegative integer tables with nested legal row neighborhoods have finite legal unit rectangle paths.

**Definition 1.1 (Legal support).**

$$\forall Row \in Type, Column \in Type,\; \forall E \in \operatorname{Arrow}\left(Row, \operatorname{Arrow}\left(Column, Prop\right)\right), P \in \operatorname{Arrow}\left(Row, \operatorname{Arrow}\left(Column, Nat\right)\right),\; \operatorname{Supported}\left(E, P\right) \Leftrightarrow \left(\forall i \in Row, j \in Column,\; \left(\neg \operatorname{value}\left(E, i, j\right)\right) \Rightarrow \operatorname{value}\left(P, i, j\right) = 0\right)$$

*Formalization.* `D5/S3/Combinatorics/Transportation/FerrersIntegerRectanglePaths.Supported` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Supported(E,P) means that P(i,j) is zero whenever E(i,j) is false, for every row i and column j.

**Definition 1.2 (Complete row and column margins).**

$$\forall Row \in Type, Column \in Type,\; [\operatorname{Fintype}\left(Row\right)], [\operatorname{Fintype}\left(Column\right)], \forall P \in \operatorname{Arrow}\left(Row, \operatorname{Arrow}\left(Column, Nat\right)\right), Q \in \operatorname{Arrow}\left(Row, \operatorname{Arrow}\left(Column, Nat\right)\right),\; \operatorname{SameMargins}\left(P, Q\right) \Leftrightarrow \left(\left(\forall i \in Row,\; \operatorname{rowSum}\left(P, i\right) = \operatorname{rowSum}\left(Q, i\right)\right) \land \left(\forall j \in Column,\; \operatorname{columnSum}\left(P, j\right) = \operatorname{columnSum}\left(Q, j\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Transportation/FerrersIntegerRectanglePaths.SameMargins` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

rowSum(P,i) is the sum of P(i,j) over every column j; columnSum(P,j) is the sum of P(i,j) over every row i. SameMargins(P,Q) requires equality of each of these complete finite sums.

**Definition 1.3 (A total natural-number rectangle update).**

$$\forall Row \in Type, Column \in Type,\; [\operatorname{LinearOrder}\left(Row\right)], [\operatorname{DecidableEq}\left(Column\right)], \forall P \in \operatorname{Arrow}\left(Row, \operatorname{Arrow}\left(Column, Nat\right)\right), i \in Row, l \in Row, j \in Column, k \in Column, a \in Row, b \in Column,\; \operatorname{value}\left(\operatorname{unitSwap}\left(P, i, l, j, k\right), a, b\right) = \operatorname{ite}\left(a = i, \operatorname{ite}\left(b = j, \operatorname{NatSub}\left(\operatorname{value}\left(P, a, b\right), 1\right), \operatorname{ite}\left(b = k, \operatorname{value}\left(P, a, b\right) + 1, \operatorname{value}\left(P, a, b\right)\right)\right), \operatorname{ite}\left(a = l, \operatorname{ite}\left(b = k, \operatorname{NatSub}\left(\operatorname{value}\left(P, a, b\right), 1\right), \operatorname{ite}\left(b = j, \operatorname{value}\left(P, a, b\right) + 1, \operatorname{value}\left(P, a, b\right)\right)\right), \operatorname{value}\left(P, a, b\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Transportation/FerrersIntegerRectanglePaths.unitSwap` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

In the formula, value evaluates a function at its displayed arguments, ite selects its second argument when its first argument holds and its third otherwise, and NatSub is subtraction truncated at zero. In row i, unitSwap(P,i,l,j,k) subtracts one at column j and adds one at column k; in row l it subtracts one at k and adds one at j; other rows are unchanged. The row-i case has priority when i equals l, and each row's subtraction column has priority when j equals k. The legal-step relation below requires distinct rows and columns and positive donors, so neither overlap nor truncation occurs in a legal step.

**Definition 1.4 (A legal unit rectangle step).**

$$\forall Row \in Type, Column \in Type,\; [\operatorname{LinearOrder}\left(Row\right)], [\operatorname{DecidableEq}\left(Column\right)], \forall E \in \operatorname{Arrow}\left(Row, \operatorname{Arrow}\left(Column, Prop\right)\right), P \in \operatorname{Arrow}\left(Row, \operatorname{Arrow}\left(Column, Nat\right)\right), Pnext \in \operatorname{Arrow}\left(Row, \operatorname{Arrow}\left(Column, Nat\right)\right),\; \operatorname{RectangleStep}\left(E, P, Pnext\right) \Leftrightarrow \left(\exists i \in Row, l \in Row, j \in Column, k \in Column,\; i \ne l \land \left(j \ne k \land \left(\operatorname{value}\left(E, i, j\right) \land \left(\operatorname{value}\left(E, i, k\right) \land \left(\operatorname{value}\left(E, l, j\right) \land \left(\operatorname{value}\left(E, l, k\right) \land \left(0 < \operatorname{value}\left(P, i, j\right) \land \left(0 < \operatorname{value}\left(P, l, k\right) \land Pnext = \operatorname{unitSwap}\left(P, i, l, j, k\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Transportation/FerrersIntegerRectanglePaths.RectangleStep` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

RectangleStep(E,P,P') holds when there are distinct rows i and l and distinct columns j and k such that all four corners satisfy E, both P(i,j) and P(l,k) are positive, and P' is exactly unitSwap(P,i,l,j,k).

**Theorem 1.5 (Every intermediate table preserves the same margins and legal support).**

$$\forall Row \in Type, Column \in Type,\; [\operatorname{Fintype}\left(Row\right)], [\operatorname{Fintype}\left(Column\right)], [\operatorname{LinearOrder}\left(Row\right)], [\operatorname{DecidableEq}\left(Column\right)], \forall E \in \operatorname{Arrow}\left(Row, \operatorname{Arrow}\left(Column, Prop\right)\right), P \in \operatorname{Arrow}\left(Row, \operatorname{Arrow}\left(Column, Nat\right)\right), Q \in \operatorname{Arrow}\left(Row, \operatorname{Arrow}\left(Column, Nat\right)\right),\; \left(\left(\forall i \in Row, l \in Row,\; i \le l \Rightarrow \left(\forall j \in Column,\; \operatorname{value}\left(E, i, j\right) \Rightarrow \operatorname{value}\left(E, l, j\right)\right)\right) \land \left(\operatorname{Supported}\left(E, P\right) \land \left(\operatorname{Supported}\left(E, Q\right) \land \operatorname{SameMargins}\left(P, Q\right)\right)\right)\right) \Rightarrow \operatorname{FeasibleRectanglePath}\left(E, P, Q\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Transportation/FerrersIntegerRectanglePaths.ferrers_integer_rectangle_connected` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Rows and columns are arbitrary finite carriers. Rows have a linear order, and the allowed neighbors of a row are contained in those of every later row. Entries are natural numbers. Supported means that every forbidden cell is zero; SameMargins means equality of every complete row sum and every complete column sum.

FeasibleRectanglePath denotes the reflexive transitive closure from P to Q of the relation on tables A and B requiring RectangleStep(E,A,B), Supported(E,B), and SameMargins(B,Q). A RectangleStep chooses distinct rows i and l and distinct columns j and k, requires all four corners to be legal and both donor entries A(i,j) and A(l,k) to be positive, and performs the actual update subtracting one from those donors and adding one to A(i,k) and A(l,j). Thus the result is a finite sequence of tables, not merely a signed spanning identity.

At the first unmatched row, equal row totals provide a surplus column and a deficit column. Equal column totals and equality of all earlier rows provide a later donor whose deficit-column entry exceeds its target entry. Nested neighborhoods make the fourth corner legal. The current row's total positive excess decreases by one; the donor row's total positive excess does not increase. Strong induction on the total natural-number excess constructs a finite path. No positive-margin or interior assumption is needed; empty carriers and zero margins are included.

For a board obtained by removing one rectangular block, place the restricted rows before the unrestricted rows. Their neighborhoods are the allowed column complement and the full column set, so the theorem applies. In the five-mode two-window board, order L and B before 0, M and H; the two restricted rows cannot meet columns H and B. This gives the required nested neighborhoods of the twenty-one legal cells.

An integer table of positive total mass becomes a rational probability table after division by that same total. Two supported rational probability tables on the same finite board with nested legal row neighborhoods, equal complete row and column margins, and a common positive denominator D inherit an integer path after scaling by D; normalizing every step by D preserves their common margins and structural zeros. This application is a mathematical parameter correspondence. The Lean theorem here quantifies over natural tables, and does not establish a finite path for arbitrary real tables, the twelve-dimensional real linear kernel, the four-dimensional saturated fiber, or a physical operation on an observer's history.

Rectangle connectivity belongs to classical transportation and Markov-basis mathematics. This is a direct formal construction for nested legal neighborhoods. The adjacent KTV fixed-margin connectivity development at commit 15b5f47c9ac833bfdf99b8b29374af7a678ef4bc uses Boolean entries on the complete board and has no structural-zero predicate; it does not supply this arbitrary-multiplicity restricted-board statement. No mathematical originality is claimed.

## References

- Truth anchor: `D5/S3/Combinatorics/Transportation/FerrersIntegerRectanglePaths.RectangleStep`
- Truth anchor: `D5/S3/Combinatorics/Transportation/FerrersIntegerRectanglePaths.SameMargins`
- Truth anchor: `D5/S3/Combinatorics/Transportation/FerrersIntegerRectanglePaths.Supported`
- Truth anchor: `D5/S3/Combinatorics/Transportation/FerrersIntegerRectanglePaths.ferrers_integer_rectangle_connected`
- Truth anchor: `D5/S3/Combinatorics/Transportation/FerrersIntegerRectanglePaths.unitSwap`
