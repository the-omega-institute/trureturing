# Hardin's width-two pattern-avoiding arrays

## Abstract

Hardin's width-two array recurrence and offset-one generating function.

OEIS A206981, revision 17, NAME: "Number of n X 2 0..1 arrays avoiding the patterns 0 1 0 or 1 0 1 in any row, column, diagonal or antidiagonal." The entry has no page numbers. A cell has row index in Fin n and column index in Fin 2; false represents 0 and true represents 1. Rectangles have no wraparound, and all forbidden triples are contiguous.

**Definition 1.1 (The two forbidden triples).**

$$\forall x: Bool, (\forall y: Bool, (\forall z: Bool, ((\operatorname{Forbidden}\left(x, y, z\right)) \iff (((x = false) \land ((y = true) \land (z = false))) \lor ((x = true) \land ((y = false) \land (z = true)))))))$$

*Formalization.* `D5/S1/Words/AdmissibleWords/HardinWidthTwoRecurrence.Forbidden` (`✓ std3`).

*Citation.* R. H. Hardin; OEIS Foundation Inc. (2012). *OEIS A206981 — Width-two binary arrays avoiding alternating triples*. URL: <https://oeis.org/A206981>.

*Commentary.*

OEIS A206981, revision 17, NAME: "Number of n X 2 0..1 arrays avoiding the patterns 0 1 0 or 1 0 1 in any row, column, diagonal or antidiagonal." The entry has no page numbers. The two displayed Boolean triples represent its patterns 0 1 0 and 1 0 1.

**Definition 1.2 (Contiguous triples in the four directions).**

$$\forall n: Nat, (\forall p: \operatorname{Fin}\left(n\right) \times \operatorname{Fin}\left(2\right), (\forall q: \operatorname{Fin}\left(n\right) \times \operatorname{Fin}\left(2\right), (\forall r: \operatorname{Fin}\left(n\right) \times \operatorname{Fin}\left(2\right), ((\operatorname{StraightTriple}\left(p, q, r\right)) \iff (\exists dr: Int, (\exists dc: Int, ((((dr = 0) \land (dc = 1)) \lor (((dr = 1) \land (dc = 0)) \lor (((dr = 1) \land (dc = 1)) \lor ((dr = 1) \land (dc = -1))))) \land (((\operatorname{val}\left(q.1\right): Int) = (\operatorname{val}\left(p.1\right): Int) + dr) \land (((\operatorname{val}\left(r.1\right): Int) = (\operatorname{val}\left(q.1\right): Int) + dr) \land (((\operatorname{val}\left(q.2\right): Int) = (\operatorname{val}\left(p.2\right): Int) + dc) \land ((\operatorname{val}\left(r.2\right): Int) = (\operatorname{val}\left(q.2\right): Int) + dc)))))))))))$$

*Formalization.* `D5/S1/Words/AdmissibleWords/HardinWidthTwoRecurrence.StraightTriple` (`✓ std3`).

*Citation.* R. H. Hardin; OEIS Foundation Inc. (2012). *OEIS A206981 — Width-two binary arrays avoiding alternating triples*. URL: <https://oeis.org/A206981>.

*Commentary.*

OEIS A206981, revision 17, NAME: "Number of n X 2 0..1 arrays avoiding the patterns 0 1 0 or 1 0 1 in any row, column, diagonal or antidiagonal." The entry has no page numbers. The four direction steps are (0,1), (1,0), (1,1) and (1,-1). Coordinates are cast to Int before adding a step; all three cells remain in the finite rectangle. Reversing a step preserves both forbidden patterns.

**Definition 1.3 (The source array predicate).**

$$\forall n: Nat, (\forall A: (\operatorname{Fin}\left(n\right)) \to ((\operatorname{Fin}\left(2\right)) \to (Bool)), ((\operatorname{Avoids}\left(A\right)) \iff (\forall p: \operatorname{Fin}\left(n\right) \times \operatorname{Fin}\left(2\right), (\forall q: \operatorname{Fin}\left(n\right) \times \operatorname{Fin}\left(2\right), (\forall r: \operatorname{Fin}\left(n\right) \times \operatorname{Fin}\left(2\right), ((\operatorname{StraightTriple}\left(p, q, r\right)) \implies (\neg (\operatorname{Forbidden}\left(A\left(p.1, p.2\right), A\left(q.1, q.2\right), A\left(r.1, r.2\right)\right)))))))))$$

*Formalization.* `D5/S1/Words/AdmissibleWords/HardinWidthTwoRecurrence.Avoids` (`✓ std3`).

*Citation.* R. H. Hardin; OEIS Foundation Inc. (2012). *OEIS A206981 — Width-two binary arrays avoiding alternating triples*. URL: <https://oeis.org/A206981>.

*Commentary.*

OEIS A206981, revision 17, NAME: "Number of n X 2 0..1 arrays avoiding the patterns 0 1 0 or 1 0 1 in any row, column, diagonal or antidiagonal." The entry has no page numbers. Avoids checks every triple in the four listed directions on the actual array.

**Definition 1.4 (The actual array count).**

$$\forall n: Nat, (\operatorname{a}\left(n\right) = \operatorname{Nat.card}\left(\{A: (\operatorname{Fin}\left(n\right)) \to ((\operatorname{Fin}\left(2\right)) \to (Bool)) \mid \operatorname{Avoids}\left(A\right)\}\right))$$

*Formalization.* `D5/S1/Words/AdmissibleWords/HardinWidthTwoRecurrence.a` (`✓ std3`).

*Citation.* R. H. Hardin; OEIS Foundation Inc. (2012). *OEIS A206981 — Width-two binary arrays avoiding alternating triples*. URL: <https://oeis.org/A206981>.

*Commentary.*

OEIS A206981, revision 17, NAME: "Number of n X 2 0..1 arrays avoiding the patterns 0 1 0 or 1 0 1 in any row, column, diagonal or antidiagonal." The entry has no page numbers. The number of arrays is the cardinality of the subtype of finite binary arrays satisfying Avoids. The empty rectangle has its usual array count; the generating series begins at height one.

**Definition 1.5 (The offset-one ordinary generating series).**

$$gf = \operatorname{PowerSeries.mk}\left((\lambda n: Nat \mapsto \operatorname{ite}\left((n = 0), 0, (\operatorname{a}\left(n\right): Int)\right))\right)$$

*Formalization.* `D5/S1/Words/AdmissibleWords/HardinWidthTwoRecurrence.gf` (`✓ std3`).

*Citation.* R. H. Hardin; OEIS Foundation Inc. (2012). *OEIS A206981 — Width-two binary arrays avoiding alternating triples*. URL: <https://oeis.org/A206981>.

*Commentary.*

OEIS A206981, revision 17, OFFSET: "1,1". The entry has no page numbers. Thus gf is an integer formal power series whose constant coefficient is zero and whose coefficient at every positive n is the integer cast of a n. No convergence assumption is used.

**Definition 1.6 (The first FORMULA assertion).**

$$(claim) \iff ((\forall n: Nat, ((4 \leq n) \implies ((\operatorname{a}\left(n\right): Int) = 2 \cdot (\operatorname{a}\left(n - 1\right): Int) + 2 \cdot (\operatorname{a}\left(n - 2\right): Int) - (\operatorname{a}\left(n - 3\right): Int)))) \land (gf \cdot (1 - 2 \cdot \operatorname{PowerSeries.X} - 2 \cdot \operatorname{PowerSeries.X}^{2} + \operatorname{PowerSeries.X}^{3}) = 4 \cdot \operatorname{PowerSeries.X} + 8 \cdot \operatorname{PowerSeries.X}^{2} - 4 \cdot \operatorname{PowerSeries.X}^{3}))$$

*Formalization.* `D5/S1/Words/AdmissibleWords/HardinWidthTwoRecurrence.claim` (`✓ std3`).

*Citation.* R. H. Hardin; OEIS Foundation Inc. (2012). *OEIS A206981 — Width-two binary arrays avoiding alternating triples*. URL: <https://oeis.org/A206981>.

*Commentary.*

OEIS A206981, revision 17, first FORMULA: "Empirical: a(n) = 2*a(n-1) + 2*a(n-2) - a(n-3). G.f.: -4*x*(-1-2*x+x^2) / ( (1+x)*(x^2-3*x+1) )." The entry has no page numbers. The recurrence starts at n ≥ 4; lagged indices use Nat subtraction and count values are cast to Int. The generating-function denominator has constant coefficient one. Multiplying out (1+x)*(x^2-3*x+1) and the printed numerator gives exactly the displayed formal-series identity.

**Theorem 1.7 (The recurrence and generating function).**

$$(\forall n: Nat, ((4 \leq n) \implies ((\operatorname{a}\left(n\right): Int) = 2 \cdot (\operatorname{a}\left(n - 1\right): Int) + 2 \cdot (\operatorname{a}\left(n - 2\right): Int) - (\operatorname{a}\left(n - 3\right): Int)))) \land (gf \cdot (1 - 2 \cdot \operatorname{PowerSeries.X} - 2 \cdot \operatorname{PowerSeries.X}^{2} + \operatorname{PowerSeries.X}^{3}) = 4 \cdot \operatorname{PowerSeries.X} + 8 \cdot \operatorname{PowerSeries.X}^{2} - 4 \cdot \operatorname{PowerSeries.X}^{3})$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/AdmissibleWords/HardinWidthTwoRecurrence.result` (`✓ std3`). ∎

*Resolves.* `Problems/hardin-a206981-width-two-recurrence` (proved) by `D5/S1/Words/AdmissibleWords/HardinWidthTwoRecurrence.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"hardin-a206981-width-two-recurrence","declaration_gid":"D5/S1/Words/AdmissibleWords/HardinWidthTwoRecurrence.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2012). *OEIS A206981 — Width-two binary arrays avoiding alternating triples*. URL: <https://oeis.org/A206981>.

*Commentary.*

Width two excludes horizontal and diagonal triples, leaving two independent legal columns. A positive-length column is determined by its first bit and its adjacent XOR switches. A forbidden triple occurs exactly when two consecutive switches are true. The existing admissible-word enumeration therefore gives 2 F(n+1) columns and 4 F(n+1)^2 arrays for each n ≥ 1. Mathlib's Fin.partialSum inverse laws reconstruct the bits from the switches. The Fibonacci recurrence yields the signed order-three recurrence by polynomial algebra. Comparing formal-series coefficients, with initial counts 4, 16 and 36, proves the generating-function identity.

## References

- Truth anchor: `D5/S1/Words/AdmissibleWords/HardinWidthTwoRecurrence.Avoids`
- Truth anchor: `D5/S1/Words/AdmissibleWords/HardinWidthTwoRecurrence.Forbidden`
- Truth anchor: `D5/S1/Words/AdmissibleWords/HardinWidthTwoRecurrence.StraightTriple`
- Truth anchor: `D5/S1/Words/AdmissibleWords/HardinWidthTwoRecurrence.a`
- Truth anchor: `D5/S1/Words/AdmissibleWords/HardinWidthTwoRecurrence.claim`
- Truth anchor: `D5/S1/Words/AdmissibleWords/HardinWidthTwoRecurrence.gf`
- Truth anchor: `D5/S1/Words/AdmissibleWords/HardinWidthTwoRecurrence.result`
- Dependency: [D5/S1/Words/AdmissibleWords/AdmissibleCount](AdmissibleCount.md)
