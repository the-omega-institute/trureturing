# Rational Interval Expression Certificates

## Abstract

Exact rational arithmetic checks provide proof inputs for real analytic covers.

**Definition 1.1 (Arithmetic expression with proposed endpoints).**

Lean statement: `D5/S0/Certificates/BoxCover/RationalIntervalExpression.Expr`

*Formalization.* `D5/S0/Certificates/BoxCover/RationalIntervalExpression.Expr` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The syntax stores rational annotations while the underlying expression retains real semantics.

**Definition 1.2 (Proposed rational bounds).**

Lean statement: `D5/S0/Certificates/BoxCover/RationalIntervalExpression.bounds`

*Formalization.* `D5/S0/Certificates/BoxCover/RationalIntervalExpression.bounds` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This projection has no truth authority by itself. The check validates it.

**Definition 1.3 (Real evaluation independent of annotations).**

Lean statement: `D5/S0/Certificates/BoxCover/RationalIntervalExpression.value`

*Formalization.* `D5/S0/Certificates/BoxCover/RationalIntervalExpression.value` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Evaluation discards every endpoint and applies the actual real field operations.

**Definition 1.4 (Exact local rational checks).**

Lean statement: `D5/S0/Certificates/BoxCover/RationalIntervalExpression.check`

*Formalization.* `D5/S0/Certificates/BoxCover/RationalIntervalExpression.check` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

All four multiplication corners, square sign cases and strict reciprocal guards are checked recursively.

**Theorem 1.5 (Successful checks enclose every real input).**

Lean statement: `D5/S0/Certificates/BoxCover/RationalIntervalExpression.checked_expression_encloses`

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/BoxCover/RationalIntervalExpression.checked_expression_encloses` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Structural induction proves a real enclosure from only exact rational local comparisons and membership in the input box. No enclosure oracle, external PASS or rational-only input restriction is assumed.

Application: positive-row population gain.

In Four-Path Full-Record Recovery Bound, Continuation IV, (51.5)–(51.6) and (51.11), put h = sqrt(1/2), c = sqrt((1+h)/2), s = sqrt((1-h)/2), k = c-h, and x = 1-xi/4+q/2. The positive-row gain is K = k² sqrt(1-q)/(8(hx+c)) + 2s sqrt(q)(1+x)/(3 sqrt(3)x). Here xi and q are real, with 21/10 ≤ xi ≤ 239/100. The field checker supplies the arithmetic enclosures between successive square roots; the root comparisons use Real.sq_sqrt and nonnegativity, separately from the field-expression language.

For h in [7/10,177/250], the accepted field expression (1+h)/2 has bounds [17/20,427/500], and (1-h)/2 has bounds [73/500,3/20]. These are the existing mul/add/input/neg constructors evaluated at the same h. The theorem checked_expression_encloses applies to this whole real interval. Comparing the endpoint squares then gives c in [92/100,93/100] and s in [191/500,39/100]. The initial bound on h follows from h ≥ 0 and h² = 1/2. Thus k ≥ 21/100, s ≥ 191/500, and 0 < sqrt(3) ≤ 1733/1000. Every square-root comparison has a nonnegative radicand and nonnegative proposed root endpoints.

Write v = sqrt(q) and a(v) = 19/40+v²/2. On 1/20 ≤ q ≤ 1/2, one has 0 < x < 1 and x ≤ a(v). For 0 ≤ t ≤ v ≤ 1, 0 ≤ r ≤ 13/10, and v ≤ r, set f(v) = v(1+a(v))-r a(v). Its difference is f(v)-f(t) = (v-t)[59/40+(v²+vt+t²-r(v+t))/2]. The bracket is at least 7/40: v², vt and t² are nonnegative and r(v+t) ≤ 2r ≤ 13/5. If r a(t) ≤ t(1+a(t)), this yields f(v) ≥ 0. Since r-v ≥ 0 and x ≤ a(v), it follows that r x ≤ v(1+x).

For q in [1/20,1/5], use (t,r) = (2/9,2/3); for [1/5,1/4], use (4/9,7/6); for [1/4,1/2], use (1/2,13/10). Squaring verifies t ≤ sqrt(q); the respective upper q bound gives sqrt(q) ≤ min(1,r). In each case the endpoint comparison r a(t) ≤ t(1+a(t)) is rational arithmetic. Positivity of x and the constant bounds therefore make the second summand of K at least (764/5199)r.

In the first range, x ≤ 23/40, hx+c ≤ 27/20, sqrt(1-q) ≥ 8/9 and k² ≥ 441/10000. Since hx+c > 0, these give the first summand at least 1/300. In the other ranges the first summand is nonnegative. Consequently K ≥ 1/10 for q in [1/20,1/5], K ≥ 17/100 for q in [1/5,1/4], and K ≥ 19/100 for q in [1/4,1/2], always with 21/10 ≤ xi ≤ 239/100. The final comparisons are respectively 1/300+(764/5199)(2/3) ≥ 1/10, (764/5199)(7/6) ≥ 17/100, and (764/5199)(13/10) ≥ 19/100. All intervals are closed, so the bounds include shared faces and corners. These are the continuous inequalities in rows P10–P12, obtained without sampled enclosures.

This application reuses the existing field soundness theorem and Mathlib square-root and ordered-field facts; it supplies no new named Lean theorem. It concerns only the scalar positive-row expression at the stated parameters. The selector of Theorem 37.5, selected root of Theorem 49.1, refinement (51.10), rows P1–P9 and P13–P14, population-cost relation T, native gain/transport bridge to one original effect and feedback, and equality classification are not established by these three bounds. No unrestricted quantum recovery minimum or physical realization follows from them.

## References

- Truth anchor: `D5/S0/Certificates/BoxCover/RationalIntervalExpression.Expr`
- Truth anchor: `D5/S0/Certificates/BoxCover/RationalIntervalExpression.bounds`
- Truth anchor: `D5/S0/Certificates/BoxCover/RationalIntervalExpression.check`
- Truth anchor: `D5/S0/Certificates/BoxCover/RationalIntervalExpression.checked_expression_encloses`
- Truth anchor: `D5/S0/Certificates/BoxCover/RationalIntervalExpression.value`
