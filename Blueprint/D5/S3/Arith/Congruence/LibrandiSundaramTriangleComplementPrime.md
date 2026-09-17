# Librandi's Sundaram-Type Triangle Complement

## Abstract

Librandi's triangle complement maps every outside value to a prime 4h+5.

**Definition 1.1 (The triangle row formula).**

$$\forall m \in {\mathbb N}, n \in {\mathbb N},\; T\left(m, n\right) = \left\lfloor\frac{2 \cdot m \cdot n + m + n - 2}{2}\right\rfloor$$

*Formalization.* `D5/S3/Arith/Congruence/LibrandiSundaramTriangleComplementPrime.T` (`✓ std3`).

*Citation.* Vincenzo Librandi (2012). *OEIS A140869, Triangle read by rows where T(m,n) = floor((2mn+m+n-2)/2), m >= n >= 1*. URL: <https://oeis.org/A140869>.

*Commentary.*

For natural m and n, T is the displayed natural-number quotient. The subtraction and division are literal truncated natural operations; on m >= n >= 1 the numerator is at least two, so the formula has its intended value.

**Definition 1.2 (Membership in the triangle).**

$$\forall h \in {\mathbb N},\; InTriangle\left(h\right) \Leftrightarrow (\exists m \in {\mathbb N}, n \in {\mathbb N},\; 1 \le n \land \left(n \le m \land T\left(m, n\right) = h\right))$$

*Formalization.* `D5/S3/Arith/Congruence/LibrandiSundaramTriangleComplementPrime.InTriangle` (`✓ std3`).

*Citation.* Vincenzo Librandi (2012). *OEIS A140869, Triangle read by rows where T(m,n) = floor((2mn+m+n-2)/2), m >= n >= 1*. URL: <https://oeis.org/A140869>.

*Commentary.*

A natural h belongs to the triangle exactly when it is T(m,n) for natural coordinates with 1 <= n <= m.

**Theorem 1.3 (The complement-prime theorem).**

$$\forall h \in {\mathbb N},\; \left(\neg InTriangle\left(h\right)\right) \Rightarrow Prime\left(4 \cdot h + 5\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Congruence/LibrandiSundaramTriangleComplementPrime.librandi_a140869` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a140869-sundaram-triangle-complement-prime` (proved) by `D5/S3/Arith/Congruence/LibrandiSundaramTriangleComplementPrime.librandi_a140869`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a140869-sundaram-triangle-complement-prime","declaration_gid":"D5/S3/Arith/Congruence/LibrandiSundaramTriangleComplementPrime.librandi_a140869","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Commentary.*

Assume that 4h+5 is composite. A nontrivial divisor supplied by the factorization theorem gives two odd factors. Writing them as 2a+1 and 2b+1, ordering the half-factors, and normalizing their product identity produces T(a,b)=h, a contradiction. The converse is false at h = 2, 8, and 12.

## References

- Truth anchor: `D5/S3/Arith/Congruence/LibrandiSundaramTriangleComplementPrime.InTriangle`
- Truth anchor: `D5/S3/Arith/Congruence/LibrandiSundaramTriangleComplementPrime.T`
- Truth anchor: `D5/S3/Arith/Congruence/LibrandiSundaramTriangleComplementPrime.librandi_a140869`
