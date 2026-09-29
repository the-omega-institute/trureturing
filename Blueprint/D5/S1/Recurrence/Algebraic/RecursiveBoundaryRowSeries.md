# Recursive Arrays from Arbitrary Boundaries

## Abstract

Every boundary sequence over a commutative ring determines a unique recursive array whose rows have exact formal composition and finite coefficient formulas.

Let R be a commutative ring and a a sequence indexed by the natural numbers. All indices start at zero. The first column is T(n,0)=a(n), and the successor rule is T(n,k+1)=T(n+1,k)-sum over 0<=j<=k of T(n,j)a(k-j). This constructs each column from earlier columns. The boundary entries may vanish, and the zeroth row is unrestricted. The coefficient ring can in particular be the rationals or the complex numbers.

**Definition 1.1 (The recursive array).**

Lean statement: `D5/S1/Recurrence/Algebraic/RecursiveBoundaryRowSeries.array`

*Formalization.* `D5/S1/Recurrence/Algebraic/RecursiveBoundaryRowSeries.array` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

array(a,n,k) is defined by the boundary at k=0 and the successor rule at k+1. The recursive calls have strictly smaller column index. The finite index type Fin(k+1) includes both endpoints j=0 and j=k.

**Definition 1.2 (The boundary and recurrence equations).**

Lean statement: `D5/S1/Recurrence/Algebraic/RecursiveBoundaryRowSeries.IsExtension`

*Formalization.* `D5/S1/Recurrence/Algebraic/RecursiveBoundaryRowSeries.IsExtension` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

IsExtension(a,T) asserts that T has first column a and satisfies the successor rule at every pair of natural indices. Replacing a(k-j) by T(k-j,0) and moving the sum to the other side gives the equivalent row-successor equation.

**Definition 1.3 (An actual row series).**

Lean statement: `D5/S1/Recurrence/Algebraic/RecursiveBoundaryRowSeries.row`

*Formalization.* `D5/S1/Recurrence/Algebraic/RecursiveBoundaryRowSeries.row` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

row(T,n) has coefficient T(n,k) at degree k. It is the generating series of the given array, defined independently of the composition formula.

**Definition 1.4 (The normalized boundary series).**

Lean statement: `D5/S1/Recurrence/Algebraic/RecursiveBoundaryRowSeries.source`

*Formalization.* `D5/S1/Recurrence/Algebraic/RecursiveBoundaryRowSeries.source` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

source(a)=1+X*mk(a), where mk(a) has coefficient a(k) at degree k. Thus the constant coefficient of source(a) is one for every a.

**Definition 1.5 (The formal reciprocal).**

Lean statement: `D5/S1/Recurrence/Algebraic/RecursiveBoundaryRowSeries.reciprocal`

*Formalization.* `D5/S1/Recurrence/Algebraic/RecursiveBoundaryRowSeries.reciprocal` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

reciprocal(a)=invOfUnit(source(a),1) is the two-sided multiplicative inverse of source(a). The inverse uses its unit constant coefficient and is defined over an arbitrary commutative ring.

**Definition 1.6 (The substitution series).**

Lean statement: `D5/S1/Recurrence/Algebraic/RecursiveBoundaryRowSeries.inner`

*Formalization.* `D5/S1/Recurrence/Algebraic/RecursiveBoundaryRowSeries.inner` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

inner(a)=X*reciprocal(a) has constant coefficient zero. Substitution of this series into an arbitrary outer formal series is therefore defined.

**Definition 1.7 (A shifted boundary series).**

Lean statement: `D5/S1/Recurrence/Algebraic/RecursiveBoundaryRowSeries.tail`

*Formalization.* `D5/S1/Recurrence/Algebraic/RecursiveBoundaryRowSeries.tail` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

tail(a,n) has coefficient a(n+j) at degree j. The starting row n is arbitrary.

**Theorem 1.8 (Unique extension and exact row formulas).**

Lean statement: `D5/S1/Recurrence/Algebraic/RecursiveBoundaryRowSeries.result`

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Algebraic/RecursiveBoundaryRowSeries.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every a, array(a) satisfies IsExtension(a), and every other extension equals it. Write I=reciprocal(a), Y=inner(a), and R(n)=row(array(a),n). For every n and N, R(n)=I*sum over 0<=j<N of C(a(n+j))*Y^j +Y^N*R(n+N), where C embeds a coefficient as a constant series. The remainder is divisible by X^N, including N=0. Consequently R(n)=I*tail(a,n).subst(Y), where subst means formal composition, and array(a,n,k)=sum over 0<=j<=k of a(n+j)*coeff(k-j)(I^(j+1)). Uniqueness gives the same two formulas for any array with the stated boundary and recurrence. To prove the identities, coefficient convolution first gives source(a)*R(n)=C(a(n))+X*R(n+1). Finite iteration yields the expansion. At degree k, taking N=k+1 makes the remainder coefficient zero. All identities concern formal coefficients and require no analytic convergence.

## References

- Truth anchor: `D5/S1/Recurrence/Algebraic/RecursiveBoundaryRowSeries.IsExtension`
- Truth anchor: `D5/S1/Recurrence/Algebraic/RecursiveBoundaryRowSeries.array`
- Truth anchor: `D5/S1/Recurrence/Algebraic/RecursiveBoundaryRowSeries.inner`
- Truth anchor: `D5/S1/Recurrence/Algebraic/RecursiveBoundaryRowSeries.reciprocal`
- Truth anchor: `D5/S1/Recurrence/Algebraic/RecursiveBoundaryRowSeries.result`
- Truth anchor: `D5/S1/Recurrence/Algebraic/RecursiveBoundaryRowSeries.row`
- Truth anchor: `D5/S1/Recurrence/Algebraic/RecursiveBoundaryRowSeries.source`
- Truth anchor: `D5/S1/Recurrence/Algebraic/RecursiveBoundaryRowSeries.tail`
