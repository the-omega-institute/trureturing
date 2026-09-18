# Antidiagonal Array and Source Series

## Abstract

The antidiagonal natural array and the normalized rational source series are uniquely determined, and their first-column coefficients agree after a one-step shift.

The array is the total natural function array from the A392095 recurrence: its zeroth row is one and each successor row uses the shifted entry and the finite sum over j from zero through k. The source is the normalized rational power series specified independently by F(x/F(x))=(1-x)^(-1). All coefficients are indexed from zero. The theorem result includes both uniqueness statements, the natural source sequence, and the shifted first-column identity.

**Remark 1.1 (The antidiagonal array).**

Lean statement: `D5/S1/Recurrence/Algebraic/AntidiagonalArraySourceSeries.array`

*Formalization.* `D5/S1/Recurrence/Algebraic/AntidiagonalArraySourceSeries.array` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The declaration array is the recursively constructed natural-valued two-index array. Its recursion is well founded by the lexicographic measure (n+k,n), with all finite-sum endpoints included.

**Remark 1.2 (The array predicate).**

Lean statement: `D5/S1/Recurrence/Algebraic/AntidiagonalArraySourceSeries.IsArray`

*Formalization.* `D5/S1/Recurrence/Algebraic/AntidiagonalArraySourceSeries.IsArray` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

IsArray(T) records the zeroth-row equation and the full successor recurrence for every natural n and k, using the finite range k+1.

**Remark 1.3 (The normalized source predicate).**

Lean statement: `D5/S1/Recurrence/Algebraic/AntidiagonalArraySourceSeries.IsSource`

*Formalization.* `D5/S1/Recurrence/Algebraic/AntidiagonalArraySourceSeries.IsSource` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

IsSource(F) requires constant coefficient one and the formal substitution equation F.subst(X times invOfUnit(F,1)) = invOfUnit(1-X,1).

**Remark 1.4 (The substitution operator).**

Lean statement: `D5/S1/Recurrence/Algebraic/AntidiagonalArraySourceSeries.phi`

*Formalization.* `D5/S1/Recurrence/Algebraic/AntidiagonalArraySourceSeries.phi` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

phi(F) is F.subst(X times invOfUnit(F,1)); it is defined without reference to the array.

**Remark 1.5 (Triangular source coefficients).**

Lean statement: `D5/S1/Recurrence/Algebraic/AntidiagonalArraySourceSeries.sourceCoeff`

*Formalization.* `D5/S1/Recurrence/Algebraic/AntidiagonalArraySourceSeries.sourceCoeff` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

sourceCoeff is the recursively defined rational coefficient function obtained by forcing each coefficient of phi to equal the corresponding coefficient of the geometric series.

**Remark 1.6 (The independent source series).**

Lean statement: `D5/S1/Recurrence/Algebraic/AntidiagonalArraySourceSeries.sourceSeries`

*Formalization.* `D5/S1/Recurrence/Algebraic/AntidiagonalArraySourceSeries.sourceSeries` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

sourceSeries is the power series whose coefficient at m is sourceCoeff(m).

**Theorem 1.7 (The complete array-source result).**

$$result$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Algebraic/AntidiagonalArraySourceSeries.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The result proves IsArray(array), uniqueness of every IsArray witness, IsSource(sourceSeries), uniqueness of every normalized source, existence and uniqueness of a natural source sequence, its zero coefficient, coefficient agreement with sourceSeries, and array(n,0)=b(n+1) for every natural n.

## References

- Truth anchor: `D5/S1/Recurrence/Algebraic/AntidiagonalArraySourceSeries.IsArray`
- Truth anchor: `D5/S1/Recurrence/Algebraic/AntidiagonalArraySourceSeries.IsSource`
- Truth anchor: `D5/S1/Recurrence/Algebraic/AntidiagonalArraySourceSeries.array`
- Truth anchor: `D5/S1/Recurrence/Algebraic/AntidiagonalArraySourceSeries.phi`
- Truth anchor: `D5/S1/Recurrence/Algebraic/AntidiagonalArraySourceSeries.result`
- Truth anchor: `D5/S1/Recurrence/Algebraic/AntidiagonalArraySourceSeries.sourceCoeff`
- Truth anchor: `D5/S1/Recurrence/Algebraic/AntidiagonalArraySourceSeries.sourceSeries`
