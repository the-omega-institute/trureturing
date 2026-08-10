# The Normalized Beta Deficit Is Three-Valued

## Abstract

The normalized beta deficit of golden addition takes only the values -1, 0, and 1.

**Theorem 1.1 (The normalized beta deficit takes only the values -1, 0, and 1).**

$$c(v_1,v_2) = \beta'(v_1) + \beta'(v_2) - \beta'(v_1+v_2) \in \{-1, 0, +1\}$$

*Proof.* Machine-checked in Lean as `D5/S1/Deficit/DeficitThreeValued.deficit_three_valued` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The deficit of golden addition is the failure of the model-set value of canonical Zeckendorf digits to be additive across a sum: the value of the first operand plus the value of the second minus the value of the sum. The integer theorem of this bucket already records that this deficit is a rational integer equal to the signed count of bottom carries fired during normalization. This theorem closes the remaining quantitative question: the integer is never anything other than minus one, zero, or plus one. However large the operands and however long the carry chain, the net hidden account of normalization is at most a single unit.

The proof intersects the integer certificate with a window bound on the contraction face. Read on that face, each operand evaluates its Zeckendorf indices at powers of the golden conjugate, whose exponents are at least two. Splitting into even and odd exponents dominates the positive part by the geometric series of the squared conjugate starting at its square and the negative part by the same series starting at its cube, so every reading lands in the window from minus the inverse square of the golden ratio to the inverse of the golden ratio. Three window readings place the deficit strictly between minus two and two, and the final numeric gates reduce to the golden conjugate being negative and the golden ratio being less than two: the window of length exactly one admits precisely three integers.

## References

- Truth anchor: `D5/S1/Deficit/DeficitThreeValued.deficit_three_valued`
- Dependency: [D5/S1/Deficit/DeficitInteger](DeficitInteger.md)
