# Kagey's Binary Null Polynomial Recurrence

## Abstract

Binary integer polynomials of each positive degree that vanish modulo three at every integer satisfy Kagey's order-eight counting recurrence. Coefficient words identify the count with a nine-state transfer column; an exact column identity propagates through every matrix power.

**Definition 1.1 (The polynomial count).**

$$\forall (n: \mathrm{Nat}), a (n) = \operatorname{Nat}.\operatorname{card} (\{f: Polynomial (\mathrm{Int}) // (\operatorname{Polynomial}.\operatorname{natDegree} (f) = n) \land ((\operatorname{Polynomial}.\operatorname{Monic} (f)) \land ((\forall (i: \mathrm{Nat}), \operatorname{Polynomial}.\operatorname{coeff} (f) (i) = 0 \lor \operatorname{Polynomial}.\operatorname{coeff} (f) (i) = 1) \land (\forall (k: \mathrm{Int}), (3: \mathrm{Int}) \mid \operatorname{Polynomial}.\operatorname{eval} (k) (f))))\})$$

*Formalization.* `D5/S3/Combinatorics/BinaryNullPolynomials/KageyA329479Recurrence.a` (`✓ std3`).

*Citation.* Peter Kagey (2019). *OEIS A329479: Binary null polynomials modulo three*. URL: <https://oeis.org/A329479/internal>.

*Commentary.*

OEIS A329479, revision 25, NAME (unpaginated): "Number of degree n polynomials f with all nonzero coefficients equal to 1 such that f(k) is divisible by 3 for all integers k." The carrier is Polynomial Int, so distinct integer polynomials are counted separately. Degree is exactly n, monicness forces the leading coefficient to be one, and every coefficient is zero or one. The degree-seven example fixes the degree interpretation despite the entry's different string-length wording.

**Definition 1.2 (The conjectured recurrence).**

$$claim \Leftrightarrow (\forall (n: \mathrm{Nat}), 9 \le n \Rightarrow (a (n): \mathrm{Int}) = 2 \cdot (a (n - 1): \mathrm{Int}) + 2 \cdot (a (n - 2): \mathrm{Int}) - 5 \cdot (a (n - 3): \mathrm{Int}) - 2 \cdot (a (n - 4): \mathrm{Int}) + 10 \cdot (a (n - 5): \mathrm{Int}) - 4 \cdot (a (n - 6): \mathrm{Int}) - 4 \cdot (a (n - 7): \mathrm{Int}) + 8 \cdot (a (n - 8): \mathrm{Int}))$$

*Formalization.* `D5/S3/Combinatorics/BinaryNullPolynomials/KageyA329479Recurrence.claim` (`✓ std3`).

*Citation.* Peter Kagey (2019). *OEIS A329479: Binary null polynomials modulo three*. URL: <https://oeis.org/A329479/internal>.

*Commentary.*

OEIS A329479, revision 25, final FORMULA line (unpaginated): "Conjectured recurrence: a(n) = 2a(n-1) + 2a(n-2) - 5a(n-3) - 2a(n-4) + 10a(n-5) - 4a(n-6) - 4a(n-7) + 8a(n-8)." The offset is one, so nine is the first argument whose eight predecessors are all in the sequence. Indices use natural subtraction; counts are cast to Int before the additions, multiplications and subtractions.

**Theorem 1.3 (The recurrence holds).**

$$\forall (n: \mathrm{Nat}), 9 \le n \Rightarrow (a (n): \mathrm{Int}) = 2 \cdot (a (n - 1): \mathrm{Int}) + 2 \cdot (a (n - 2): \mathrm{Int}) - 5 \cdot (a (n - 3): \mathrm{Int}) - 2 \cdot (a (n - 4): \mathrm{Int}) + 10 \cdot (a (n - 5): \mathrm{Int}) - 4 \cdot (a (n - 6): \mathrm{Int}) - 4 \cdot (a (n - 7): \mathrm{Int}) + 8 \cdot (a (n - 8): \mathrm{Int})$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/BinaryNullPolynomials/KageyA329479Recurrence.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Peter Kagey (2019). *OEIS A329479: Binary null polynomials modulo three*. URL: <https://oeis.org/A329479/internal>.

*Commentary.*

Evaluation at zero forces the constant coefficient to vanish. A polynomial of degree n plus one is recovered uniquely from its n interior Boolean coefficients and its leading one. Over ZMod 3 its remaining null condition is simultaneous vanishing at one and minus one. Prepending a Boolean coefficient changes the two evaluations by affine maps on ZMod 3 times ZMod 3. The labelled-word transfer identity equates the polynomial count to the column ending at the evaluation pair of X. Direct arithmetic verifies the degree-eight identity at all nine starting states. The transition is linear, so induction propagates that identity to every power. The coefficient-word correspondence then gives the claimed recurrence.

## References

- Truth anchor: `D5/S3/Combinatorics/BinaryNullPolynomials/KageyA329479Recurrence.a`
- Truth anchor: `D5/S3/Combinatorics/BinaryNullPolynomials/KageyA329479Recurrence.claim`
- Truth anchor: `D5/S3/Combinatorics/BinaryNullPolynomials/KageyA329479Recurrence.result`
- Dependency: [D5/S0/Computability/BinaryMachine/TapeToStacks](../../../S0/Computability/BinaryMachine/TapeToStacks.md)
- Dependency: [D5/S3/Combinatorics/NarayanaStrip/CiglerCycleWalkTransfer](../NarayanaStrip/CiglerCycleWalkTransfer.md)
