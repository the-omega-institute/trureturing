# An Alternating Stirling Identity for Fibonacci and Lucas Numbers

## Abstract

The alternating factorial-Stirling weighted sum of the even-index terms of a Fibonacci recurrence equals the signed weighted sum of the preceding Stirling row.

**Definition 1.1 (The Stirling row polynomial).**

$$(\operatorname{Q}\left(0\right) = 1) \land (\forall n \in \mathrm{Nat},\; \operatorname{Q}\left(n + 1\right) = X \cdot (1 + X) \cdot \operatorname{derivative}\left(\operatorname{Q}\left(n\right)\right) + X \cdot \operatorname{Q}\left(n\right))$$

*Formalization.* `D5/S3/Combinatorics/ParisseStirlingFibonacciAlternatingSum.Q` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Daniele Parisse (2024). *On Hypersequences of an Arbitrary Sequence and Their Weighted Sums*. DOI: [10.5281/zenodo.13331499](https://doi.org/10.5281/zenodo.13331499). URL: <https://math.colgate.edu/~integers/y70/y70.pdf>.

*Commentary.*

The source writes the Stirling numbers of the second kind for the number of partitions of a set into a prescribed number of nonempty blocks. Collecting a row of them with the factorials as weights gives the polynomial whose coefficient at an index is that index factorial times the Stirling number. The recurrence displayed here is what the Stirling recurrence becomes under that collection: multiplying an index by its coefficient is differentiation followed by multiplication by the variable, and lowering the second argument by one is multiplication by the variable. The polynomial of the zeroth row is the constant one. The polynomial itself is classical: it is the Fubini polynomial, also called the ordered Bell polynomial, whose value at one counts the ordered partitions of a set. What is set up here is its presentation by that differential recurrence, which is the form the later argument uses.

**Definition 1.2 (The pairing with a recurrence sequence).**

$$\forall u \in \mathrm{Nat} \to \mathbb{Z},\; \forall c \in \mathrm{Nat},\; \forall p \in \mathbb{Z}[X],\; \operatorname{L}\left(u, c, p\right) = \sum_{k\in \operatorname{support}\left(p\right)} (\operatorname{coeff}\left(p, k\right) \cdot \operatorname{u}\left(k + c\right))$$

*Formalization.* `D5/S3/Combinatorics/ParisseStirlingFibonacciAlternatingSum.L` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Daniele Parisse (2024). *On Hypersequences of an Arbitrary Sequence and Their Weighted Sums*. DOI: [10.5281/zenodo.13331499](https://doi.org/10.5281/zenodo.13331499). URL: <https://math.colgate.edu/~integers/y70/y70.pdf>.

*Commentary.*

A polynomial is paired with a sequence by summing each coefficient against the term of the sequence whose index is shifted by a fixed amount. Only the indices carrying a nonzero coefficient contribute, so the sum is finite. When the sequence obeys the Fibonacci recurrence this pairing turns multiplication of the polynomial by the variable into a shift of one, and multiplication by one plus the variable into a shift of two.

**Definition 1.3 (The Lucas numbers).**

$$(\operatorname{lucas}\left(0\right) = 2) \land ((\operatorname{lucas}\left(1\right) = 1) \land (\forall n \in \mathrm{Nat},\; \operatorname{lucas}\left(n + 2\right) = \operatorname{lucas}\left(n\right) + \operatorname{lucas}\left(n + 1\right)))$$

*Formalization.* `D5/S3/Combinatorics/ParisseStirlingFibonacciAlternatingSum.lucas` (`✓ std3`).

*Citation.* Daniele Parisse (2024). *On Hypersequences of an Arbitrary Sequence and Their Weighted Sums*. DOI: [10.5281/zenodo.13331499](https://doi.org/10.5281/zenodo.13331499). URL: <https://math.colgate.edu/~integers/y70/y70.pdf>.

*Commentary.*

The source writes the Lucas numbers with the values two and one at the first two indices, continuing by the Fibonacci recurrence. They are the second of the two sequences to which the source applies its formula for weighted sums.

**Definition 1.4 (The two conjectured identities).**

$$(claim) \Leftrightarrow ((\forall l \in \mathrm{Nat},\; \sum_{m=0}^{l} ((-1)^{m} \cdot (m)! \cdot \operatorname{S}\left(l + 1, m + 1\right) \cdot \operatorname{fib}\left(2 \cdot m + 2\right)) = (-1)^{l} \cdot \sum_{m=0}^{l} ((m)! \cdot \operatorname{S}\left(l, m\right) \cdot \operatorname{fib}\left(m + 2\right))) \land (\forall l \in \mathrm{Nat},\; \sum_{m=0}^{l} ((-1)^{m} \cdot (m)! \cdot \operatorname{S}\left(l + 1, m + 1\right) \cdot \operatorname{lucas}\left(2 \cdot m + 2\right)) = (-1)^{l} \cdot \sum_{m=0}^{l} ((m)! \cdot \operatorname{S}\left(l, m\right) \cdot \operatorname{lucas}\left(m + 2\right))))$$

*Formalization.* `D5/S3/Combinatorics/ParisseStirlingFibonacciAlternatingSum.claim` (`✓ std3`).

*Citation.* Daniele Parisse (2024). *On Hypersequences of an Arbitrary Sequence and Their Weighted Sums*. DOI: [10.5281/zenodo.13331499](https://doi.org/10.5281/zenodo.13331499). URL: <https://math.colgate.edu/~integers/y70/y70.pdf>.

*Commentary.*

Section 4 of the source states verbatim: "For all ell in N zero, the sum over m from zero to ell of minus one to the m times m factorial times the Stirling number of the second kind at ell plus one and m plus one times the Fibonacci number at twice m plus one equals minus one to the ell times the sum over m from zero to ell of m factorial times the Stirling number of the second kind at ell and m times the Fibonacci number at m plus two." The second statement is the same with the Lucas numbers in place of the Fibonacci numbers. Both arise as the constant term of the formula the source derives for the weighted sums of powers times Fibonacci and Lucas numbers, after the evaluation of its coefficients at zero. The source names the unsigned right-hand side of the first as the sequence A000557 and the negated right-hand side of the second as A263968; both sequence records carry the factorial-Stirling form, which settles the reading of the stacked bracket symbols.

**Theorem 1.5 (Both identities hold).**

$$claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ParisseStirlingFibonacciAlternatingSum.result` (`✓ std3`). ∎

*Resolves.* `Problems/parisse-stirling-fibonacci-alternating-sum` (proved) by `D5/S3/Combinatorics/ParisseStirlingFibonacciAlternatingSum.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"parisse-stirling-fibonacci-alternating-sum","declaration_gid":"D5/S3/Combinatorics/ParisseStirlingFibonacciAlternatingSum.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Daniele Parisse (2024). *On Hypersequences of an Arbitrary Sequence and Their Weighted Sums*. DOI: [10.5281/zenodo.13331499](https://doi.org/10.5281/zenodo.13331499). URL: <https://math.colgate.edu/~integers/y70/y70.pdf>.

*Commentary.*

Neither identity depends on the first two terms of the sequence, so both follow from one statement about an arbitrary integer sequence obeying the Fibonacci recurrence. Write the Stirling row polynomial for the row at hand. The recurrence for those polynomials yields, by induction, the functional equation asserting that the variable times the polynomial composed with minus one minus the variable equals minus one to the row index times one plus the variable times the polynomial; the induction step differentiates the previous instance and combines it with the composite of the recurrence in a single linear step. The pairing sends one plus the variable raised to a power to the term of the sequence at twice that power plus one, which is the doubling of the index under the binomial transform and again uses only the recurrence. On the other side, the Stirling recurrence rewrites the weight at each index as the sum of two neighbouring coefficients of the row polynomial; reindexing one of the two parts and cancelling the even-index terms against each other collapses the alternating sum to the pairing of the composite polynomial. The boundary term drops out because the row polynomial has no constant term once the row index is at least one, which also lets the variable be factored out and cancelled in the functional equation. What remains is the pairing shifted twice, which is the right-hand side. At row index zero both sides are the term of the sequence at index two.

## References

- Truth anchor: `D5/S3/Combinatorics/ParisseStirlingFibonacciAlternatingSum.L`
- Truth anchor: `D5/S3/Combinatorics/ParisseStirlingFibonacciAlternatingSum.Q`
- Truth anchor: `D5/S3/Combinatorics/ParisseStirlingFibonacciAlternatingSum.claim`
- Truth anchor: `D5/S3/Combinatorics/ParisseStirlingFibonacciAlternatingSum.lucas`
- Truth anchor: `D5/S3/Combinatorics/ParisseStirlingFibonacciAlternatingSum.result`
