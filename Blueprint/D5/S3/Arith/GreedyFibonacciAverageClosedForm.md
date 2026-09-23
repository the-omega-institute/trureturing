# A Closed Form for the Greedy Fibonacci-Average Sequence

## Abstract

The greedy sequence whose running averages are Fibonacci takes the conjectured closed form from the tenth term onwards.

**Definition 1.1 (Being a Fibonacci number).**

$$\forall k \in \mathrm{Nat},\; (\operatorname{IsFib}\left(k\right)) \Leftrightarrow (\exists m \in \mathrm{Nat},\; \operatorname{fib}\left(m\right) = k)$$

*Formalization.* `D5/S3/Arith/GreedyFibonacciAverageClosedForm.IsFib` (`✓ std3`).

*Citation.* Sela Fried (2025). *Proofs of Several Conjectures From the OEIS*. URL: <https://cs.uwaterloo.ca/journals/JIS/VOL28/Fried/fried15.pdf>.

*Commentary.*

The source speaks of a number being a Fibonacci number; that is the property displayed here. It is decidable, because an index whose Fibonacci value is a given number is at most that number plus one.

**Definition 1.2 (An admissible next value).**

$$\forall L \in \operatorname{List}\left(\mathrm{Nat}\right),\; \forall n \in \mathrm{Nat},\; \forall v \in \mathrm{Nat},\; (\operatorname{Good}\left(L, n, v\right)) \Leftrightarrow ((0 < v) \land ((\neg (v \in L)) \land ((n \mid \operatorname{sum}\left(L\right) + v) \land (\operatorname{IsFib}\left(\operatorname{div}\left(\operatorname{sum}\left(L\right) + v, n\right)\right)))))$$

*Formalization.* `D5/S3/Arith/GreedyFibonacciAverageClosedForm.Good` (`✓ std3`).

*Citation.* Sela Fried (2025). *Proofs of Several Conjectures From the OEIS*. URL: <https://cs.uwaterloo.ca/journals/JIS/VOL28/Fried/fried15.pdf>.

*Commentary.*

The source builds its sequence from distinct least positive numbers whose running averages are Fibonacci numbers. After the first terms have been written down, a candidate is admissible exactly when it is positive, has not been used, and makes the average of the terms written so far together with it a Fibonacci number. The average is expressed as divisibility of the new total by the number of terms together with the quotient being a Fibonacci number.

**Theorem 1.3 (Some value is always admissible).**

$$\forall L \in \operatorname{List}\left(\mathrm{Nat}\right),\; \forall n \in \mathrm{Nat},\; (0 < n) \Rightarrow (\exists v \in \mathrm{Nat},\; \operatorname{Good}\left(L, n, v\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GreedyFibonacciAverageClosedForm.good_exists` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Taking the index twice the current total plus two gives a Fibonacci number larger than that total, so the difference is positive, exceeds every term already written, and leaves the required quotient. The greedy rule therefore never stalls and the sequence is defined at every index.

**Definition 1.4 (The greedy value).**

$$\forall L \in \operatorname{List}\left(\mathrm{Nat}\right),\; \forall n \in \mathrm{Nat},\; (0 < n) \Rightarrow (\operatorname{nextVal}\left(L, n\right) = \operatorname{min}\left(\{v: \mathrm{Nat} \mid \operatorname{Good}\left(L, n, v\right)\}\right))$$

*Formalization.* `D5/S3/Arith/GreedyFibonacciAverageClosedForm.nextVal` (`✓ std3`).

*Citation.* Sela Fried (2025). *Proofs of Several Conjectures From the OEIS*. URL: <https://cs.uwaterloo.ca/journals/JIS/VOL28/Fried/fried15.pdf>.

*Commentary.*

The least admissible value, which exists by the previous statement. The word least is the one the source uses.

**Definition 1.5 (The terms written so far).**

$$\forall n \in \mathrm{Nat},\; \operatorname{hist}\left(0\right) = []   \operatorname{hist}\left(n + 1\right) = \operatorname{append}\left(\operatorname{hist}\left(n\right), [\operatorname{nextVal}\left(\operatorname{hist}\left(n\right), n + 1\right)]\right)$$

*Formalization.* `D5/S3/Arith/GreedyFibonacciAverageClosedForm.hist` (`✓ std3`).

*Citation.* Sela Fried (2025). *Proofs of Several Conjectures From the OEIS*. URL: <https://cs.uwaterloo.ca/journals/JIS/VOL28/Fried/fried15.pdf>.

*Commentary.*

The list of the first terms, extended one term at a time by the greedy value for the next index.

**Definition 1.6 (The sequence itself).**

$$\forall n \in \mathrm{Nat},\; \operatorname{a}\left(n\right) = \operatorname{nextVal}\left(\operatorname{hist}\left(n - 1\right), n\right)$$

*Formalization.* `D5/S3/Arith/GreedyFibonacciAverageClosedForm.a` (`✓ std3`).

*Citation.* Sela Fried (2025). *Proofs of Several Conjectures From the OEIS*. URL: <https://cs.uwaterloo.ca/journals/JIS/VOL28/Fried/fried15.pdf>.

*Commentary.*

The source writes this sequence with subscripts from one. Its entry at an index is the greedy value taken after the preceding terms.

**Definition 1.7 (The value at an even index).**

$$\forall j \in \mathrm{Nat},\; \operatorname{X}\left(j\right) = \operatorname{fib}\left(j + 2\right) + 2 \cdot j \cdot \operatorname{fib}\left(j + 1\right)$$

*Formalization.* `D5/S3/Arith/GreedyFibonacciAverageClosedForm.X` (`✓ std3`).

*Citation.* Sela Fried (2025). *Proofs of Several Conjectures From the OEIS*. URL: <https://cs.uwaterloo.ca/journals/JIS/VOL28/Fried/fried15.pdf>.

*Commentary.*

The source displays the even case of its closed form as the index times the Fibonacci number three beyond half the index, less one below the index times the Fibonacci number two beyond half the index. Expanding the Fibonacci recurrence once turns that into the expression displayed here, which involves no subtraction.

**Definition 1.8 (The first ten terms).**

$$base10 = [1, 3, 2, 6, 13, 5, 26, 8, 53, 93]$$

*Formalization.* `D5/S3/Arith/GreedyFibonacciAverageClosedForm.base10` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The terms the greedy rule produces before the closed form takes over. The source states its closed form from the tenth term onwards, and these are the values below that point together with the tenth.

**Definition 1.9 (The terms from the eleventh onwards).**

$$\forall k \in \mathrm{Nat},\; \operatorname{tailList}\left(0\right) = []   \operatorname{tailList}\left(k + 1\right) = \operatorname{append}\left(\operatorname{tailList}\left(k\right), [\operatorname{fib}\left(k + 8\right), \operatorname{X}\left(k + 6\right)]\right)$$

*Formalization.* `D5/S3/Arith/GreedyFibonacciAverageClosedForm.tailList` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

From the eleventh term the values come in pairs: a Fibonacci number at an odd index, then the even-index value at the next one.

**Definition 1.10 (The conjectured closed form).**

$$(claim) \Leftrightarrow (\forall n \in \mathrm{Nat},\; (10 \le n) \Rightarrow (((\operatorname{mod}\left(n, 2\right) = 0) \Rightarrow (\operatorname{a}\left(n\right) + \left(n - 1\right) \cdot \operatorname{fib}\left(\operatorname{div}\left(n, 2\right) + 2\right) = n \cdot \operatorname{fib}\left(\operatorname{div}\left(n, 2\right) + 3\right))) \land ((\operatorname{mod}\left(n, 2\right) = 1) \Rightarrow (\operatorname{a}\left(n\right) = \operatorname{fib}\left(\operatorname{div}\left(n + 1, 2\right) + 2\right)))))$$

*Formalization.* `D5/S3/Arith/GreedyFibonacciAverageClosedForm.claim` (`✓ std3`).

*Citation.* Sela Fried (2025). *Proofs of Several Conjectures From the OEIS*. URL: <https://cs.uwaterloo.ca/journals/JIS/VOL28/Fried/fried15.pdf>.

*Commentary.*

Section 6 of the source reads verbatim: "Refining the conjecture stated in A248982 regarding a closed-form formula, it seems that, for n at least ten, we have a n equals n times F of n over two plus three minus n minus one times F of n over two plus two if n is even, and F of n plus one over two plus two otherwise." The even case is displayed here additively so that no truncated subtraction occurs. The sequence entry carries two further standing conjectures, an order eight linear recurrence beyond the seventeenth term and the identification of the odd-index terms with Fibonacci numbers; both follow from the displayed form.

**Theorem 1.11 (The closed form holds).**

$$claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GreedyFibonacciAverageClosedForm.result` (`✓ std3`). ∎

*Resolves.* `Problems/greedy-fibonacci-average-closed-form` (proved) by `D5/S3/Arith/GreedyFibonacciAverageClosedForm.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"greedy-fibonacci-average-closed-form","declaration_gid":"D5/S3/Arith/GreedyFibonacciAverageClosedForm.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Commentary.*

Write S for the total of the terms written so far. The argument is a two step induction on the claim that after an even index twice j the total is twice j times the Fibonacci number three beyond j, and after the next index it is one more than twice j times that same Fibonacci number. The base is the tenth term, where the total is two hundred ten. At an odd index the least admissible Fibonacci average is the one three beyond j, because a smaller one would not raise the total; the resulting value is that Fibonacci number itself. At the following even index the same Fibonacci average would repeat the value just used, so the rule moves to the next one and the value is the even-index expression. What separates the two families is that no even-index value is a Fibonacci number, which is the frozen statement this module depends on. The remaining exclusions are inequalities between consecutive Fibonacci numbers, together with the observation that the even-index values increase and that the first nine terms are all below both families from the tenth onwards.

## References

- Truth anchor: `D5/S3/Arith/GreedyFibonacciAverageClosedForm.Good`
- Truth anchor: `D5/S3/Arith/GreedyFibonacciAverageClosedForm.IsFib`
- Truth anchor: `D5/S3/Arith/GreedyFibonacciAverageClosedForm.X`
- Truth anchor: `D5/S3/Arith/GreedyFibonacciAverageClosedForm.a`
- Truth anchor: `D5/S3/Arith/GreedyFibonacciAverageClosedForm.base10`
- Truth anchor: `D5/S3/Arith/GreedyFibonacciAverageClosedForm.claim`
- Truth anchor: `D5/S3/Arith/GreedyFibonacciAverageClosedForm.good_exists`
- Truth anchor: `D5/S3/Arith/GreedyFibonacciAverageClosedForm.hist`
- Truth anchor: `D5/S3/Arith/GreedyFibonacciAverageClosedForm.nextVal`
- Truth anchor: `D5/S3/Arith/GreedyFibonacciAverageClosedForm.result`
- Truth anchor: `D5/S3/Arith/GreedyFibonacciAverageClosedForm.tailList`
- Dependency: [D5/S3/Arith/FriedFibonacciShiftNonFibonacci](FriedFibonacciShiftNonFibonacci.md)
