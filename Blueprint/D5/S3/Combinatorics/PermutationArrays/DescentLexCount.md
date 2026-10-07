# Three-column permutation arrays with compatible row orders

## Abstract

Positive-length three-column permutation arrays have count 2+(n+1)(n+2)(n+3)/6.

**Theorem 1.1 (The count for every positive length).**

Lean statement: `D5/S3/Combinatorics/PermutationArrays/DescentLexCount.count_arrays`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PermutationArrays/DescentLexCount.count_arrays` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a222001-descent-lex-arrays` (proved) by `D5/S3/Combinatorics/PermutationArrays/DescentLexCount.count_arrays`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a222001-descent-lex-arrays","declaration_gid":"D5/S3/Combinatorics/PermutationArrays/DescentLexCount.count_arrays","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker (2013). *OEIS A222001, Number of n X 3 arrays with permutation rows and compatible descent and lexicographic orders*. URL: <https://oeis.org/A222001>.

*Commentary.*

A row is an actual permutation of Fin 3. Its entry in column j is the natural number (r j).val+1, so the source symbols are exactly 1,2,3. Adding one preserves strict comparisons, equality and non-strict comparisons. The descent count is the sum of the two indicators for entry 1 exceeding entry 2 and entry 2 exceeding entry 3. Lexicographic comparison tests the first entry, then the second, then the third.

The type Arrays n consists of functions from Fin n to these actual rows. The descent counts are nondecreasing along the original row indices, and the rows are lexicographically nonincreasing. Equal rows are allowed. For every n at least one, the cardinality is 2+(n+1)*(n+2)*(n+3)/6, where the division is exact natural division.

In increasing lexicographic order the rows are 123,132,213,231,312,321, with descent counts 0,1,1,1,1,2. Descents therefore cannot increase when a row decreases lexicographically. The two array conditions force the descent count to be constant. Descent classes zero and two contain only 123 and 321 respectively, giving exactly two constant arrays.

The middle class consists of all nonincreasing words on 132,213,231,312. Their multisets preserve every occurrence, including repetitions. Sorting a multiset in decreasing order reconstructs the unique word. The equivalence between actual arrays and the disjoint sum of two constants and length-n multisets is exhaustive in both directions. Mathlib's Sym cardinality theorem counts the multisets by choosing n from n+3. Binomial symmetry and the descending factorial identity give the displayed cubic.

Positive length distinguishes the two constant arrays. At length zero there is one empty array; the displayed formula would give three. The theorem explicitly assumes n at least one. The cited OEIS entry publishes the formula as a conjecture. This statement concerns that exact array count, without an assertion about publication priority or external acceptance.

## References

- Truth anchor: `D5/S3/Combinatorics/PermutationArrays/DescentLexCount.count_arrays`
