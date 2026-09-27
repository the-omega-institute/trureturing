# Fibonacci Numbers That Are Pythagorean Perimeters

## Abstract

A Fibonacci number at an index that is not a multiple of six is the perimeter of a Pythagorean triangle, so the conjectured characterisation fails.

**Definition 1.1 (Being a Pythagorean perimeter).**

$$\forall N \in \mathrm{Nat},\; (\operatorname{IsPythPerimeter}\left(N\right)) \Leftrightarrow (\exists a \in \mathrm{Nat},\; \exists b \in \mathrm{Nat},\; \exists c \in \mathrm{Nat},\; (0 < a) \land ((0 < b) \land ((0 < c) \land ((a^{2} + b^{2} = c^{2}) \land (a + b + c = N)))))$$

*Formalization.* `D5/S3/Arith/FibonacciPythagoreanPerimeterRefutation.IsPythPerimeter` (`✓ std3`).

*Citation.* Felix Huber; Artur Jasinski (2023). *OEIS A134492, a(n) = Fibonacci(6*n)*. URL: <https://oeis.org/A134492>.

*Commentary.*

The source speaks of a number being the sum of the three numbers of a Pythagorean triple. The three numbers are the two legs and the hypotenuse, so their sum is the perimeter of the corresponding triangle. No qualifier appears in the source, so the triples range over all triples of positive integers satisfying the relation, primitive or not.

**Definition 1.2 (The conjectured characterisation).**

$$(claim) \Leftrightarrow (\forall N \in \mathrm{Nat},\; (\exists k \in \mathrm{Nat},\; \operatorname{fib}\left(k\right) = N) \Rightarrow ((\operatorname{IsPythPerimeter}\left(N\right)) \Leftrightarrow (\exists n \in \mathrm{Nat},\; (2 \le n) \land (\operatorname{fib}\left(6 \cdot n\right) = N))))$$

*Formalization.* `D5/S3/Arith/FibonacciPythagoreanPerimeterRefutation.claim` (`✓ std3`).

*Citation.* Felix Huber; Artur Jasinski (2023). *OEIS A134492, a(n) = Fibonacci(6*n)*. URL: <https://oeis.org/A134492>.

*Commentary.*

The comment on the sequence of Fibonacci numbers at indices divisible by six reads verbatim: "For n at least two, the terms of this sequence are exactly those Fibonacci numbers which are the sum of the three numbers of a Pythagorean triple (checked up to F of eighty)." Written out, the assertion is that a Fibonacci number is such a sum precisely when it is the value of the sequence at some index at least two.

**Theorem 1.3 (The characterisation fails).**

$$\neg (claim)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciPythagoreanPerimeterRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/fibonacci-pythagorean-perimeter-refutation` (refuted) by `D5/S3/Arith/FibonacciPythagoreanPerimeterRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"fibonacci-pythagorean-perimeter-refutation","declaration_gid":"D5/S3/Arith/FibonacciPythagoreanPerimeterRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Felix Huber; Artur Jasinski (2023). *OEIS A134492, a(n) = Fibonacci(6*n)*. URL: <https://oeis.org/A134492>.

*Commentary.*

Take the Fibonacci number at index forty-five, which is one billion one hundred thirty-four million nine hundred three thousand one hundred seventy. The three numbers three hundred forty-four million one hundred ninety-one thousand nine hundred forty-five, three hundred twenty million four hundred forty-three thousand two hundred forty-eight and four hundred seventy million two hundred sixty-seven thousand nine hundred seventy-seven satisfy the Pythagorean relation and add up to it, so it is a perimeter. It is not a term of the sequence: the terms jump from the Fibonacci number at index forty-two to the one at index forty-eight, and the Fibonacci function is monotone, so no index at least two can produce it. The witness was found by writing a perimeter as twice a product of three factors, two of them coprime with the larger between the smaller and its double and odd, and then testing the Fibonacci numbers at indices divisible by three; at the other indices they are odd and a perimeter is even. Index forty-five is the smallest failure, and it lies inside the range the comment reports having checked.

## References

- Truth anchor: `D5/S3/Arith/FibonacciPythagoreanPerimeterRefutation.IsPythPerimeter`
- Truth anchor: `D5/S3/Arith/FibonacciPythagoreanPerimeterRefutation.claim`
- Truth anchor: `D5/S3/Arith/FibonacciPythagoreanPerimeterRefutation.result`
