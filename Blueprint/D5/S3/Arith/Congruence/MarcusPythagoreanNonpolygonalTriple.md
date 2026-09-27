# Marcus's A344083 Pythagorean Triple Conjecture

## Abstract

The three-four-five triple is the unique positive Pythagorean triple whose sides all belong to A090467.

**Definition 1.1 (Polygonal numbers).**

$$\forall k \in \mathbb{N}, m \in \mathbb{N},\; \operatorname{polygonal}\left(k, m\right) = m + \left(k - 2\right) \cdot \operatorname{choose}\left(m, 2\right)$$

*Formalization.* `D5/S3/Arith/Congruence/MarcusPythagoreanNonpolygonalTriple.polygonal` (`✓ std3`).

*Citation.* Michel Marcus (2021). *OEIS A344083, a(n) = f(x)+f(y)+f(z), where (x,y,h) is the n-th Pythagorean triple listed in (A046083, A046084, A009000), and f(m)=A176775(m) is the index of m as k-gonal number for the smallest possible k*. URL: <https://oeis.org/A344083>.

*Commentary.*

All operations are in the natural numbers. The operator choose denotes Nat.choose, and subtraction is truncated. For k and m above two, this subtraction-free value equals 1+k*m*(m-1) div 2-(m-1)^2, where div is natural floor division; this is the formula printed in the definition of A090467.

**Definition 1.2 (The A090467 predicate).**

$$\forall n \in \mathbb{N},\; (\operatorname{nonpolygonal}\left(n\right)) \Leftrightarrow (\neg(\exists k \in \mathbb{N}, m \in \mathbb{N},\; (2 < k) \land ((2 < m) \land (n = \operatorname{polygonal}\left(k, m\right)))))$$

*Formalization.* `D5/S3/Arith/Congruence/MarcusPythagoreanNonpolygonalTriple.nonpolygonal` (`✓ std3`).

*Citation.* Michel Marcus (2021). *OEIS A344083, a(n) = f(x)+f(y)+f(z), where (x,y,h) is the n-th Pythagorean triple listed in (A046083, A046084, A009000), and f(m)=A176775(m) is the index of m as k-gonal number for the smallest possible k*. URL: <https://oeis.org/A344083>.

*Commentary.*

A natural number is nonpolygonal when it has no representation by the displayed polygonal formula with both the order and the index strictly greater than two.

**Definition 1.3 (Marcus's uniqueness conjecture).**

$$(claim) \Leftrightarrow (((\operatorname{nonpolygonal}\left(3\right)) \land ((\operatorname{nonpolygonal}\left(4\right)) \land ((\operatorname{nonpolygonal}\left(5\right)) \land (3^{2} + 4^{2} = 5^{2})))) \land (\forall x \in \mathbb{N}, y \in \mathbb{N}, z \in \mathbb{N},\; (0 < x) \Rightarrow ((0 < y) \Rightarrow ((x^{2} + y^{2} = z^{2}) \Rightarrow ((\operatorname{nonpolygonal}\left(x\right)) \Rightarrow ((\operatorname{nonpolygonal}\left(y\right)) \Rightarrow ((\operatorname{nonpolygonal}\left(z\right)) \Rightarrow ((\{x, y\} = \{3, 4\}) \land (z = 5)))))))))$$

*Formalization.* `D5/S3/Arith/Congruence/MarcusPythagoreanNonpolygonalTriple.claim` (`✓ std3`).

*Citation.* Michel Marcus (2021). *OEIS A344083, a(n) = f(x)+f(y)+f(z), where (x,y,h) is the n-th Pythagorean triple listed in (A046083, A046084, A009000), and f(m)=A176775(m) is the index of m as k-gonal number for the smallest possible k*. URL: <https://oeis.org/A344083>.

*Commentary.*

The sides three, four, and five are nonpolygonal and satisfy the Pythagorean equation. For any positive legs x and y satisfying that equation, if all three sides are nonpolygonal, then the unordered finset of legs is {3,4} and the hypotenuse is 5. The third nonpolygonal hypothesis is retained even though the uniqueness proof needs only the two leg hypotheses.

**Theorem 1.4 (The unique nonpolygonal Pythagorean triple).**

$$claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Congruence/MarcusPythagoreanNonpolygonalTriple.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a344083-marcus-pythagorean-nonpolygonal-triple` (proved) by `D5/S3/Arith/Congruence/MarcusPythagoreanNonpolygonalTriple.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a344083-marcus-pythagorean-nonpolygonal-triple","declaration_gid":"D5/S3/Arith/Congruence/MarcusPythagoreanNonpolygonalTriple.result","resolution_kind":"proved"} -->

*Citation.* Michel Marcus (2021). *OEIS A344083, a(n) = f(x)+f(y)+f(z), where (x,y,h) is the n-th Pythagorean triple listed in (A046083, A046084, A009000), and f(m)=A176775(m) is the index of m as k-gonal number for the smallest possible k*. URL: <https://oeis.org/A344083>.

*Commentary.*

Reduction modulo three shows that one leg is divisible by three. A positive nonpolygonal multiple of three must equal three, because every larger multiple 3t has the polygonal representation polygonal(t+1,3). The Pythagorean equation then bounds and determines the other leg and the hypotenuse as four and five.

## References

- Truth anchor: `D5/S3/Arith/Congruence/MarcusPythagoreanNonpolygonalTriple.claim`
- Truth anchor: `D5/S3/Arith/Congruence/MarcusPythagoreanNonpolygonalTriple.nonpolygonal`
- Truth anchor: `D5/S3/Arith/Congruence/MarcusPythagoreanNonpolygonalTriple.polygonal`
- Truth anchor: `D5/S3/Arith/Congruence/MarcusPythagoreanNonpolygonalTriple.result`
