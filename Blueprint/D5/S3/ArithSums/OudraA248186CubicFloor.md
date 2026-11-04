# Oudra's formula for A248186

## Abstract

Oudra's cubic floor formula for the least reciprocal-product threshold index.

**Definition 1.1 (The finite-sum residual).**

$$\forall k \in \mathrm{Nat},\; \operatorname{residual}\left(k\right) = \frac{1}{18} - \sum_{h \in \operatorname{Finset.Icc}\left(1, k\right)} \frac{1}{(h : \mathrm{Real}) \cdot ((h : \mathrm{Real}) + 1) \cdot ((h : \mathrm{Real}) + 2) \cdot ((h : \mathrm{Real}) + 3)}$$

*Formalization.* `D5/S3/ArithSums/OudraA248186CubicFloor.residual` (`✓ std3`).

*Citation.* Clark Kimberling; Ridouane Oudra (2023). *OEIS A248186, least reciprocal-product threshold index*. URL: <https://oeis.org/A248186/internal>.

*Commentary.*

OEIS A248186 revision 18, NAME (%N; unpaginated): Least k such that 1/18 - Sum_{h=1..k} 1/(h*(h+1)*(h+2)*(h+3)) < 1/n^3. The sum runs over natural h from 1 through k, including both endpoints; all summands and the subtraction are real-valued. At k=0 the sum is empty.

**Definition 1.2 (The real cubic-root constant).**

$$r = (3 : \mathrm{Real})^{\frac{-(1 : \mathrm{Real})}{3}}$$

*Formalization.* `D5/S3/ArithSums/OudraA248186CubicFloor.r` (`✓ std3`).

*Citation.* Clark Kimberling; Ridouane Oudra (2023). *OEIS A248186, least reciprocal-product threshold index*. URL: <https://oeis.org/A248186/internal>.

*Commentary.*

OEIS A248186 revision 18, FORMULA (%F; unpaginated): Conjecture: a(n) = floor(r*n + r^2/n - 1), where r = 3^(-1/3), for n > 2. - _Ridouane Oudra_, Oct 06 2023 The fixed positive base 3 is raised to the real exponent -1/3.

**Definition 1.3 (The least positive threshold sequence).**

$$\forall A \in (\mathrm{Nat} \to \mathrm{Nat}),\; (\operatorname{IsSourceSequence}\left(A\right)) \Leftrightarrow (\forall n \in \mathrm{Nat},\; (1 \le n) \Rightarrow (\operatorname{IsLeast}\left(\{k : \mathrm{Nat} \mid (1 \le k) \land (\operatorname{residual}\left(k\right) < \frac{1}{(n : \mathrm{Real})^{3}})\}, A\left(n\right)\right)))$$

*Formalization.* `D5/S3/ArithSums/OudraA248186CubicFloor.IsSourceSequence` (`✓ std3`).

*Citation.* Clark Kimberling; Ridouane Oudra (2023). *OEIS A248186, least reciprocal-product threshold index*. URL: <https://oeis.org/A248186/internal>.

*Commentary.*

OEIS A248186 revision 18, NAME (%N; unpaginated): Least k such that 1/18 - Sum_{h=1..k} 1/(h*(h+1)*(h+2)*(h+3)) < 1/n^3. The source program searches Range[z], hence positive k. The offset is 1,5; n ranges over positive natural numbers, and A(0) is unconstrained. IsLeast requires both membership and minimality; the comparison is strict. The initial values are a(1)=a(2)=1.

**Definition 1.4 (The source assertion with sequence existence).**

$$(claim) \Leftrightarrow ((\exists A \in (\mathrm{Nat} \to \mathrm{Nat}),\; \operatorname{IsSourceSequence}\left(A\right)) \land (\forall A \in (\mathrm{Nat} \to \mathrm{Nat}),\; (\operatorname{IsSourceSequence}\left(A\right)) \Rightarrow (\forall n \in \mathrm{Nat},\; (2 < n) \Rightarrow ((A\left(n\right) : \mathrm{Int}) = \lfloor r \cdot (n : \mathrm{Real}) + \frac{r^{2}}{(n : \mathrm{Real})} - 1 \rfloor))))$$

*Formalization.* `D5/S3/ArithSums/OudraA248186CubicFloor.claim` (`✓ std3`).

*Citation.* Clark Kimberling; Ridouane Oudra (2023). *OEIS A248186, least reciprocal-product threshold index*. URL: <https://oeis.org/A248186/internal>.

*Commentary.*

OEIS A248186 revision 18, FORMULA (%F; unpaginated): Conjecture: a(n) = floor(r*n + r^2/n - 1), where r = 3^(-1/3), for n > 2. - _Ridouane Oudra_, Oct 06 2023 A is natural-valued. Its term is cast into the integers before comparison with Int.floor; n is cast into the reals in the formula. Existence is asserted for all positive n, and the formula is asserted for every such sequence at n>2.

**Theorem 1.5 (Oudra's formula holds).**

$$(\exists A \in (\mathrm{Nat} \to \mathrm{Nat}),\; \operatorname{IsSourceSequence}\left(A\right)) \land (\forall A \in (\mathrm{Nat} \to \mathrm{Nat}),\; (\operatorname{IsSourceSequence}\left(A\right)) \Rightarrow (\forall n \in \mathrm{Nat},\; (2 < n) \Rightarrow ((A\left(n\right) : \mathrm{Int}) = \lfloor r \cdot (n : \mathrm{Real}) + \frac{r^{2}}{(n : \mathrm{Real})} - 1 \rfloor)))$$

*Proof.* Machine-checked in Lean as `D5/S3/ArithSums/OudraA248186CubicFloor.result` (`✓ std3`). ∎

*Resolves.* `Problems/oudra-a248186-cubic-floor` (proved) by `D5/S3/ArithSums/OudraA248186CubicFloor.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oudra-a248186-cubic-floor","declaration_gid":"D5/S3/ArithSums/OudraA248186CubicFloor.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Clark Kimberling; Ridouane Oudra (2023). *OEIS A248186, least reciprocal-product threshold index*. URL: <https://oeis.org/A248186/internal>.

*Commentary.*

Finite telescoping gives residual(k)=1/(3*(k+1)*(k+2)*(k+3)). Writing x=r*n and b=x+r^2/n, the identity r^3=1/3 gives 3*(b^3-b)=n^3+1/(3*n^3). For n>2 this lies strictly between n^3 and n^3+1. The polynomial 3*(y^3-y) is strictly increasing for y>=1. Its value at the integer floor of b is an integer, so it is at most n^3; its value at floor(b)+1 exceeds n^3. These bounds identify floor(b)-1 as the least positive admissible index. Translation of the floor by the integer one yields the displayed expression. For n=1 and n=2 the least index is one.

## References

- Truth anchor: `D5/S3/ArithSums/OudraA248186CubicFloor.IsSourceSequence`
- Truth anchor: `D5/S3/ArithSums/OudraA248186CubicFloor.claim`
- Truth anchor: `D5/S3/ArithSums/OudraA248186CubicFloor.r`
- Truth anchor: `D5/S3/ArithSums/OudraA248186CubicFloor.residual`
- Truth anchor: `D5/S3/ArithSums/OudraA248186CubicFloor.result`
