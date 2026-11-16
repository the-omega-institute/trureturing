# Copeland's A131758 polynomial content conjecture

## Abstract

At n=8 the complete coefficient row has content 1, but the proposed count is 2.

**Definition 1.1 (The source coefficient formula).**

$$\forall n \in \mathrm{Nat},\; \forall m \in \mathrm{Nat},\; \operatorname{a}\left(n, m\right) = (-1 : \mathrm{Rat})^{n} \cdot (\operatorname{Nat}.\operatorname{factorial}\left(n\right) : \mathrm{Rat}) \cdot (\sum_{k \in \operatorname{Finset}.\operatorname{range}\left(m + 1\right)} (-1 : \mathrm{Rat})^{k} \cdot (\operatorname{Nat}.\operatorname{choose}\left(n + 1, k\right) : \mathrm{Rat}) \cdot (\sum_{j \in \operatorname{Finset}.\operatorname{range}\left(n + 1\right)} \frac{(-1 : \mathrm{Rat})^{j} \cdot (\operatorname{Nat}.\operatorname{choose}\left(n, j\right) : \mathrm{Rat}) \cdot (\operatorname{Nat}.\operatorname{sub}\left(m, k\right) + 1 : \mathrm{Rat})^{j}}{(\operatorname{Nat}.\operatorname{factorial}\left(j\right) : \mathrm{Rat})}))$$

*Formalization.* `D5/S0/Certificates/CopelandA131758PolynomialContentRefutation.a` (`✓ std3`).

*Citation.* Tom Copeland (2008). *OEIS A131758: Coefficients of numerators of rational functions whose binomial transforms give the normalized polylogarithms Li(-n,t)/n!*. URL: <https://oeis.org/A131758>.

*Commentary.*

OEIS A131758, FORMULA (unpaginated), states verbatim: "a(n,m) = (-1)^n*n!*Sum_{k=0..m} (-1)^k*C(n+1,k)*Lag(n, m-k+1)." COMMENTS: "Lag(n,x) is a Laguerre polynomial and T(n,t) is a Touchard / Bell / exponential polynomial." The displayed inner rational sum is the ordinary order-zero Laguerre expansion of DLMF 18.5.12 at α=0. Indices n,m,k,j are natural numbers; Nat.sub is truncated natural subtraction, and k≤m throughout the outer sum. Rational division is by j!, which is nonzero.

**Definition 1.2 (The complete polynomial).**

$$\forall n \in \mathrm{Nat},\; \operatorname{P}\left(n\right) = \sum_{m \in \operatorname{Finset}.\operatorname{range}\left(n + 1\right)} \operatorname{Polynomial}.\operatorname{monomial}\left(m, \operatorname{a}\left(n, m\right)\right)$$

*Formalization.* `D5/S0/Certificates/CopelandA131758PolynomialContentRefutation.P` (`✓ std3`).

*Citation.* Tom Copeland (2008). *OEIS A131758: Coefficients of numerators of rational functions whose binomial transforms give the normalized polylogarithms Li(-n,t)/n!*. URL: <https://oeis.org/A131758>.

*Commentary.*

OEIS A131758, COMMENTS (unpaginated), states verbatim: "The P(n,t) are related to the Laguerre polynomials through

  P(n,t) = (-1)^n n! [ (1-t)^(n+1)} ] Sum_{k>=0} [ (t^k*Lag(n,k+1) ] = Sum_{m=0..n} a(n,m) * t^m" P n is the polynomial over ℚ containing all n+1 displayed coefficients.

**Definition 1.3 (Integer realization of a complete row).**

$$\forall n \in \mathrm{Nat},\; \forall row \in \operatorname{Fin}\left(n + 1\right) \to \mathrm{Int},\; (\operatorname{IsSourceRow}\left(n, row\right)) \Leftrightarrow (\forall m \in \operatorname{Fin}\left(n + 1\right),\; (\operatorname{row}\left(m\right) : \mathrm{Rat}) = \operatorname{a}\left(n, \operatorname{val}\left(m\right)\right))$$

*Formalization.* `D5/S0/Certificates/CopelandA131758PolynomialContentRefutation.IsSourceRow` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Tom Copeland (2008). *OEIS A131758: Coefficients of numerators of rational functions whose binomial transforms give the normalized polylogarithms Li(-n,t)/n!*. URL: <https://oeis.org/A131758>.

*Commentary.*

A row has domain Fin (n+1), including indices zero and n. Each integer coordinate, cast into ℚ, equals its source coefficient.

**Definition 1.4 (Nonnegative coefficient content).**

$$\forall n \in \mathrm{Nat},\; \forall row \in \operatorname{Fin}\left(n + 1\right) \to \mathrm{Int},\; \operatorname{rowContent}\left(row\right) = \operatorname{Finset}.\operatorname{gcd}\left((\operatorname{Finset}.\operatorname{univ} : \operatorname{Finset}\left(\operatorname{Fin}\left(n + 1\right)\right)), (fun (m : \operatorname{Fin}\left(n + 1\right)) \mapsto \operatorname{Int}.\operatorname{natAbs}\left(\operatorname{row}\left(m\right)\right))\right)$$

*Formalization.* `D5/S0/Certificates/CopelandA131758PolynomialContentRefutation.rowContent` (`✓ std3`).

*Citation.* Tom Copeland (2008). *OEIS A131758: Coefficients of numerators of rational functions whose binomial transforms give the normalized polylogarithms Li(-n,t)/n!*. URL: <https://oeis.org/A131758>.

*Commentary.*

The content is the finite gcd of the absolute values of all integer coordinates. The gcd of an all-zero row is zero.

**Definition 1.5 (Divisors no larger than the square root).**

$$\forall n \in \mathrm{Nat},\; \operatorname{D}\left(n\right) = \operatorname{Finset}.\operatorname{card}\left(\operatorname{Finset}.\operatorname{filter}\left((fun (d : \mathrm{Nat}) \mapsto d \cdot d \le n), \operatorname{Nat}.\operatorname{divisors}\left(n\right)\right)\right)$$

*Formalization.* `D5/S0/Certificates/CopelandA131758PolynomialContentRefutation.D` (`✓ std3`).

*Citation.* Tom Copeland (2008). *OEIS A131758: Coefficients of numerators of rational functions whose binomial transforms give the normalized polylogarithms Li(-n,t)/n!*. URL: <https://oeis.org/A131758>.

*Commentary.*

OEIS A038548, NAME (unpaginated), states verbatim: "Number of divisors of n that are at most sqrt(n)." Nat.divisors contains positive divisors for positive n; d*d≤n expresses the square-root bound. Nat.divisors 0 is empty, and D 0 is not asserted below.

**Definition 1.6 (Copeland's content assertion).**

$$(claim) \Leftrightarrow ((\forall n \in \mathrm{Nat},\; \exists row \in \operatorname{Fin}\left(n + 1\right) \to \mathrm{Int},\; \operatorname{IsSourceRow}\left(n, row\right)) \land (\forall n \in \mathrm{Nat},\; (1 \le n) \Rightarrow (\forall row \in \operatorname{Fin}\left(n + 1\right) \to \mathrm{Int},\; (\operatorname{IsSourceRow}\left(n, row\right)) \Rightarrow (\operatorname{rowContent}\left(row\right) = \operatorname{D}\left(n\right)))))$$

*Formalization.* `D5/S0/Certificates/CopelandA131758PolynomialContentRefutation.claim` (`✓ std3`).

*Citation.* Tom Copeland (2008). *OEIS A131758: Coefficients of numerators of rational functions whose binomial transforms give the normalized polylogarithms Li(-n,t)/n!*. URL: <https://oeis.org/A131758>.

*Commentary.*

OEIS A131758, COMMENTS, revision 48 (unpaginated), states verbatim: "Conjecture for the polynomial array:

The greatest common divisor of the coefficients of each polynomial is given by A060872(n)/n or, equivalently, by A038548(n)." The first conjunct asserts integer realizations at every n≥0. The second quantifies over every realization and every n≥1, matching the offset of A038548. The gcd always uses all n+1 coordinates of that same row.

**Theorem 1.7 (The content assertion is false).**

$$\neg ((\forall n \in \mathrm{Nat},\; \exists row \in \operatorname{Fin}\left(n + 1\right) \to \mathrm{Int},\; \operatorname{IsSourceRow}\left(n, row\right)) \land (\forall n \in \mathrm{Nat},\; (1 \le n) \Rightarrow (\forall row \in \operatorname{Fin}\left(n + 1\right) \to \mathrm{Int},\; (\operatorname{IsSourceRow}\left(n, row\right)) \Rightarrow (\operatorname{rowContent}\left(row\right) = \operatorname{D}\left(n\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/CopelandA131758PolynomialContentRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/copeland-a131758` (refuted) by `D5/S0/Certificates/CopelandA131758PolynomialContentRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"copeland-a131758","declaration_gid":"D5/S0/Certificates/CopelandA131758PolynomialContentRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Tom Copeland (2008). *OEIS A131758: Coefficients of numerators of rational functions whose binomial transforms give the normalized polylogarithms Li(-n,t)/n!*. URL: <https://oeis.org/A131758>.

*Commentary.*

At n=8 the integer row supplied by the existence assertion must begin 6209, −41417. Their coprimality forces the gcd of the complete nine-coordinate row to equal 1. The proposed divisor count D 8 equals 2, a contradiction. The proof uses only propext, Classical.choice and Quot.sound. It does not prove an infinite family or a replacement content formula.

## References

- Truth anchor: `D5/S0/Certificates/CopelandA131758PolynomialContentRefutation.D`
- Truth anchor: `D5/S0/Certificates/CopelandA131758PolynomialContentRefutation.IsSourceRow`
- Truth anchor: `D5/S0/Certificates/CopelandA131758PolynomialContentRefutation.P`
- Truth anchor: `D5/S0/Certificates/CopelandA131758PolynomialContentRefutation.a`
- Truth anchor: `D5/S0/Certificates/CopelandA131758PolynomialContentRefutation.claim`
- Truth anchor: `D5/S0/Certificates/CopelandA131758PolynomialContentRefutation.result`
- Truth anchor: `D5/S0/Certificates/CopelandA131758PolynomialContentRefutation.rowContent`
