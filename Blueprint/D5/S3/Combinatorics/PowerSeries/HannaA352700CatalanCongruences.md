# Hanna's modulo 2 and modulo 3 conjectures for OEIS A352700

## Abstract

Lagrange substitution and Frobenius pairing prove Hanna's six A352700 congruences.

Power series are formal univariate series in X over Z or ZMod(p). The operation PowerSeries.subst(u,f) denotes formal composition f(u) when u has zero constant coefficient; PowerSeries.coeff(k,f) extracts the degree-k coefficient of f; Finset.range(k) is the finite set {0,...,k-1}; PowerSeries.map applies a ring homomorphism coefficientwise, and PowerSeries.invOfUnit(f,1) is the multiplicative inverse of a series f with constant coefficient one. Natural division Nat.div is exact on every displayed weight, Catalan quotient Nat.div(Nat.choose(2*n+1,n), 2*n+1) = catalan(n), and Raney quotient; Nat.cast embeds natural numbers into Z, Int.ModEq(m,a,b) denotes congruence a ≡ b (mod m) in Z, and catalan(n) is the n-th Catalan number A000108(n).

SignedCatalanCubicSubstitutionModThree.inverse_exists supplies two-sided compositional inversion on normalized integral power series, and prime_power_subst gives the Frobenius substitution identity f^p = f(X^p) over ZMod(p) for prime p.

**Definition 1.1 (Exact integer binomial weight).**

$$\forall m: \mathbb{N}, (\operatorname{weight}\left(m\right) = \operatorname{Nat}.\operatorname{div}\left(\operatorname{Nat}.\operatorname{choose}\left(\left(m + 1\right) \cdot \left(2 \cdot m + 1\right), m\right), 2 \cdot m + 1\right))$$

*Formalization.* `D5/S3/Combinatorics/PowerSeries/HannaA352700CatalanCongruences.weight` (`✓ std3`).

*Citation.* Paul D. Hanna (2022). *OEIS A352700: Catalan inverse-power binomial series and modulo 2 and 3 congruences*. URL: <https://oeis.org/A352700>.

*Commentary.*

OEIS A352700, NAME (unpaginated): the m-th summand carries weight binomial((m+1)*(2*m+1), m)/(2*m+1). Because gcd(2*m+1, m) = 1 and (m+1)*(2*m+1)*binomial((m+1)*(2*m+1)-1, m-1) = m*binomial((m+1)*(2*m+1), m) for m >= 1, the odd denominator 2*m+1 divides the binomial numerator in N for every m >= 0.

**Definition 1.2 (Integral Catalan generating series).**

$$\operatorname{catalanZ} = \operatorname{PowerSeries}.\operatorname{map}\left(\operatorname{Nat}.\operatorname{castRingHom}\left(\mathbb{Z}\right), \operatorname{PowerSeries}.\operatorname{catalanSeries}\right)$$

*Formalization.* `D5/S3/Combinatorics/PowerSeries/HannaA352700CatalanCongruences.catalanZ` (`✓ std3`).

*Citation.* Paul D. Hanna (2022). *OEIS A352700: Catalan inverse-power binomial series and modulo 2 and 3 congruences*. URL: <https://oeis.org/A352700>.

*Commentary.*

OEIS A352700, NAME and COMMENTS (unpaginated): C(x) = 1 + x*C(x)^2 is the Catalan generating series (OEIS A000108), obtained by casting PowerSeries.catalanSeries from N[[X]] to Z[[X]].

**Definition 1.3 (Multiplicative inverse of the Catalan series).**

$$\operatorname{catalanInvZ} = \operatorname{PowerSeries}.\operatorname{invOfUnit}\left(\operatorname{catalanZ}, 1\right)$$

*Formalization.* `D5/S3/Combinatorics/PowerSeries/HannaA352700CatalanCongruences.catalanInvZ` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2022). *OEIS A352700: Catalan inverse-power binomial series and modulo 2 and 3 congruences*. URL: <https://oeis.org/A352700>.

*Commentary.*

Since catalanZ has constant coefficient 1, it is a unit in Z[[X]]. Its multiplicative inverse C(X)^(-1) satisfies C(X)^(-1) = 1 - X*C(X).

**Definition 1.4 (Coefficient sequence of OEIS A352700).**

$$\forall n: \mathbb{N}, (\operatorname{coeffA}\left(n\right) = \sum_{m\in\operatorname{Finset}.\operatorname{range}\left(n + 1\right)}(\operatorname{Nat}.\operatorname{cast}\left(\operatorname{weight}\left(m\right)\right) \cdot \operatorname{PowerSeries}.\operatorname{coeff}\left(n - m, (\operatorname{catalanInvZ})^{m \cdot \left(2 \cdot m + 1\right) + 1}\right)))$$

*Formalization.* `D5/S3/Combinatorics/PowerSeries/HannaA352700CatalanCongruences.coeffA` (`✓ std3`).

*Citation.* Paul D. Hanna (2022). *OEIS A352700: Catalan inverse-power binomial series and modulo 2 and 3 congruences*. URL: <https://oeis.org/A352700>.

*Commentary.*

OEIS A352700, NAME and PROG (unpaginated): in the defining sum sum_{m>=0} weight(m)*X^m*(C(X)^(-1))^(m*(2*m+1)+1), every summand with m > n is divisible by X^(n+1), so the degree-n coefficient a(n) equals the displayed finite sum over 0 <= m <= n.

**Definition 1.5 (Integral generating series of OEIS A352700).**

$$\operatorname{seriesA} = \operatorname{PowerSeries}.\operatorname{mk}\left(\operatorname{coeffA}\right)$$

*Formalization.* `D5/S3/Combinatorics/PowerSeries/HannaA352700CatalanCongruences.seriesA` (`✓ std3`).

*Citation.* Paul D. Hanna (2022). *OEIS A352700: Catalan inverse-power binomial series and modulo 2 and 3 congruences*. URL: <https://oeis.org/A352700>.

*Commentary.*

OEIS A352700, NAME (unpaginated): A(X) = sum_{n>=0} a(n)*X^n in Z[[X]] assembled from coeffA.

**Definition 1.6 (Modular reduction of A(X)).**

$$\forall p: \mathbb{N}, (\operatorname{seriesMod}\left(p\right) = \operatorname{PowerSeries}.\operatorname{map}\left(\operatorname{Int}.\operatorname{castRingHom}\left(\operatorname{ZMod}\left(p\right)\right), \operatorname{seriesA}\right))$$

*Formalization.* `D5/S3/Combinatorics/PowerSeries/HannaA352700CatalanCongruences.seriesMod` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2022). *OEIS A352700: Catalan inverse-power binomial series and modulo 2 and 3 congruences*. URL: <https://oeis.org/A352700>.

*Commentary.*

Coefficientwise reduction of seriesA from Z[[X]] to (ZMod(p))[[X]].

**Definition 1.7 (Modular reduction of C(X)).**

$$\forall p: \mathbb{N}, (\operatorname{catalanMod}\left(p\right) = \operatorname{PowerSeries}.\operatorname{map}\left(\operatorname{Int}.\operatorname{castRingHom}\left(\operatorname{ZMod}\left(p\right)\right), \operatorname{catalanZ}\right))$$

*Formalization.* `D5/S3/Combinatorics/PowerSeries/HannaA352700CatalanCongruences.catalanMod` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2022). *OEIS A352700: Catalan inverse-power binomial series and modulo 2 and 3 congruences*. URL: <https://oeis.org/A352700>.

*Commentary.*

Coefficientwise reduction of catalanZ from Z[[X]] to (ZMod(p))[[X]].

**Definition 1.8 (Second binomial quotient of conjecture (4)).**

$$\forall n: \mathbb{N}, (\operatorname{raneyTerm}\left(n\right) = \operatorname{ite}\left(n < 2, 0, \operatorname{Nat}.\operatorname{div}\left(3 \cdot \operatorname{Nat}.\operatorname{choose}\left(2 \cdot n - 1, n - 2\right), 2 \cdot n - 1\right)\right))$$

*Formalization.* `D5/S3/Combinatorics/PowerSeries/HannaA352700CatalanCongruences.raneyTerm` (`✓ std3`).

*Citation.* Paul D. Hanna (2022). *OEIS A352700: Catalan inverse-power binomial series and modulo 2 and 3 congruences*. URL: <https://oeis.org/A352700>.

*Commentary.*

OEIS A352700, COMMENTS (4) and EXAMPLE (unpaginated): represents 3*binomial(2*n-1, n-2)/(2*n-1) under the standard negative-lower-index binomial rule binomial(2*n-1, n-2) = 0 for n < 2. For n = k+2 >= 2, exact division holds in N and equals catalan(k+2) - catalan(k+1).

**Definition 1.9 (Conjunction of Hanna's six A352700 conjectures).**

$$\operatorname{claim} \iff (((\operatorname{seriesMod}\left(3\right))^{3} = \operatorname{PowerSeries}.\operatorname{subst}\left((X)^{3}, \operatorname{seriesMod}\left(3\right)\right)) \land (((\operatorname{seriesMod}\left(3\right) = \operatorname{catalanMod}\left(3\right) + (X)^{2} \cdot (\operatorname{catalanMod}\left(3\right))^{3}) \land (\operatorname{catalanMod}\left(3\right) + (X)^{2} \cdot (\operatorname{catalanMod}\left(3\right))^{3} = \left(2 - X\right) \cdot \operatorname{catalanMod}\left(3\right) - 1)) \land ((\operatorname{seriesMod}\left(2\right) = \operatorname{catalanMod}\left(2\right)) \land ((\forall n: \mathbb{N}, (\operatorname{Int}.\operatorname{ModEq}\left(3, \operatorname{coeffA}\left(n\right), \operatorname{Nat}.\operatorname{cast}\left(\operatorname{Nat}.\operatorname{div}\left(\operatorname{Nat}.\operatorname{choose}\left(2 \cdot n + 1, n\right), 2 \cdot n + 1\right)\right) + \operatorname{Nat}.\operatorname{cast}\left(\operatorname{raneyTerm}\left(n\right)\right)\right))) \land ((\forall n: \mathbb{N}, ((1 \leq n) \implies (\operatorname{Int}.\operatorname{ModEq}\left(3, \operatorname{coeffA}\left(n\right), 2 \cdot \operatorname{Nat}.\operatorname{cast}\left(\operatorname{catalan}\left(n\right)\right) - \operatorname{Nat}.\operatorname{cast}\left(\operatorname{catalan}\left(n - 1\right)\right)\right)))) \land (\forall n: \mathbb{N}, (\operatorname{Int}.\operatorname{ModEq}\left(2, \operatorname{coeffA}\left(n\right), \operatorname{Nat}.\operatorname{cast}\left(\operatorname{catalan}\left(n\right)\right)\right))))))))$$

*Formalization.* `D5/S3/Combinatorics/PowerSeries/HannaA352700CatalanCongruences.claim` (`✓ std3`).

*Citation.* Paul D. Hanna (2022). *OEIS A352700: Catalan inverse-power binomial series and modulo 2 and 3 congruences*. URL: <https://oeis.org/A352700>.

*Commentary.*

OEIS A352700, COMMENTS (unpaginated), conjectures (1)-(6) of Paul D. Hanna (March 2022): (1) A(X)^3 ≡ A(X^3) (mod 3); (2) A(X) ≡ C(X) + X^2*C(X)^3 ≡ (2 - X)*C(X) - 1 (mod 3); (3) A(X) ≡ C(X) (mod 2); (4) a(n) ≡ binomial(2*n+1,n)/(2*n+1) + raneyTerm(n) (mod 3) for all n >= 0, where 2*n+1 divides Nat.choose(2*n+1,n) in N with exact quotient catalan(n); (5) a(n) ≡ 2*catalan(n) - catalan(n-1) (mod 3) for all n >= 1; and (6) a(n) ≡ catalan(n) (mod 2) for all n >= 0.

**Theorem 1.10 (Proof of Hanna's six A352700 conjectures).**

$$((\operatorname{seriesMod}\left(3\right))^{3} = \operatorname{PowerSeries}.\operatorname{subst}\left((X)^{3}, \operatorname{seriesMod}\left(3\right)\right)) \land (((\operatorname{seriesMod}\left(3\right) = \operatorname{catalanMod}\left(3\right) + (X)^{2} \cdot (\operatorname{catalanMod}\left(3\right))^{3}) \land (\operatorname{catalanMod}\left(3\right) + (X)^{2} \cdot (\operatorname{catalanMod}\left(3\right))^{3} = \left(2 - X\right) \cdot \operatorname{catalanMod}\left(3\right) - 1)) \land ((\operatorname{seriesMod}\left(2\right) = \operatorname{catalanMod}\left(2\right)) \land ((\forall n: \mathbb{N}, (\operatorname{Int}.\operatorname{ModEq}\left(3, \operatorname{coeffA}\left(n\right), \operatorname{Nat}.\operatorname{cast}\left(\operatorname{Nat}.\operatorname{div}\left(\operatorname{Nat}.\operatorname{choose}\left(2 \cdot n + 1, n\right), 2 \cdot n + 1\right)\right) + \operatorname{Nat}.\operatorname{cast}\left(\operatorname{raneyTerm}\left(n\right)\right)\right))) \land ((\forall n: \mathbb{N}, ((1 \leq n) \implies (\operatorname{Int}.\operatorname{ModEq}\left(3, \operatorname{coeffA}\left(n\right), 2 \cdot \operatorname{Nat}.\operatorname{cast}\left(\operatorname{catalan}\left(n\right)\right) - \operatorname{Nat}.\operatorname{cast}\left(\operatorname{catalan}\left(n - 1\right)\right)\right)))) \land (\forall n: \mathbb{N}, (\operatorname{Int}.\operatorname{ModEq}\left(2, \operatorname{coeffA}\left(n\right), \operatorname{Nat}.\operatorname{cast}\left(\operatorname{catalan}\left(n\right)\right)\right)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PowerSeries/HannaA352700CatalanCongruences.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a352700-hanna-catalan-congruences` (proved) by `D5/S3/Combinatorics/PowerSeries/HannaA352700CatalanCongruences.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a352700-hanna-catalan-congruences","declaration_gid":"D5/S3/Combinatorics/PowerSeries/HannaA352700CatalanCongruences.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2022). *OEIS A352700: Catalan inverse-power binomial series and modulo 2 and 3 congruences*. URL: <https://oeis.org/A352700>.

*Commentary.*

Substituting zeta(X) = X*(1+X)^(-2) sends C(X) - 1 to X and C(X)^(-1) to (1+X)^(-1), transforming A(X) into B(C(X) - 1) where B(X) = sum_{m>=0} weight(m)*X^m*(1+X)^(-(m+1)*(2*m+1)) has degree-n coefficient sum_{m=0}^n (-1)^(n-m)*weight(m)*binomial(2*m*(m+1)+n, n-m). Modulo 2, Pascal absorption splits each m >= 1 summand into two quadratic binomial sums sum_{j=0}^L binomial(L,j)*binomial(2*(j+c)*(j+c+1)+d+L, L), which vanish for L >= 1 by pairing j with j + 2^k where 2^k <= L < 2^(k+1); hence B(X) ≡ 1 + X (mod 2) and A(X) ≡ 1 + (C(X) - 1) = C(X) (mod 2), giving (3) and (6). Modulo 3, binomial absorption and Lucas decomposition force weight(m) ≡ 0 (mod 3) whenever m >= 1 and m ≢ 1 (mod 3), while for n = 3*N + 1 >= 4 the remaining m = 3*M + 1 slice reduces to 2*sum_{M=0}^N (-1)^(N-M)*binomial(N,M)*binomial(6*M*(M+1)+1+N, N), which vanishes by 3-way Frobenius grouping M, M + 3^k, M + 2*3^k for 3^k <= N < 3^(k+1). Thus B(X) ≡ (1+X)^(-1) + 2*X (mod 3), so A(X) ≡ C(X)^(-1) + 2*(C(X) - 1) = (2 - X)*C(X) - 1 = C(X) + X^2*C(X)^3 (mod 3), establishing (2), (1) by prime_power_subst, and (4)-(5) by coefficient extraction. Global literature novelty is unverified.

## References

- Truth anchor: `D5/S3/Combinatorics/PowerSeries/HannaA352700CatalanCongruences.catalanInvZ`
- Truth anchor: `D5/S3/Combinatorics/PowerSeries/HannaA352700CatalanCongruences.catalanMod`
- Truth anchor: `D5/S3/Combinatorics/PowerSeries/HannaA352700CatalanCongruences.catalanZ`
- Truth anchor: `D5/S3/Combinatorics/PowerSeries/HannaA352700CatalanCongruences.claim`
- Truth anchor: `D5/S3/Combinatorics/PowerSeries/HannaA352700CatalanCongruences.coeffA`
- Truth anchor: `D5/S3/Combinatorics/PowerSeries/HannaA352700CatalanCongruences.raneyTerm`
- Truth anchor: `D5/S3/Combinatorics/PowerSeries/HannaA352700CatalanCongruences.result`
- Truth anchor: `D5/S3/Combinatorics/PowerSeries/HannaA352700CatalanCongruences.seriesA`
- Truth anchor: `D5/S3/Combinatorics/PowerSeries/HannaA352700CatalanCongruences.seriesMod`
- Truth anchor: `D5/S3/Combinatorics/PowerSeries/HannaA352700CatalanCongruences.weight`
- Dependency: [D5/S1/Recurrence/Invariants/SignedCatalanCubicSubstitutionModThree](../../../S1/Recurrence/Invariants/SignedCatalanCubicSubstitutionModThree.md)
