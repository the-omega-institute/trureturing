# Song's conjecture in OEIS A232624

## Abstract

The exact leading term of the difference of odd and doubled cosine minimal polynomials.

The polynomials have coefficients in Q. MPR2 n is the minimal polynomial over Q of the stated real cosine. Nat.div denotes natural-number division; subtraction between natural numbers is truncated subtraction. For odd n > 1, m is positive and odd and m <= d, so d - m is the ordinary nonnegative difference. The variable e below denotes the rational sign written epsilon in the text. Multiplication by the rational one half is scalar multiplication of polynomials.

**Definition 1.1 (The real cosine minimal polynomial).**

$$\forall n \in \mathbb{N},\; \operatorname{MPR2}\left(n\right) = \operatorname{minpoly}\left(\mathbb{Q}, (2: \mathbb{R})\cdot \operatorname{Real}.\operatorname{cos}\left(\frac{2\cdot \operatorname{Real}.\operatorname{pi}}{(n: \mathbb{R})}\right)\right)$$

*Formalization.* `D5/S3/Arith/InterlaceFan/SongA232624LeadingTerm.MPR2` (`✓ std3`).

*Citation.* Jianing Song; Wolfdieter Lang (2019). *OEIS A232624: cosine minimal-polynomial coefficient array and Song's conjecture*. URL: <https://oeis.org/A232624>.

*Commentary.*

OEIS A232624 revision 109, unpaginated Formula line: "a(n,m) = [x^m] MPR2(n, x), n >= 1, m=0, 1, ..., deg(n), with MPR2(n, x) the (monic) minimal polynomials of 2*cos(2*Pi/n), explained in a comment above. The degree is deg(1) = deg(2) = 1, deg(n) = phi(n)/2 = A023022(n), n >= 3 (phi is the Euler totient function A000010)." The real number is 2 times Real.cos (2 times Real.pi divided by the real cast of n). The coefficient field of minpoly is Q.

**Definition 1.2 (The coefficient array).**

$$\forall n \in \mathbb{N},\; \forall j \in \mathbb{N},\; \operatorname{a}\left(n, j\right) = (\operatorname{MPR2}\left(n\right)).\operatorname{coeff}\left(j\right)$$

*Formalization.* `D5/S3/Arith/InterlaceFan/SongA232624LeadingTerm.a` (`✓ std3`).

*Citation.* Jianing Song; Wolfdieter Lang (2019). *OEIS A232624: cosine minimal-polynomial coefficient array and Song's conjecture*. URL: <https://oeis.org/A232624>.

*Commentary.*

OEIS A232624 revision 109, unpaginated Formula line: "a(n,m) = [x^m] MPR2(n, x), n >= 1, m=0, 1, ..., deg(n), with MPR2(n, x) the (monic) minimal polynomials of 2*cos(2*Pi/n), explained in a comment above. The degree is deg(1) = deg(2) = 1, deg(n) = phi(n)/2 = A023022(n), n >= 3 (phi is the Euler totient function A000010)." Polynomial.coeff extends the array by zero above the degree; the source uses rows beginning at n = 1 and coefficient indices beginning at zero.

**Definition 1.3 (The leading term and all coefficient consequences).**

$$\operatorname{claim} = (\forall n \in \mathbb{N},\; (\operatorname{Odd}\left(n\right)) \Rightarrow ((1 < n) \Rightarrow (\operatorname{let} d: \mathbb{N} = \operatorname{Nat}.\operatorname{div}\left(\operatorname{Nat}.\operatorname{totient}\left(n\right), 2\right); \operatorname{let} m: \mathbb{N} = \operatorname{Nat}.\operatorname{div}\left(n, \operatorname{UniqueFactorizationMonoid}.\operatorname{radical}\left(n\right)\right); \operatorname{let} e: \mathbb{Q} = (-1: \mathbb{Q})^{\operatorname{ArithmeticFunction}.\operatorname{cardDistinctFactors}\left(n\right)}; \operatorname{let} F: \operatorname{Polynomial}\left(\mathbb{Q}\right) = (\frac{1}{2}: \mathbb{Q})\cdot (\operatorname{MPR2}\left(2\cdot n\right)-\operatorname{MPR2}\left(n\right)); (F \ne 0) \land ((F.\operatorname{natDegree} = d-m) \land ((F.\operatorname{leadingCoeff} = e) \land ((\forall k \in \mathbb{N},\; (\operatorname{Odd}\left(k\right)) \Rightarrow ((k < m) \Rightarrow ((\operatorname{a}\left(n, d-k\right) = 0) \land (\operatorname{a}\left(2\cdot n, d-k\right) = 0)))) \land ((\operatorname{a}\left(n, d-m\right) = -e) \land (\operatorname{a}\left(2\cdot n, d-m\right) = e))))))))$$

*Formalization.* `D5/S3/Arith/InterlaceFan/SongA232624LeadingTerm.claim` (`✓ std3`).

*Citation.* Jianing Song; Wolfdieter Lang (2019). *OEIS A232624: cosine minimal-polynomial coefficient array and Song's conjecture*. URL: <https://oeis.org/A232624>.

*Commentary.*

OEIS A232624 revision 109, unpaginated Comment line: "Conjecture: For odd n > 1, the term of the highest degree of (MPR2(2n, x) - MPR2(n, x))/2 is (-1)^omega(n) * x^(phi(n)/2-n/rad(n)) = A076479(n) * x^(A023022(n)-A003557(n)). For example, for n = 15, (MPR2(30, x) - MPR2(15, x))/2 = x^3 - 4x; for n = 105, (MPR2(210, x) - MPR2(105, x))/2 = -x^23 + ...; for n = 225, (MPR2(450, x) - MPR2(225, x))/2 = x^45 + ... If this is true, then for odd n > 1, a(n,A023022(n)-k) = a(2n,A023022(n)-k) = 0 for k = 1, 3, ..., A003557(n)-2; a(n,A023022(n)-A003557(n)) = -A076479(n) and a(2n,A023022(n)-A003557(n)) = A076479(n). - _Jianing Song_, Jul 11 2019" Nat.totient, UniqueFactorizationMonoid.radical and ArithmeticFunction.cardDistinctFactors express phi, rad and omega. Odd k and k < m express precisely 1, 3, ..., m - 2. The formula includes nonzeroness and every coefficient consequence.

**Theorem 1.4 (Song's leading term formula).**

$$\forall n \in \mathbb{N},\; (\operatorname{Odd}\left(n\right)) \Rightarrow ((1 < n) \Rightarrow (\operatorname{let} d: \mathbb{N} = \operatorname{Nat}.\operatorname{div}\left(\operatorname{Nat}.\operatorname{totient}\left(n\right), 2\right); \operatorname{let} m: \mathbb{N} = \operatorname{Nat}.\operatorname{div}\left(n, \operatorname{UniqueFactorizationMonoid}.\operatorname{radical}\left(n\right)\right); \operatorname{let} e: \mathbb{Q} = (-1: \mathbb{Q})^{\operatorname{ArithmeticFunction}.\operatorname{cardDistinctFactors}\left(n\right)}; \operatorname{let} F: \operatorname{Polynomial}\left(\mathbb{Q}\right) = (\frac{1}{2}: \mathbb{Q})\cdot (\operatorname{MPR2}\left(2\cdot n\right)-\operatorname{MPR2}\left(n\right)); (F \ne 0) \land ((F.\operatorname{natDegree} = d-m) \land ((F.\operatorname{leadingCoeff} = e) \land ((\forall k \in \mathbb{N},\; (\operatorname{Odd}\left(k\right)) \Rightarrow ((k < m) \Rightarrow ((\operatorname{a}\left(n, d-k\right) = 0) \land (\operatorname{a}\left(2\cdot n, d-k\right) = 0)))) \land ((\operatorname{a}\left(n, d-m\right) = -e) \land (\operatorname{a}\left(2\cdot n, d-m\right) = e)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/InterlaceFan/SongA232624LeadingTerm.result` (`✓ std3`). ∎

*Resolves.* `Problems/song232624-leadingterm` (proved) by `D5/S3/Arith/InterlaceFan/SongA232624LeadingTerm.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"song232624-leadingterm","declaration_gid":"D5/S3/Arith/InterlaceFan/SongA232624LeadingTerm.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Jianing Song; Wolfdieter Lang (2019). *OEIS A232624: cosine minimal-polynomial coefficient array and Song's conjecture*. URL: <https://oeis.org/A232624>.

*Commentary.*

Möbius inversion in the power-series quotient by X raised to m + 1 leaves the unique factor indexed by rad(n) and n/rad(n). Its first nonconstant coefficient is minus e. Reflection at odd conductors makes the cyclotomic half-difference start with e times X raised to m. Homogeneous evaluation at X squared plus one and X identifies it with the reciprocal substitution of the actual cosine minimal-polynomial difference. Its lowest coefficient determines the degree and leading coefficient of that difference without cancellation. Reflection then gives every displayed coefficient identity.

## References

- Truth anchor: `D5/S3/Arith/InterlaceFan/SongA232624LeadingTerm.MPR2`
- Truth anchor: `D5/S3/Arith/InterlaceFan/SongA232624LeadingTerm.a`
- Truth anchor: `D5/S3/Arith/InterlaceFan/SongA232624LeadingTerm.claim`
- Truth anchor: `D5/S3/Arith/InterlaceFan/SongA232624LeadingTerm.result`
- Dependency: [D5/S3/Arith/InterlaceFan/Cyclotomic](Cyclotomic.md)
