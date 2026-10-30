# The OEIS A380680 Square-Residue Conjecture Is False

## Abstract

Hanna's square-residue conjecture for OEIS A380680 fails at n = 1.

**Definition 1.1 (The coefficients of A380680).**

$$\forall m \in \mathbb{N},\; \operatorname{a}\left(m\right) = \operatorname{PowerSeries}.\operatorname{coeff}\left(m, 1 + 2 \cdot \sum_{n \in \operatorname{Finset}.\operatorname{Icc}\left(1, m\right)} (((\operatorname{PowerSeries}.\operatorname{X}: \operatorname{PowerSeries}\left(\mathbb{Q}\right)))^{(n)^{2}} \cdot (2 - ((\operatorname{PowerSeries}.\operatorname{X}: \operatorname{PowerSeries}\left(\mathbb{Q}\right)))^{n})^{n} \cdot ((1 - 2 \cdot ((\operatorname{PowerSeries}.\operatorname{X}: \operatorname{PowerSeries}\left(\mathbb{Q}\right)))^{n})^{n})^{-1})\right)$$

*Formalization.* `D5/S0/Certificates/OeisA380680BilateralModFourRefutation.a` (`✓ std3`).

*Citation.* Paul D. Hanna (2025). *OEIS A380680, bilateral rational-quotient square series*. URL: <https://oeis.org/A380680>.

*Commentary.*

Paul D. Hanna, OEIS A380680, unpaginated Name: "G.f. A(x) = Sum_{n=-oo..+oo} x^(n^2) * (2 - x^n)^n/(1 - 2*x^n)^n." Comments: "The term x^(n^2) * (2 - x^n)^n/(1 - 2*x^n)^n is invariant under sign reversal of n." Formula (2): "A(x) = 1 + 2*Sum_{n>=1} x^(n^2) * (2 - x^n)^n/(1 - 2*x^n)^n." The term at zero is one and opposite indices give equal terms. The coefficient at the natural index m is taken in PowerSeries(Q), summing over Finset.Icc 1 m. Larger indices contribute zero because the summand contains X^(n^2). The inverse is the formal power-series inverse, with denominator constant coefficient one. The entry starts at index zero, with coefficients 1, 4, 6.

**Definition 1.2 (Hanna's square-residue conjecture).**

$$\operatorname{claim} = (\forall n \in \mathbb{N},\; (0 < n) \Rightarrow (\exists z \in \mathbb{Z},\; ((z: \mathbb{Q}) = \operatorname{a}\left(n\right)) \land (((\operatorname{Int}.\operatorname{emod}\left(z, 4\right) = 2) \Leftrightarrow (\operatorname{IsSquare}\left(n\right))) \land ((\neg \operatorname{IsSquare}\left(n\right)) \Rightarrow ((4: \mathbb{Z}) \mid z)))))$$

*Formalization.* `D5/S0/Certificates/OeisA380680BilateralModFourRefutation.claim` (`✓ std3`).

*Citation.* Paul D. Hanna (2025). *OEIS A380680, bilateral rational-quotient square series*. URL: <https://oeis.org/A380680>.

*Commentary.*

OEIS A380680, unpaginated Comments: "Conjecture: for n > 0, a(n) == 2 (mod 4) iff n is a square, and a(n) is divisible by 4 when n is nonsquare." The index n is natural and positive. The integer z equals the rational coefficient a(n) through the integer-to-rational coercion. Int.emod z 4 is the integer remainder z % 4. IsSquare n means that n is a product of a natural number with itself. Both the residue equivalence and nonsquare divisibility are asserted for that same integer z.

**Theorem 1.3 (The conjecture fails at one).**

$$\neg (\forall n \in \mathbb{N},\; (0 < n) \Rightarrow (\exists z \in \mathbb{Z},\; ((z: \mathbb{Q}) = \operatorname{a}\left(n\right)) \land (((\operatorname{Int}.\operatorname{emod}\left(z, 4\right) = 2) \Leftrightarrow (\operatorname{IsSquare}\left(n\right))) \land ((\neg \operatorname{IsSquare}\left(n\right)) \Rightarrow ((4: \mathbb{Z}) \mid z)))))$$

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/OeisA380680BilateralModFourRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a380680-hanna-bilateral-mod-four` (refuted) by `D5/S0/Certificates/OeisA380680BilateralModFourRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a380680-hanna-bilateral-mod-four","declaration_gid":"D5/S0/Certificates/OeisA380680BilateralModFourRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2025). *OEIS A380680, bilateral rational-quotient square series*. URL: <https://oeis.org/A380680>.

*Commentary.*

The first coefficient is a(1) = 4: only index one contributes, and its quotient has constant coefficient two. Since one is a square, the conjecture would require the integer coefficient four to have remainder two modulo four. Its remainder is zero, giving a contradiction.

## References

- Truth anchor: `D5/S0/Certificates/OeisA380680BilateralModFourRefutation.a`
- Truth anchor: `D5/S0/Certificates/OeisA380680BilateralModFourRefutation.claim`
- Truth anchor: `D5/S0/Certificates/OeisA380680BilateralModFourRefutation.result`
