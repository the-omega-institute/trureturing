# The alternating Catalan recurrence

## Abstract

Mathar's D-finite recurrence for the alternating Catalan numbers.

The sequence is the signed binomial transform of the Catalan numbers, scaled by 16 to the index power. All sum indices and sequence arguments are natural numbers; subtraction in an argument, including 2n-i, is natural truncated subtraction. Every polynomial coefficient of the recurrence is evaluated in the integers. The parenthesized casts to Z display that distinction.

**Definition 1.1 (Alternating Catalan numbers).**

$$\forall n \in \mathbb{N},\; \operatorname{a308815}\left(n\right) = 16^{n} \cdot \sum_{i \in \operatorname{Finset}.\operatorname{range}\left(n + 1\right)} (-2:\mathbb{Z})^{i} \cdot (\operatorname{Nat}.\operatorname{choose}\left(n, i\right):\mathbb{Z}) \cdot (\operatorname{catalan}\left(2 \cdot n - i\right):\mathbb{Z})$$

*Formalization.* `D5/S1/Recurrence/A308815DFiniteRecurrence.a308815` (`✓ std3`).

*Citation.* Gavril Farkas; Riccardo Moschetti; Juan Carlos Naranjo; Gian Pietro Pirola (2021). *Alternating Catalan numbers and curves with triple ramification*. DOI: [10.2422/2036-2145.201909_009](https://doi.org/10.2422/2036-2145.201909_009). URL: <https://arxiv.org/abs/1906.10406>.

*Commentary.*

Theorem 1.1, page 1 of arXiv:1906.10406v2: “The number of odd covers of degree 2g + 1 of a general curve of genus g ≥ 3 equals” the displayed signed binomial sum. The genus g is n here, and Mathlib's catalan is the ordinary Catalan sequence. OEIS A308815 gives the same expression in its PARI program: “a(n) = 16^n*sum(i=0, n, (-2)^i*binomial(n, i)*C(2*n-i));”. The NAME line prints 2^i; the PARI expression and the displayed data use (-2)^i. The sum defines the initial indices as well; the geometric interpretation starts at n ≥ 3.

**Definition 1.2 (Mathar's recurrence assertion).**

$$claim \Leftrightarrow \left(\forall n \in \mathbb{N},\; 3 \le n \Rightarrow (n:\mathbb{Z}) \cdot (2 \cdot (n:\mathbb{Z}) + 1) \cdot \operatorname{a308815}\left(n\right) - 32 \cdot (9 \cdot (n:\mathbb{Z}) - 4) \cdot ((n:\mathbb{Z}) - 1) \cdot \operatorname{a308815}\left(n - 1\right) + 1024 \cdot (3 \cdot (n:\mathbb{Z})^{2} - 23 \cdot (n:\mathbb{Z}) + 29) \cdot \operatorname{a308815}\left(n - 2\right) + 65536 \cdot ((n:\mathbb{Z}) - 2) \cdot (2 \cdot (n:\mathbb{Z}) - 5) \cdot \operatorname{a308815}\left(n - 3\right) = 0\right)$$

*Formalization.* `D5/S1/Recurrence/A308815DFiniteRecurrence.claim` (`✓ std3`).

*Citation.* R. J. Mathar; OEIS Foundation Inc. (2020). *OEIS A308815 — D-finite recurrence for alternating Catalan numbers*. URL: <https://oeis.org/A308815>.

*Commentary.*

OEIS A308815, FORMULA section (no page numbers): “Conjecture: D-finite with recurrence: n*(2*n+1)*a(n) -32*(9*n-4)*(n-1)*a(n-1) +1024*(3*n^2-23*n+29)*a(n-2) +65536*(n-2)*(2*n-5)*a(n-3)=0. - _R. J. Mathar_, Jan 27 2020”. Here a is a308815. The assertion ranges over every natural n ≥ 3; lagged indices use natural subtraction, and the factors n-1 and n-2 outside a308815 use integer subtraction.

**Theorem 1.3 (The recurrence holds).**

$$\forall n \in \mathbb{N},\; 3 \le n \Rightarrow (n:\mathbb{Z}) \cdot (2 \cdot (n:\mathbb{Z}) + 1) \cdot \operatorname{a308815}\left(n\right) - 32 \cdot (9 \cdot (n:\mathbb{Z}) - 4) \cdot ((n:\mathbb{Z}) - 1) \cdot \operatorname{a308815}\left(n - 1\right) + 1024 \cdot (3 \cdot (n:\mathbb{Z})^{2} - 23 \cdot (n:\mathbb{Z}) + 29) \cdot \operatorname{a308815}\left(n - 2\right) + 65536 \cdot ((n:\mathbb{Z}) - 2) \cdot (2 \cdot (n:\mathbb{Z}) - 5) \cdot \operatorname{a308815}\left(n - 3\right) = 0$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/A308815DFiniteRecurrence.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a308815-dfinite-recurrence` (proved) by `D5/S1/Recurrence/A308815DFiniteRecurrence.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a308815-dfinite-recurrence","declaration_gid":"D5/S1/Recurrence/A308815DFiniteRecurrence.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* R. J. Mathar; OEIS Foundation Inc. (2020). *OEIS A308815 — D-finite recurrence for alternating Catalan numbers*. URL: <https://oeis.org/A308815>.

*Commentary.*

The ordinary Catalan series satisfies X C(X)^2-C(X)+1=0. Differentiation and elimination give X(1-4X)C'(X)+(1-2X)C(X)=1. The signed binomial sum is the coefficient of degree 2n in (1-2X)^n C(X). For n=m+3, the differential certificate X U'(X)-2(m+3)U(X) is a polynomial combination of the four shifted coefficient expressions, plus a forcing polynomial of degree at most m+5. Its degree-2(m+3) coefficient is zero: the Euler derivative cancels that coefficient, and m+5 < 2(m+3). Extracting coefficients and multiplying by 16^(m+3) produces the stated integer recurrence. The generating-function closed form and asymptotic formula are not proved by this module.

## References

- Truth anchor: `D5/S1/Recurrence/A308815DFiniteRecurrence.a308815`
- Truth anchor: `D5/S1/Recurrence/A308815DFiniteRecurrence.claim`
- Truth anchor: `D5/S1/Recurrence/A308815DFiniteRecurrence.result`
