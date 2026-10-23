# An odd midpoint counterexample to Fiore-Nasr-Stone Conjecture 6.8

## Abstract

At the distinct odd primes three, five and eleven, both complete midpoint polynomials have nonnegative integer coefficients.

Fiore, Nasr and Stone define, for distinct primes p, q and r and exponents a, b, c and d in {0,1,2}, A_abcd = X Phi_p^2 Phi_q^2 Phi_pq^a Phi_pr^b Phi_qr^c Phi_pqr^d and B_abcd = X Phi_r^2 Phi_pq^a Phi_pr^b Phi_qr^c Phi_pqr^d. They pair A_abcd with B_(2-a,2-b,2-c,2-d). At a=b=c=d=1 the complementary exponents are also one. Every factor, including the initial X, is retained below.

Conjecture 6.8 states: "In the remaining 33 pairs of the polynomials A_abcd and B_(2-a,2-b,2-c,2-d) (including the case where p != 2 for when a=b=c=d=1), one of the two polynomials will have a negative coefficient."

The closed assertion below is precisely this explicitly included universal midpoint clause. The primes 3, 5 and 11 are pairwise distinct and meet p != 2; they are also all odd and satisfy p<q<r. The source conjecture therefore requires a negative coefficient for this very pair. Showing that both polynomials have no negative coefficient contradicts that required instance and refutes the whole conjecture. This implication does not identify the midpoint clause with the complete remaining-case assertion or classify any other exponent tuple.

**Definition 1.1 (The first complete midpoint polynomial).**

Lean statement: `D5/S3/Factorization/Cyclotomic/FioreNasrStoneMidpointRefutation.midpointA`

*Formalization.* `D5/S3/Factorization/Cyclotomic/FioreNasrStoneMidpointRefutation.midpointA` (`✓ std3`).

*Citation.* Evelyn Fiore, George D. Nasr, and Cooper Stone (2026). *Dice Relabeling using Square-Sided Dice*. URL: <https://arxiv.org/html/2606.20311v1>.

*Commentary.*

For natural parameters p, q and r, midpointA is the integer polynomial X Phi_p^2 Phi_q^2 Phi_pq Phi_pr Phi_qr Phi_pqr from Definition 6.1.

**Definition 1.2 (The complementary midpoint polynomial).**

Lean statement: `D5/S3/Factorization/Cyclotomic/FioreNasrStoneMidpointRefutation.midpointB`

*Formalization.* `D5/S3/Factorization/Cyclotomic/FioreNasrStoneMidpointRefutation.midpointB` (`✓ std3`).

*Citation.* Evelyn Fiore, George D. Nasr, and Cooper Stone (2026). *Dice Relabeling using Square-Sided Dice*. URL: <https://arxiv.org/html/2606.20311v1>.

*Commentary.*

For the same natural parameters, midpointB is the integer polynomial X Phi_r^2 Phi_pq Phi_pr Phi_qr Phi_pqr. All four complementary mixed exponents equal one.

**Definition 1.3 (The explicit universal midpoint assertion).**

Lean statement: `D5/S3/Factorization/Cyclotomic/FioreNasrStoneMidpointRefutation.claim`

*Formalization.* `D5/S3/Factorization/Cyclotomic/FioreNasrStoneMidpointRefutation.claim` (`✓ std3`).

*Citation.* Evelyn Fiore, George D. Nasr, and Cooper Stone (2026). *Dice Relabeling using Square-Sided Dice*. URL: <https://arxiv.org/html/2606.20311v1>.

*Commentary.*

For every triple of natural primes p, q and r, pairwise distinct with p != 2, claim requires some natural-index coefficient of midpointA or midpointB to be strictly negative. The two existential indices are independent and range over all natural numbers. There is no prime-order premise.

**Theorem 1.4 (The explicit midpoint assertion is false).**

Lean statement: `D5/S3/Factorization/Cyclotomic/FioreNasrStoneMidpointRefutation.result`

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Cyclotomic/FioreNasrStoneMidpointRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/fiore-nasr-stone-2026-midpoint-negativity` (refuted) by `D5/S3/Factorization/Cyclotomic/FioreNasrStoneMidpointRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"fiore-nasr-stone-2026-midpoint-negativity","declaration_gid":"D5/S3/Factorization/Cyclotomic/FioreNasrStoneMidpointRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Evelyn Fiore, George D. Nasr, and Cooper Stone (2026). *Dice Relabeling using Square-Sided Dice*. URL: <https://arxiv.org/html/2606.20311v1>.

*Commentary.*

Write G_m(X) for the finite sum of X^j over 0 <= j < m. Cyclotomic factorization and expansion give the complete polynomial identity A(3,5,11) = X G_3(X) G_5(X) G_3(X^11) G_5(X^33). For the second polynomial they give B(3,5,11) = X (Phi_11(X) Phi_15(X)) G_11(X^15).

The remaining product Phi_11(X) Phi_15(X) equals the sum of X^s for s in {0,3,5,6,8,9,10,12,13,15,18}. The signed expansion of Phi_15 is the existing identity Counterexample.cyclotomic_15. Multiplication by G_11 cancels all its negative coefficients. Every displayed sum has nonnegative coefficients. The coefficient of a product is a finite sum of products of coefficients, and substitution X -> X^k inserts zeros. These laws establish nonnegativity at every natural index, including the zero tails.

The geometric-sum identity is supplied by GeometricSpectrumFactorization.geometric_sum_eq_cyclotomic_product; Polynomial.cyclotomic_expand_eq_cyclotomic_mul supplies each prime expansion. The factor identities and coefficient arguments are all inside this single result.

Table 2 repeats the tuple (2,1,1,2), so the printed number 33 does not define a verified remaining domain. Lemma 6.6 asserts an odd-prime obstruction using the claim that sums of odd-prime multiples are always even; 11=2*3+5 disproves that step. Its classification is not used here. The midpoint is explicitly included in Conjecture 6.8 regardless of these defects. The other exponent cases, a corrected classification, and physical realization of dice remain outside this theorem.

## References

- Truth anchor: `D5/S3/Factorization/Cyclotomic/FioreNasrStoneMidpointRefutation.claim`
- Truth anchor: `D5/S3/Factorization/Cyclotomic/FioreNasrStoneMidpointRefutation.midpointA`
- Truth anchor: `D5/S3/Factorization/Cyclotomic/FioreNasrStoneMidpointRefutation.midpointB`
- Truth anchor: `D5/S3/Factorization/Cyclotomic/FioreNasrStoneMidpointRefutation.result`
- Dependency: [D5/S3/Factorization/Cyclotomic/GeometricSpectrumFactorization](GeometricSpectrumFactorization.md)
