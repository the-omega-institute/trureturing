# The Cohn Polynomial: A Uniform Three-Adic Obstruction

## Abstract

A uniform three-adic congruence and its obstruction for the explicit Cohn polynomial.

For a natural number q, put m=(q-1)/2 and define the integer polynomial P_q(T) as the sum, for 0<=k<=m, of binom(q,2k+1)(-3)^k(1+T)^(m-k). Write nu=v_3(q-1). The notation Dvd(a,b) below means integer divisibility. The hypotheses range over every q>=7 with q congruent to 1 modulo 6, including composite q, and every integer xi divisible by 3.

**Theorem 1.1 (The polynomial is the odd-power imaginary coordinate).**

$$\forall m \in \mathbb{N}, P_{2m+1}(X^{2}-1) = \operatorname{im}{z^{2m+1}}$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Congruence/CohnUniformThreeAdic.polynomial_identification` (`✓ std3`). ∎

*Citation.* J. H. E. Cohn (1993). *The Diophantine equation x^2+3=y^n*. DOI: [10.1017/S0017089500009757](https://doi.org/10.1017/S0017089500009757).

*Commentary.*

Here X is the polynomial indeterminate and z is X+sqrt(-3) in the quadratic algebra over Z[X]; P_q(X squared minus one) denotes polynomial composition. The identity holds for every natural m. The existing odd binomial expansion of the imaginary coordinate identifies each term after substituting X squared minus one into P_(2m+1). The evaluation hom evalQuadratic evaluates both coordinates at an integer a and commutes with powers. The Eisenstein reduction consumes this identity through that hom, without a second proof of the polynomial expansion.

**Theorem 1.2 (Uniform congruence of the actual polynomial).**

$$\forall q \in \mathbb{N}, \forall xi \in \mathbb{Z}, 7 \le q \Rightarrow q \operatorname{mod} 6 = 1 \Rightarrow dvd{3,xi} \Rightarrow dvd{3^{nu + 2}, P_{q}{xi} - 2^{q-1}}$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Congruence/CohnUniformThreeAdic.cohn_stationary_congruence` (`✓ std3`). ∎

*Citation.* J. H. E. Cohn (1993). *The Diophantine equation x^2+3=y^n*. DOI: [10.1017/S0017089500009757](https://doi.org/10.1017/S0017089500009757).

*Commentary.*

The proof identifies P_q(X^2-1) with the imaginary coordinate of (X+sqrt(-3))^q in the quadratic algebra over integer polynomials. Formal differentiation gives the second-order polynomial identity. For c_r=coeff(P_q,r) and d_r=r!c_r, it yields 16d_(r+2)=4(q-5r-3)d_(r+1)-(q-2r)(q-2r-1)d_r, with integer signed factors. The sixth power at X=1 gives c_0=2^(q-1) and c_1=0. Unbounded induction proves 3^nu divides d_r for every r>=1, including coefficients beyond the degree. Mathlib's strict factorial valuation bound then gives 3^(nu+2) dividing c_r xi^r for r>=2. Zero coefficients and xi=0 are handled before nonzero valuation formulas. The finite polynomial sum concludes the congruence. This is a polynomial and integer reformulation of Cohn's argument; there is no mathematical priority claim and no finite exponent cutoff.

**Theorem 1.3 (The value one is excluded).**

$$\forall q \in \mathbb{N}, \forall xi \in \mathbb{Z}, 7 \le q \Rightarrow q \operatorname{mod} 6 = 1 \Rightarrow dvd{3,xi} \Rightarrow \neg P_{q}{xi} = 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Congruence/CohnUniformThreeAdic.cohn_polynomial_ne_one` (`✓ std3`). ∎

*Citation.* J. H. E. Cohn (1993). *The Diophantine equation x^2+3=y^n*. DOI: [10.1017/S0017089500009757](https://doi.org/10.1017/S0017089500009757).

*Commentary.*

The actual polynomial congruence is consumed here. LTE at 4, 1 and (q-1)/2 gives v_3(2^(q-1)-1)=nu+1, while P_q(xi)=1 would make the same nonzero integer divisible by 3^(nu+2). EisensteinCohnReductionCore derives xi=a^2-1, divisibility of xi by three, and P_q(xi)=1 from the remaining odd-prime power equation. That reduction handles q=3 and even exponents directly, and combines this obstruction with the prime-divisor reduction to exclude x^2+3=y^e for all integers x>=2 and y and all natural e>=2.

## References

- Truth anchor: `D5/S3/Arith/Congruence/CohnUniformThreeAdic.cohn_polynomial_ne_one`
- Truth anchor: `D5/S3/Arith/Congruence/CohnUniformThreeAdic.cohn_stationary_congruence`
- Truth anchor: `D5/S3/Arith/Congruence/CohnUniformThreeAdic.polynomial_identification`
