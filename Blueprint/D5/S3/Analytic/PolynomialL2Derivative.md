# Complex Polynomial L2 Derivative Energy

## Abstract

Shifted Legendre orthogonality bounds complex polynomial derivative energy by a fourth power of the dimension.

**Definition 1.1 (The actual shifted Legendre family).**

Lean statement: `D5/S3/Analytic/PolynomialL2Derivative.legendreC`

*Formalization.* `D5/S3/Analytic/PolynomialL2Derivative.legendreC` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every natural n, legendreC(n) is Mathlib's integer shifted Legendre polynomial mapped by the integer cast ring homomorphism to complex coefficients. Both derivative energy and moment-orthogonal approximation use this same family.

**Definition 1.2 (Bilinear polynomial integration).**

Lean statement: `D5/S3/Analytic/PolynomialL2Derivative.moment`

*Formalization.* `D5/S3/Analytic/PolynomialL2Derivative.moment` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every pair of complex polynomials p,q, moment(p,q) is the integral from zero to one of p(x)q(x), with real inputs cast to the complex numbers. The operation is bilinear; Hermitian pairing is obtained by explicitly conjugating the second polynomial's coefficients.

**Definition 1.3 (Finite expansion with an arbitrary coefficient sequence).**

Lean statement: `D5/S3/Analytic/PolynomialL2Derivative.expansion`

*Formalization.* `D5/S3/Analytic/PolynomialL2Derivative.expansion` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every natural d and every sequence a from the naturals to the complex numbers, expansion(d,a) is the polynomial sum_(n<d) C(a_n) legendreC(n). The sequence remains unrestricted outside the finite sum; at d=0 the expansion is the zero polynomial.

**Theorem 1.4 (The degree formulation includes the zero-dimensional space).**

Lean statement: `D5/S3/Analytic/PolynomialL2Derivative.complex_polynomial_derivative_l2_of_degree`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/PolynomialL2Derivative.complex_polynomial_derivative_l2_of_degree` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural d and every polynomial p with arbitrary complex coefficients and degree(p)<d in WithBot(Nat), the integral from zero to one of norm(p'(x)) squared is at most d^4 times the integral of norm(p(x)) squared. Evaluation uses the real input embedded in the complex numbers, and both integrals use real Lebesgue measure. There is no nonzero polynomial hypothesis. At d=0 the degree premise forces p=0, and the same statement gives the zero-energy boundary case.

The proof maps Mathlib's integer shifted Legendre polynomials to complex polynomials L_n. In this convention L_n(0)=1 and L_n(1)=(-1)^n. Rodrigues' identity is n! L_n=D^n[X^n(1-X)^n]. Every derivative of the Rodrigues primitive of order below n vanishes at both endpoints, by divisibility by the remaining positive powers of X and 1-X. Repeated integration by parts transfers n derivatives onto a test polynomial. Its derivative vanishes when its degree is below n, which proves lower-degree orthogonality.

The beta integral of x^n(1-x)^n is n!^2/(2n+1)!. Together with the leading coefficient this gives the exact squared L2 norm integral norm(L_n(x))^2 dx=1/(2n+1). Conjugation is retained explicitly: mapping the coefficients by complex conjugation conjugates the value at real x, while L_n itself has real coefficients. Thus orthogonality is Hermitian orthogonality for arbitrary complex coefficients, rather than only a real-coefficient calculation.

One more integration by parts expresses the derivative energy through endpoint values; the integral involving L_n'' vanishes by the proved lower-degree orthogonality. The endpoint derivatives are L_n'(0)=-n(n+1) and L_n'(1)=(-1)^n n(n+1). Consequently the exact derivative energy is integral norm(L_n')^2=2n(n+1), also for n=0.

The polynomial-sequence spanning theorem supplies an expansion p=sum_(n<d) a_n L_n for every polynomial of degree below d, including the empty expansion at d=0. Explicit conjugation gives Parseval: E(p)=integral norm(p)^2=sum_(n<d) norm(a_n)^2/(2n+1). Weighted finite Cauchy-Schwarz bounds norm(p'(x))^2 by E(p) times sum_(n<d) (2n+1) norm(L_n'(x))^2. Integrating that finite density gives sum_(n<d) (2n+1)2n(n+1)=d^2(d^2-1), at most d^4. Continuity supplies each integrability premise. No exponential coefficient estimate or assumed analytic budget enters this proof.

This source combines classical Rodrigues orthogonality, beta normalization, polynomial spanning and Cauchy-Schwarz, reusing the pinned Mathlib shifted-Legendre, integration-by-parts and beta APIs. No literature originality claim is made. The spanning and mixed expansion identities also support the finite primitive estimate below.

**Theorem 1.5 (The dimension-bounded form and the pending reciprocal-tail use).**

Lean statement: `D5/S3/Analytic/PolynomialL2Derivative.complex_polynomial_derivative_l2`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/PolynomialL2Derivative.complex_polynomial_derivative_l2` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural d with 1<=d and every complex polynomial p with natDegree(p)<d, the same derivative energy is at most d^4 E(p). All four source binders d, the proof of 1<=d, p and the degree proof are retained. The zero polynomial is allowed, as are arbitrary complex coefficients. The proof applies the degree theorem using degree(p)<=natDegree(p); it introduces no further analytic assumption.

For the pending actual reciprocal-tail application, the energy estimate supplies a polynomial variation allowance. Writing g(x)=norm(p(x))^2, the classical product rule and integral Cauchy-Schwarz give integral abs(g')<=2 sqrt(E(p') E(p))<=2d^2 E(p). In particular, an energy-normalized polynomial contributes at most 2d^2 to this variation allowance. For two polynomials p and q the same reasoning bounds the variation of p times conjugate(q) by (d_p^2+d_q^2) sqrt(E(p) E(q)), under their respective degree bounds. These are application derivations in the narrative; this module does not export separate Lean variation theorems.

If the actual reciprocal factor r in that consumer is continuously differentiable on the integration interval and has bounds norm(r)<=M and norm(r')<=N there, the product rule gives integral norm((r g)')<=(2M d^2+N) E(p). For r=1/F these bounds require an actual positive lower bound on norm(F) and control of F'; reciprocal differentiation alone does not supply them. A signed tail argument must also supply its actual primitive or cumulative tail bound and the integration-by-parts boundary terms. This polynomial estimate pays the polynomial part of that calculation; it does not construct the actual reciprocal, its tail, or an enclosure.

The substantive actual reciprocal consumer remains uncompiled and pending. Its exact definitions, nonvanishing hypotheses, tail bounds, endpoint costs and final enclosure still require native verification in the consuming development. This Reg/Scribe component is intended for integration with that actual consumer. No formal Riemann-hypothesis or Robin implication is established here.

**Theorem 1.6 (Polynomial spanning).**

Lean statement: `D5/S3/Analytic/PolynomialL2Derivative.exists_expansion`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/PolynomialL2Derivative.exists_expansion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural d and every complex polynomial p with degree(p)<d, there exists a full complex coefficient sequence a such that sum_(n<d) a_n L_n=p. This spanning identity is used by the derivative estimate and corrected polynomial approximation.

**Theorem 1.7 (Continuity of real polynomial evaluation).**

Lean statement: `D5/S3/Analytic/PolynomialL2Derivative.eval_continuous`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/PolynomialL2Derivative.eval_continuous` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every complex polynomial p, the function from real x to p(x), using the complex embedding, is continuous. The actual primitive flux estimate consumes this continuity.

**Theorem 1.8 (Left scalar multiplication in a bilinear moment).**

Lean statement: `D5/S3/Analytic/PolynomialL2Derivative.moment_C_mul_left`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/PolynomialL2Derivative.moment_C_mul_left` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every complex scalar a and complex polynomials p,q, moment(C(a)p,q)=a moment(p,q). The mixed expansion uses this existing bilinearity identity.

**Theorem 1.9 (Integration by parts for polynomial moments).**

Lean statement: `D5/S3/Analytic/PolynomialL2Derivative.moment_derivative`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/PolynomialL2Derivative.moment_derivative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every pair of complex polynomials p,q, moment(p′,q)=p(1)q(1)-p(0)q(0)-moment(p,q′). Polynomial continuity supplies the analytic hypotheses. Weighted Sturm energy consumes this identity.

**Theorem 1.10 (Evaluation after coefficient conjugation).**

Lean statement: `D5/S3/Analytic/PolynomialL2Derivative.eval_map_conj`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/PolynomialL2Derivative.eval_map_conj` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every complex polynomial p and real x, evaluation of the coefficient conjugate of p at x equals conjugate(p(x)). Weighted energy retains this Hermitian pairing.

**Theorem 1.11 (The actual complex shifted Legendre coefficients).**

Lean statement: `D5/S3/Analytic/PolynomialL2Derivative.coeff_legendreC`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/PolynomialL2Derivative.coeff_legendreC` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For all natural n,k, coefficient k of legendreC(n) is (-1)^k choose(n,k) choose(n+k,n), as a complex number. The finite Sturm recurrence uses this existing coefficient formula, including coefficients outside the degree range.

**Theorem 1.12 (Finite additivity of polynomial moments).**

Lean statement: `D5/S3/Analytic/PolynomialL2Derivative.moment_sum_left`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/PolynomialL2Derivative.moment_sum_left` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite set s of naturals, polynomial sequence p and complex polynomial q, moment(sum_(i in s) p_i,q)=sum_(i in s) moment(p_i,q). The finite mixed expansion consumes this equality.

**Theorem 1.13 (Coefficient conjugation of a finite expansion).**

Lean statement: `D5/S3/Analytic/PolynomialL2Derivative.expansion_map_conj`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/PolynomialL2Derivative.expansion_map_conj` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural d and complex sequence a, coefficient conjugation of expansion(d,a) is expansion(d,conjugate(a)). The mixed expansion consumes the full sequence identity.

**Theorem 1.14 (A row of Legendre orthogonality).**

Lean statement: `D5/S3/Analytic/PolynomialL2Derivative.moment_expansion_row`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/PolynomialL2Derivative.moment_expansion_row` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every d,i and complex sequence a with i in range(d), moment(legendreC(i),expansion(d,conjugate(a)))=conjugate(a_i)/(2i+1). The mixed expansion consumes the existing normalization and orthogonality.

**Definition 1.15 (Legendre normalization weights).**

Lean statement: `D5/S3/Analytic/PolynomialL2Derivative.weight`

*Formalization.* `D5/S3/Analytic/PolynomialL2Derivative.weight` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For each natural k, weight(k)=2k+1 is the positive real normalization denominator. The high-mode coefficient gap consumes these weights.

**Definition 1.16 (Finite coefficient energy).**

Lean statement: `D5/S3/Analytic/PolynomialL2Derivative.coefficientEnergy`

*Formalization.* `D5/S3/Analytic/PolynomialL2Derivative.coefficientEnergy` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every natural d and complex sequence a, coefficientEnergy(d,a)=sum_(i<d) norm(a_i)^2/(2i+1). The inverse Sturm estimate uses the same finite energy as the original Parseval identity.

**Theorem 1.17 (Exact complex finite Parseval identity).**

Lean statement: `D5/S3/Analytic/PolynomialL2Derivative.expansion_parseval`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/PolynomialL2Derivative.expansion_parseval` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural d and complex sequence a, the integral from zero to one of norm(expansion(d,a)(x))^2 equals coefficientEnergy(d,a). The empty expansion is included. The finite primitive estimate consumes this existing equality.

## References

- Truth anchor: `D5/S3/Analytic/PolynomialL2Derivative.coeff_legendreC`
- Truth anchor: `D5/S3/Analytic/PolynomialL2Derivative.coefficientEnergy`
- Truth anchor: `D5/S3/Analytic/PolynomialL2Derivative.complex_polynomial_derivative_l2`
- Truth anchor: `D5/S3/Analytic/PolynomialL2Derivative.complex_polynomial_derivative_l2_of_degree`
- Truth anchor: `D5/S3/Analytic/PolynomialL2Derivative.eval_continuous`
- Truth anchor: `D5/S3/Analytic/PolynomialL2Derivative.eval_map_conj`
- Truth anchor: `D5/S3/Analytic/PolynomialL2Derivative.exists_expansion`
- Truth anchor: `D5/S3/Analytic/PolynomialL2Derivative.expansion`
- Truth anchor: `D5/S3/Analytic/PolynomialL2Derivative.expansion_map_conj`
- Truth anchor: `D5/S3/Analytic/PolynomialL2Derivative.expansion_parseval`
- Truth anchor: `D5/S3/Analytic/PolynomialL2Derivative.legendreC`
- Truth anchor: `D5/S3/Analytic/PolynomialL2Derivative.moment`
- Truth anchor: `D5/S3/Analytic/PolynomialL2Derivative.moment_C_mul_left`
- Truth anchor: `D5/S3/Analytic/PolynomialL2Derivative.moment_derivative`
- Truth anchor: `D5/S3/Analytic/PolynomialL2Derivative.moment_expansion_row`
- Truth anchor: `D5/S3/Analytic/PolynomialL2Derivative.moment_sum_left`
- Truth anchor: `D5/S3/Analytic/PolynomialL2Derivative.weight`
