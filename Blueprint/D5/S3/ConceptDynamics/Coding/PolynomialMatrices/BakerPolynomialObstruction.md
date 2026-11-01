# Baker polynomial obstruction

## Abstract

The Baker polynomial pair admits neither coupled lag witnesses nor a finite rectangular exchange chain over the natural-coefficient polynomial semiring.

The coefficient semiring is Polynomial Nat, equivalently polynomials with nonnegative integer coefficients. A and B below are fixed two by two matrices. The source question occurs in Emmanuel Jeandel, Combinatorial Search for Strong Shift Equivalence, arXiv:2609.03567v1, archived SSE.tex lines 731-738, after the end of the rendered document at line 628. It is an externally authored archived draft question, without a published rendered problem number.

**Definition 1.1 (First endpoint).**

Lean statement: `D5/S3/ConceptDynamics/Coding/PolynomialMatrices/BakerPolynomialObstruction.A`

*Formalization.* `D5/S3/ConceptDynamics/Coding/PolynomialMatrices/BakerPolynomialObstruction.A` (`✓ std3`).

*Citation.* Emmanuel Jeandel (2026). *Combinatorial Search for Strong Shift Equivalence*. URL: <https://arxiv.org/abs/2609.03567v1>.

*Commentary.*

A has rows (1, X+1) and (X, 1), with every entry in Polynomial Nat.

**Definition 1.2 (Second endpoint).**

Lean statement: `D5/S3/ConceptDynamics/Coding/PolynomialMatrices/BakerPolynomialObstruction.B`

*Formalization.* `D5/S3/ConceptDynamics/Coding/PolynomialMatrices/BakerPolynomialObstruction.B` (`✓ std3`).

*Citation.* Emmanuel Jeandel (2026). *Combinatorial Search for Strong Shift Equivalence*. URL: <https://arxiv.org/abs/2609.03567v1>.

*Commentary.*

B has rows (1, X^2+X) and (1, 1), with every entry in Polynomial Nat.

**Theorem 1.3 (No coupled lag witnesses).**

$$\forall n \in \mathit{Nat},\; \neg \left(\exists R \in \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \operatorname{Polynomial}\left(\mathit{Nat}\right)\right),\; \exists S \in \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \operatorname{Polynomial}\left(\mathit{Nat}\right)\right),\; A \cdot R = R \cdot B \land \left(B \cdot S = S \cdot A \land \left(R \cdot S = \operatorname{pow}\left(A, n\right) \land S \cdot R = \operatorname{pow}\left(B, n\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/PolynomialMatrices/BakerPolynomialObstruction.no_lag` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural number n, including zero, there are no two by two matrices R,S over Polynomial Nat satisfying all four equations AR=RB, BS=SA, RS=A^n, SR=B^n. There are no additional positivity, invertibility, degree, nonzero-entry or positive-lag hypotheses.

The intertwining equations force R to have rows (a,(X+1)c),(c,Xa), and S to have rows (Xh,(X+1)g),(g,h). Map coefficients injectively into the rationals. The determinant of A is p=1-X-X^2. Its irreducibility follows directly from dbonacci_irreducible at order two, the existing negated-indeterminate automorphism, and multiplication by the unit -1. The determinant equation forces both intertwiner determinants to be nonzero divisors of p^n and hence to have even degree.

Each determinant has the form Xf^2-(X+1)k^2. If it is nonzero of even degree, both inputs are nonzero and have equal degree: otherwise its highest surviving term has odd degree. Back over natural coefficients, sums cannot cancel their leading terms. The two entries in the first row of RS therefore have the same degree and its upper-right entry is nonzero. The recurrence d(n+1)=d(n)+X*u(n), u(n+1)=(X+1)*d(n)+u(n) for the first row of A^n proves their degrees differ by one at every positive n. This contradicts RS=A^n; for n=0 its upper-right entry contradicts the identity matrix.

The proof combines determinant-degree parity with the positive-coefficient product and power recurrences. It does not require the fourth equation once the other three have been assumed.

**Theorem 1.4 (No finite rectangular exchange chain).**

$$\forall L \in \mathit{Nat},\; \neg \operatorname{ExchangeChain}\left(\operatorname{Polynomial}\left(\mathit{Nat}\right), A, B, L\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/PolynomialMatrices/BakerPolynomialObstruction.no_exchange_chain` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural length L, ExchangeChain (Polynomial Nat) A B L is impossible. The existing exchange_chain_lag theorem supplies the same coupled witnesses at lag L for any such chain, so no restriction on any finite rectangular intermediate dimension is introduced. Zero length remains included.

The source-qualified negative answer concerns precisely the archived draft polynomial question. It asserts no general result about integer evaluations of Baker matrices, polynomials with real coefficients, priority, uniqueness, or an unqualified solved published problem.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Coding/PolynomialMatrices/BakerPolynomialObstruction.A`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PolynomialMatrices/BakerPolynomialObstruction.B`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PolynomialMatrices/BakerPolynomialObstruction.no_exchange_chain`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PolynomialMatrices/BakerPolynomialObstruction.no_lag`
- Dependency: [D5/S0/Tower/DBonacci/Irreducibility](../../../../S0/Tower/DBonacci/Irreducibility.md)
- Dependency: [D5/S3/ConceptDynamics/Coding/RectangularNilpotenceBarrier](../RectangularNilpotenceBarrier.md)
