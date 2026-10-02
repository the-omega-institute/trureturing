# The closed form of the higher-antibracket coefficients

## Abstract

For every n >= 2, the coefficients c_1^n, ..., c_n^n that express the higher Koszul bracket Phi^(n+1) through the operators rho_1, ..., rho_n are given by the closed formula conjectured by M. Manetti and G. Ricciardi (arXiv:1509.09032, Conjecture 2.4), and (-1)^n c_i^n > 0. The identity is the one of their Theorem 6.4, stated for linear endomorphisms of Q[x].

**Definition 1.1 (The operators Phi^(m,i)).**

$$\forall m : \mathbb{N}, \forall i : \mathbb{N}, \forall s : \mathbb{N}, \operatorname{phi}\left(m, i, x^{s}\right) = \operatorname{ite}\left(s = i, \frac{x^{m - i}}{(m - i)!}, 0\right)$$

*Formalization.* `D5/S3/HomologicalAlgebra/HigherAntibracketCoefficients.phi` (`✓ std3`).

*Citation.* Marco Manetti; Giulia Ricciardi (2016). *Universal Lie Formulas for Higher Antibrackets*. DOI: [10.3842/SIGMA.2016.053](https://doi.org/10.3842/SIGMA.2016.053). URL: <https://arxiv.org/abs/1509.09032v3>.

*Commentary.*

Phi^(m,i) is the linear endomorphism of Q[x] sending x^i to x^(m-i)/(m-i)! and every other monomial to 0.

**Definition 1.2 (The higher Koszul brackets).**

$$\forall m : \mathbb{N}, \operatorname{koszul}\left(m\right) = \sum_{i=1}^{m} (-1)^{m - i} \cdot \operatorname{phi}\left(m, i\right)$$

*Formalization.* `D5/S3/HomologicalAlgebra/HigherAntibracketCoefficients.koszul` (`✓ std3`).

*Citation.* Marco Manetti; Giulia Ricciardi (2016). *Universal Lie Formulas for Higher Antibrackets*. DOI: [10.3842/SIGMA.2016.053](https://doi.org/10.3842/SIGMA.2016.053). URL: <https://arxiv.org/abs/1509.09032v3>.

*Commentary.*

Phi^m is the alternating sum of the operators Phi^(m,i) with signs (-1)^(m-i), for i from 1 to m.

**Definition 1.3 (The operators rho_k).**

$$\forall k : \mathbb{N}, \forall \psi : \operatorname{End}\left(\mathbb{Q}[x]\right), \operatorname{rho}\left(k, \psi\right) = (\frac{x^{k}}{(k)!} - \frac{x^{k + 1} \cdot \operatorname{D}}{(k + 1)!}) \circ \psi - \psi \circ (\frac{x \cdot \operatorname{D}^{k + 1}}{(k + 1)!})$$

*Formalization.* `D5/S3/HomologicalAlgebra/HigherAntibracketCoefficients.rho` (`✓ std3`).

*Citation.* Marco Manetti; Giulia Ricciardi (2016). *Universal Lie Formulas for Higher Antibrackets*. DOI: [10.3842/SIGMA.2016.053](https://doi.org/10.3842/SIGMA.2016.053). URL: <https://arxiv.org/abs/1509.09032v3>.

*Commentary.*

For a linear endomorphism Psi of Q[x], rho_k(Psi) is the composition of (x^k/k! - x^(k+1) D/(k+1)!) with Psi, minus the composition of Psi with x D^(k+1)/(k+1)!, where D is the derivative of polynomials.

**Definition 1.4 (The conjectured coefficient).**

$$\forall n : \mathbb{N}, \forall i : \mathbb{N}, \operatorname{formula}\left(n, i\right) = \frac{(-1)^{n} \cdot \prod_{j=2}^{i} \frac{n \cdot (n - 1) - (j - 1) \cdot (j - 2)}{2}}{\sum_{h=2}^{n} h \cdot (\prod_{j=2}^{h} \frac{n \cdot (n - 1) - (j - 1) \cdot (j - 2)}{2}) \cdot \prod_{j=h}^{n - 1} \frac{(1 - j) \cdot (j + 2)}{2}}$$

*Formalization.* `D5/S3/HomologicalAlgebra/HigherAntibracketCoefficients.formula` (`✓ std3`).

*Citation.* Marco Manetti; Giulia Ricciardi (2016). *Universal Lie Formulas for Higher Antibrackets*. DOI: [10.3842/SIGMA.2016.053](https://doi.org/10.3842/SIGMA.2016.053). URL: <https://arxiv.org/abs/1509.09032v3>.

*Commentary.*

The coefficient printed in the conjecture: (-1)^n times the product over j from 2 to i of (n(n-1) - (j-1)(j-2))/2, divided by the sum over h from 2 to n of h times the same product up to h times the product over j from h to n-1 of (1-j)(j+2)/2. Empty products are 1.

**Definition 1.5 (The conjecture).**

$$claim \Leftrightarrow (\forall n : \mathbb{N}, 2 \le n \Rightarrow \left((\forall c : \mathbb{N} \to \mathbb{Q}, \operatorname{koszul}\left(n + 1\right) = \sum_{i=1}^{n} c_{i} \cdot \left(\operatorname{rho}_{1}\right)^{n - i}(\operatorname{rho}\left(i, \operatorname{koszul}\left(1\right)\right)) \Leftrightarrow (\forall i : \mathbb{N}, ((1 \le i) \land i \le n) \Rightarrow c_{i} = \operatorname{formula}\left(n, i\right))) \land \forall i : \mathbb{N}, ((1 \le i) \land i \le n) \Rightarrow 0 < (-1)^{n} \cdot \operatorname{formula}\left(n, i\right)\right))$$

*Formalization.* `D5/S3/HomologicalAlgebra/HigherAntibracketCoefficients.claim` (`✓ std3`).

*Citation.* Marco Manetti; Giulia Ricciardi (2016). *Universal Lie Formulas for Higher Antibrackets*. DOI: [10.3842/SIGMA.2016.053](https://doi.org/10.3842/SIGMA.2016.053). URL: <https://arxiv.org/abs/1509.09032v3>.

*Commentary.*

For every n >= 2, a sequence c satisfies Phi^(n+1) = c_1 rho_1^n Phi^1 + c_2 rho_1^(n-2) rho_2 Phi^1 + ... + c_n rho_n Phi^1 exactly when c_i equals the printed coefficient for 1 <= i <= n, and (-1)^n times that coefficient is positive. Here rho_1^(n-i) applies rho_1 n - i times. The paper proves that this identity has a unique solution and that the coefficients of its Theorem 2.3 are that solution.

**Theorem 1.6 (The closed form holds).**

$$claim$$

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/HigherAntibracketCoefficients.result` (`✓ std3`). ∎

*Resolves.* `Problems/manetti-ricciardi-2015-higher-antibracket-coefficients` (proved) by `D5/S3/HomologicalAlgebra/HigherAntibracketCoefficients.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"manetti-ricciardi-2015-higher-antibracket-coefficients","declaration_gid":"D5/S3/HomologicalAlgebra/HigherAntibracketCoefficients.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Marco Manetti; Giulia Ricciardi (2016). *Universal Lie Formulas for Higher Antibrackets*. DOI: [10.3842/SIGMA.2016.053](https://doi.org/10.3842/SIGMA.2016.053). URL: <https://arxiv.org/abs/1509.09032v3>.

*Commentary.*

Write an operator through its values on monomials and record the coefficient of x^d/d! in its value at x^s as the lattice point (d, s). Then rho_k sends (d, s) to alpha_k(d) (d + k, s) - C(s + k, k + 1) (d, s + k) with alpha_k(d) = C(d + k, k) - C(d + k, k + 1), and rho_i Phi^1 = (i, 1) - (0, i + 1). The two moves of rho_1 commute, so rho_1^t expands binomially along products of the step weights. The identity becomes n + 1 linear equations in c, one for each lattice point (d, n + 1 - d). Since alpha_1(2) = 0, the equations for d >= 3 form a triangular system in c_3, ..., c_n, and those for d = 0 and d = 1 then fix c_1 and c_2, which gives uniqueness. For c_i = (-1)^n (n+i-2)! / ((n-i)! 2^(i-1)) divided by (n-2)! (n+1)! / 2^(n-1), every equation reduces to the alternating binomial sum over i of (-1)^(M-i) C(M, i) C(i + a, b), which is C(a, b - M) for M <= b and 0 otherwise. The same sum shows that the printed product and denominator equal these factorial expressions for n >= 3; the case n = 2 is computed directly and gives c_1 = c_2 = 1/2.

## References

- Truth anchor: `D5/S3/HomologicalAlgebra/HigherAntibracketCoefficients.claim`
- Truth anchor: `D5/S3/HomologicalAlgebra/HigherAntibracketCoefficients.formula`
- Truth anchor: `D5/S3/HomologicalAlgebra/HigherAntibracketCoefficients.koszul`
- Truth anchor: `D5/S3/HomologicalAlgebra/HigherAntibracketCoefficients.phi`
- Truth anchor: `D5/S3/HomologicalAlgebra/HigherAntibracketCoefficients.result`
- Truth anchor: `D5/S3/HomologicalAlgebra/HigherAntibracketCoefficients.rho`
