# Bottom heaviness of q-Stirling coefficients

## Abstract

All four unshifted unsigned q-Stirling families have bottom-heavy coefficients.

**Definition 1.1 (Type A, second kind).**

$$\forall n \in \mathbb{N},\; \forall k \in \mathbb{Z},\; (\operatorname{S}\left(0, k\right) = \operatorname{ite}\left(k = 0, 1, 0\right)) \land (\operatorname{S}\left(n + 1, k\right) = \operatorname{ite}\left(k < 0, 0, \operatorname{S}\left(n, k - 1\right) + \operatorname{D5.S0.Certificates.Polynomials.QProductNecessityRefutation.qInteger} (\operatorname{Int.toNat} (k)) \cdot \operatorname{S}\left(n, k\right)\right))$$

*Formalization.* `D5/S3/Combinatorics/QStirling/SaganSwansonBottomHeavy.S` (`✓ std3`).

*Citation.* Bruce E. Sagan and Joshua P. Swanson (2022). *q-Stirling numbers in type B*. DOI: [10.1016/j.ejc.2023.103899](https://doi.org/10.1016/j.ejc.2023.103899). URL: <https://arxiv.org/abs/2205.14078v1>.

*Commentary.*

Section 1.1, equation (2), printed page 3: “We will call the (type A) q-Stirling numbers of the second kind the polynomials S[n, k] in the variable q obtained by replacing (1) with S[n,k] = S[n−1,k−1]+[k] S[n−1,k].” The initial row is the Kronecker delta at zero. Here n ranges over Nat, k over Int, and the polynomial variable is Polynomial.X over Nat. Negative k gives zero. The existing qInteger is the sum of X^j for j < a.

**Definition 1.2 (Type A, first kind).**

$$\forall n \in \mathbb{N},\; \forall k \in \mathbb{Z},\; (\operatorname{c}\left(0, k\right) = \operatorname{ite}\left(k = 0, 1, 0\right)) \land (\operatorname{c}\left(n + 1, k\right) = \operatorname{c}\left(n, k - 1\right) + \operatorname{D5.S0.Certificates.Polynomials.QProductNecessityRefutation.qInteger} (n) \cdot \operatorname{c}\left(n, k\right))$$

*Formalization.* `D5/S3/Combinatorics/QStirling/SaganSwansonBottomHeavy.c` (`✓ std3`).

*Citation.* Bruce E. Sagan and Joshua P. Swanson (2022). *q-Stirling numbers in type B*. DOI: [10.1016/j.ejc.2023.103899](https://doi.org/10.1016/j.ejc.2023.103899). URL: <https://arxiv.org/abs/2205.14078v1>.

*Commentary.*

Section 1.1, equation (5), printed page 4: “The (signless, type A) q-Stirling numbers of the first kind are the polynomials c[n, k] obtained by replacing (4) with c[n,k]=c[n−1,k−1]+[n−1] c[n−1,k].” The initial row is the Kronecker delta at zero. The displayed successor row has multiplier qInteger n.

**Definition 1.3 (Type B, second kind).**

$$\forall n \in \mathbb{N},\; \forall k \in \mathbb{Z},\; (\operatorname{SB}\left(0, k\right) = \operatorname{ite}\left(k = 0, 1, 0\right)) \land (\operatorname{SB}\left(n + 1, k\right) = \operatorname{ite}\left(k < 0, 0, \operatorname{SB}\left(n, k - 1\right) + \operatorname{D5.S0.Certificates.Polynomials.QProductNecessityRefutation.qInteger} (\operatorname{Int.toNat} (2 \cdot k + 1)) \cdot \operatorname{SB}\left(n, k\right)\right))$$

*Formalization.* `D5/S3/Combinatorics/QStirling/SaganSwansonBottomHeavy.SB` (`✓ std3`).

*Citation.* Bruce E. Sagan and Joshua P. Swanson (2022). *q-Stirling numbers in type B*. DOI: [10.1016/j.ejc.2023.103899](https://doi.org/10.1016/j.ejc.2023.103899). URL: <https://arxiv.org/abs/2205.14078v1>.

*Commentary.*

Definition 1.5, equation (8), printed page 6: “The type B q-Stirling numbers of the second kind are defined by replacing (1) with S_B[n,k]= S_B[n−1,k−1]+ [2k+1] S_B[n−1,k].” SB is the Lean name of S_B. The initial row is the Kronecker delta at zero, and negative k gives zero. Int.toNat is applied only in the nonnegative branch.

**Definition 1.4 (Type B, first kind).**

$$\forall n \in \mathbb{N},\; \forall k \in \mathbb{Z},\; (\operatorname{cB}\left(0, k\right) = \operatorname{ite}\left(k = 0, 1, 0\right)) \land (\operatorname{cB}\left(n + 1, k\right) = \operatorname{cB}\left(n, k - 1\right) + \operatorname{D5.S0.Certificates.Polynomials.QProductNecessityRefutation.qInteger} (2 \cdot n + 1) \cdot \operatorname{cB}\left(n, k\right))$$

*Formalization.* `D5/S3/Combinatorics/QStirling/SaganSwansonBottomHeavy.cB` (`✓ std3`).

*Citation.* Bruce E. Sagan and Joshua P. Swanson (2022). *q-Stirling numbers in type B*. DOI: [10.1016/j.ejc.2023.103899](https://doi.org/10.1016/j.ejc.2023.103899). URL: <https://arxiv.org/abs/2205.14078v1>.

*Commentary.*

Definition 1.5, equation (9), printed page 6: “The (signless) type B Stirling numbers of the first kind are defined by replacing (4) with c_B[n,k] = c_B[n−1,k−1] + [2n−1] c_B[n−1,k].” cB is the Lean name of c_B. Its successor-row multiplier is qInteger (2*n+1), and its initial row is the Kronecker delta at zero.

**Definition 1.5 (Conjecture 7.6).**

$$claim \Leftrightarrow \left(\forall n \in \mathbb{N},\; \forall k \in \mathbb{Z},\; \forall p \in Polynomial (\mathbb{N}),\; ((p = \operatorname{S}\left(n, k\right)) \lor ((p = \operatorname{c}\left(n, k\right)) \lor ((p = \operatorname{SB}\left(n, k\right)) \lor (p = \operatorname{cB}\left(n, k\right))))) \Rightarrow (\forall r \in \mathbb{N},\; (2 \cdot r < \operatorname{Polynomial.natDegree} (p)) \Rightarrow (\operatorname{Polynomial.coeff} (p) (\operatorname{Polynomial.natDegree} (p) - r) \le \operatorname{Polynomial.coeff} (p) (r)))\right)$$

*Formalization.* `D5/S3/Combinatorics/QStirling/SaganSwansonBottomHeavy.claim` (`✓ std3`).

*Citation.* Bruce E. Sagan and Joshua P. Swanson (2022). *q-Stirling numbers in type B*. DOI: [10.1016/j.ejc.2023.103899](https://doi.org/10.1016/j.ejc.2023.103899). URL: <https://arxiv.org/abs/2205.14078v1>.

*Commentary.*

Conjecture 7.6, printed page 40: “For each n, k, the coefficients of S[n, k], c[n, k], S_B[n, k], and c_B[n, k] are all bottom heavy.” Section 7.5, printed page 39: “A sequence is bottom heavy if aₖ ≥ aₙ₋ₖ for k < n/2.” The list starts at exponent zero and ends at the actual degree. In the formula, n : Nat and k : Int select a row entry; p is any of the four polynomials; r : Nat satisfies the strict-half test 2*r < Polynomial.natDegree p. Natural subtraction then gives the reflected exponent. Zero and constant polynomials have no such r. The separately shifted S-bar family is outside this assertion.

**Theorem 1.6 (All four families are bottom heavy).**

$$\forall n \in \mathbb{N},\; \forall k \in \mathbb{Z},\; \forall p \in Polynomial (\mathbb{N}),\; ((p = \operatorname{S}\left(n, k\right)) \lor ((p = \operatorname{c}\left(n, k\right)) \lor ((p = \operatorname{SB}\left(n, k\right)) \lor (p = \operatorname{cB}\left(n, k\right))))) \Rightarrow (\forall r \in \mathbb{N},\; (2 \cdot r < \operatorname{Polynomial.natDegree} (p)) \Rightarrow (\operatorname{Polynomial.coeff} (p) (\operatorname{Polynomial.natDegree} (p) - r) \le \operatorname{Polynomial.coeff} (p) (r)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/QStirling/SaganSwansonBottomHeavy.result` (`✓ std3`). ∎

*Resolves.* `Problems/ss2205-bottomheavy` (proved) by `D5/S3/Combinatorics/QStirling/SaganSwansonBottomHeavy.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"ss2205-bottomheavy","declaration_gid":"D5/S3/Combinatorics/QStirling/SaganSwansonBottomHeavy.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Bruce E. Sagan and Joshua P. Swanson (2022). *q-Stirling numbers in type B*. DOI: [10.1016/j.ejc.2023.103899](https://doi.org/10.1016/j.ejc.2023.103899). URL: <https://arxiv.org/abs/2205.14078v1>.

*Commentary.*

Products of positive-length qInteger polynomials decompose into sums of centered interval layers. These layers are symmetric, have bounded support, and their coefficients rise toward the center. An atom with positive constant coefficient can therefore be compared at every ambient degree bounding its support. Nonnegative sums preserve this comparison at the degree of the whole sum, even when their summands have different degrees. The four recurrences preserve this class, which proves the stated inequality for every integer k. This does not assert unimodality or log-concavity of the resulting sums.

## References

- Truth anchor: `D5/S3/Combinatorics/QStirling/SaganSwansonBottomHeavy.S`
- Truth anchor: `D5/S3/Combinatorics/QStirling/SaganSwansonBottomHeavy.SB`
- Truth anchor: `D5/S3/Combinatorics/QStirling/SaganSwansonBottomHeavy.c`
- Truth anchor: `D5/S3/Combinatorics/QStirling/SaganSwansonBottomHeavy.cB`
- Truth anchor: `D5/S3/Combinatorics/QStirling/SaganSwansonBottomHeavy.claim`
- Truth anchor: `D5/S3/Combinatorics/QStirling/SaganSwansonBottomHeavy.result`
- Dependency: [D5/S0/Certificates/Polynomials/QProductNecessityRefutation](../../../S0/Certificates/Polynomials/QProductNecessityRefutation.md)
