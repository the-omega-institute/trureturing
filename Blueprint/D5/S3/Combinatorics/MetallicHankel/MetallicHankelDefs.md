# q-Metallic Series and Shifted Hankel Determinants

## Abstract

The q-metallic quadratic equation defines integral power series and their shifted Hankel determinants.

**Definition 1.1 (The linear coefficient of the quadratic equation).**

Lean statement: `D5/S3/Combinatorics/MetallicHankel/MetallicHankelDefs.linearCoeff`

*Formalization.* `D5/S3/Combinatorics/MetallicHankel/MetallicHankelDefs.linearCoeff` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Guo-Niu Han, Emmanuel Pedon (2025). *Hankel continued fractions and Hankel determinants for q-deformed metallic numbers*. DOI: [10.48550/arXiv.2502.05993](https://doi.org/10.48550/arXiv.2502.05993). URL: <https://arxiv.org/abs/2502.05993v2>.

*Commentary.*

For a nonnegative integer n, put [n]_q = 1 + q + ... + q^{n-1}, with the empty sum zero. The integral formal power series B_n(q) is (1 + q^n)(1 - q) - q[n]_q.

**Definition 1.2 (The q-metallic equation).**

Lean statement: `D5/S3/Combinatorics/MetallicHankel/MetallicHankelDefs.IsMetallic`

*Formalization.* `D5/S3/Combinatorics/MetallicHankel/MetallicHankelDefs.IsMetallic` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Guo-Niu Han, Emmanuel Pedon (2025). *Hankel continued fractions and Hankel determinants for q-deformed metallic numbers*. DOI: [10.48550/arXiv.2502.05993](https://doi.org/10.48550/arXiv.2502.05993). URL: <https://arxiv.org/abs/2502.05993v2>.

*Commentary.*

An integral formal power series Phi is q-metallic with parameter n when its constant coefficient is one and q Phi^2 + B_n(q) Phi = 1, where B_n(q) = (1 + q^n)(1 - q) - q[n]_q.

**Definition 1.3 (Shifted Hankel determinants).**

Lean statement: `D5/S3/Combinatorics/MetallicHankel/MetallicHankelDefs.shiftedHankel`

*Formalization.* `D5/S3/Combinatorics/MetallicHankel/MetallicHankelDefs.shiftedHankel` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Guo-Niu Han, Emmanuel Pedon (2025). *Hankel continued fractions and Hankel determinants for q-deformed metallic numbers*. DOI: [10.48550/arXiv.2502.05993](https://doi.org/10.48550/arXiv.2502.05993). URL: <https://arxiv.org/abs/2502.05993v2>.

*Commentary.*

For an integral formal power series Phi(q) = sum_{r >= 0} f_r q^r and nonnegative integers ell and j, Delta_j^{(ell)} is the determinant of the j by j matrix with entry f_{ell+a+b} in row a and column b, with indices starting at zero. The empty determinant Delta_0^{(ell)} is one.

**Definition 1.4 (The periodicity and value assertion).**

Lean statement: `D5/S3/Combinatorics/MetallicHankel/MetallicHankelDefs.claim`

*Formalization.* `D5/S3/Combinatorics/MetallicHankel/MetallicHankelDefs.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Guo-Niu Han, Emmanuel Pedon (2025). *Hankel continued fractions and Hankel determinants for q-deformed metallic numbers*. DOI: [10.48550/arXiv.2502.05993](https://doi.org/10.48550/arXiv.2502.05993). URL: <https://arxiv.org/abs/2502.05993v2>.

*Commentary.*

For every integer n at least two, an integral q-metallic series Phi exists. For every integral q-metallic series with that parameter and every nonnegative integer j, Delta_{j+2n(n+1)}^{(n+2)} = (-1)^n Delta_j^{(n+2)}, and Delta_j^{(n+2)} belongs to {-2, -1, 0, 1, 2}. This is part 1 of Conjecture E of Han and Pedon.

## References

- Truth anchor: `D5/S3/Combinatorics/MetallicHankel/MetallicHankelDefs.IsMetallic`
- Truth anchor: `D5/S3/Combinatorics/MetallicHankel/MetallicHankelDefs.claim`
- Truth anchor: `D5/S3/Combinatorics/MetallicHankel/MetallicHankelDefs.linearCoeff`
- Truth anchor: `D5/S3/Combinatorics/MetallicHankel/MetallicHankelDefs.shiftedHankel`
