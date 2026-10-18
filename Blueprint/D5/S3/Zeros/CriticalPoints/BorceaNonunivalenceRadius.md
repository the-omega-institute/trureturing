# A counterexample to the root-moment nonunivalence radius

## Abstract

The polynomial z−z⁴ is injective on the closed disk of radius 5/8, although its order-one root moment times sin(π/4) is strictly smaller than 5/8. This refutes Conjecture 4's proposed nonunivalence radius.

D. Khavinson, R. Pereira, M. Putinar, E. B. Saff and S. Shimorin, Borcea's variance conjectures on the critical points of polynomials. arXiv:1010.5167v2, §5, Theorem 5.1 and Conjecture 4.

Theorem 5.1 (Alexander-Kakeya). If a polynomial F of degree n has no critical points in a closed disk of radius R, then it is univalent in the concentric disk of radius R sin(π/n).

Conjecture 4. If F is an nth degree polynomial with F(0) = 0, then F is not univalent in any closed disk of radius larger than σ_p(F) sin(π/n), p ≥ 1, centered at zero.

Of course, if the conjecture is true for p = 1, then it follows for all p ≥ 1. By the Alexander-Kakeya Theorem, the truth of this conjecture implies the truth of Conjecture 1 for the same value of p. It can be easily seen that the strongest case p = 1 of this conjecture is true for n = 2.

**Definition 1.1 (The root moment about a center).**

Lean statement: `D5/S3/Zeros/CriticalPoints/BorceaNonunivalenceRadius.rootMoment`

*Formalization.* `D5/S3/Zeros/CriticalPoints/BorceaNonunivalenceRadius.rootMoment` (`✓ std3`).

*Citation.* D. Khavinson, R. Pereira, M. Putinar, E. B. Saff, S. Shimorin (2011). *Borcea's variance conjectures on the critical points of polynomials*. DOI: [10.1007/978-3-0348-0142-3_16](https://doi.org/10.1007/978-3-0348-0142-3_16). URL: <https://arxiv.org/abs/1010.5167>.

*Commentary.*

For a polynomial F of degree n, the root moment about c is ((1/n) times the sum of |z_j−c|^p)^(1/p), with all zeros counted with algebraic multiplicity. Real powers are used, including nonintegral p.

**Definition 1.2 (The minimum root moment).**

Lean statement: `D5/S3/Zeros/CriticalPoints/BorceaNonunivalenceRadius.sigma`

*Formalization.* `D5/S3/Zeros/CriticalPoints/BorceaNonunivalenceRadius.sigma` (`✓ std3`).

*Citation.* D. Khavinson, R. Pereira, M. Putinar, E. B. Saff, S. Shimorin (2011). *Borcea's variance conjectures on the critical points of polynomials*. DOI: [10.1007/978-3-0348-0142-3_16](https://doi.org/10.1007/978-3-0348-0142-3_16). URL: <https://arxiv.org/abs/1010.5167>.

*Commentary.*

The quantity σ_p(F) is the infimum of the root moment over all complex centers c. Every root moment is nonnegative, so this family is bounded below and its infimum is at most the moment at zero.

**Definition 1.3 (Conjecture 4 as stated).**

Lean statement: `D5/S3/Zeros/CriticalPoints/BorceaNonunivalenceRadius.conjecture`

*Formalization.* `D5/S3/Zeros/CriticalPoints/BorceaNonunivalenceRadius.conjecture` (`✓ std3`).

*Citation.* D. Khavinson, R. Pereira, M. Putinar, E. B. Saff, S. Shimorin (2011). *Borcea's variance conjectures on the critical points of polynomials*. DOI: [10.1007/978-3-0348-0142-3_16](https://doi.org/10.1007/978-3-0348-0142-3_16). URL: <https://arxiv.org/abs/1010.5167>.

*Commentary.*

For every natural n≥1, every complex polynomial F of degree n with F(0)=0, every real p≥1 and every real radius r strictly larger than σ_p(F) sin(π/n), the conjecture forbids injectivity on the closed disk centered at zero of radius r. Repeated roots are permitted.

**Theorem 1.4 (Conjecture 4 is false).**

Lean statement: `D5/S3/Zeros/CriticalPoints/BorceaNonunivalenceRadius.result`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/CriticalPoints/BorceaNonunivalenceRadius.result` (`✓ std3`). ∎

*Resolves.* `Problems/khavinson-pereira-putinar-saff-shimorin-2011-nonunivalence-radius` (refuted) by `D5/S3/Zeros/CriticalPoints/BorceaNonunivalenceRadius.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"khavinson-pereira-putinar-saff-shimorin-2011-nonunivalence-radius","declaration_gid":"D5/S3/Zeros/CriticalPoints/BorceaNonunivalenceRadius.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* D. Khavinson, R. Pereira, M. Putinar, E. B. Saff, S. Shimorin (2011). *Borcea's variance conjectures on the critical points of polynomials*. DOI: [10.1007/978-3-0348-0142-3_16](https://doi.org/10.1007/978-3-0348-0142-3_16). URL: <https://arxiv.org/abs/1010.5167>.

*Commentary.*

Take F(z)=z−z⁴, n=4, p=1 and r=5/8. The roots are 0, 1, ω and its conjugate, where ω=−1/2+i sqrt(3)/2. The three nonzero roots have norm one. Their order-one moment about zero is 3/4, so σ_1(F) sin(π/4) ≤ 3 sqrt(2)/8 < 5/8.

For |z|,|w|≤5/8, the identity F(z)−F(w)=(z−w)(1−z³−z²w−zw²−w³) and the estimate |z³+z²w+zw²+w³|≤4(5/8)³=125/128<1 show that the second factor cannot vanish. Thus F is injective on the closed disk. This contradicts the conjecture at its stated strict radius threshold.

The result refutes the proposed univalence route. Borcea's variance Conjecture 1 is unaffected. A correct sharp universal replacement radius remains undetermined here.

## References

- Truth anchor: `D5/S3/Zeros/CriticalPoints/BorceaNonunivalenceRadius.conjecture`
- Truth anchor: `D5/S3/Zeros/CriticalPoints/BorceaNonunivalenceRadius.result`
- Truth anchor: `D5/S3/Zeros/CriticalPoints/BorceaNonunivalenceRadius.rootMoment`
- Truth anchor: `D5/S3/Zeros/CriticalPoints/BorceaNonunivalenceRadius.sigma`
