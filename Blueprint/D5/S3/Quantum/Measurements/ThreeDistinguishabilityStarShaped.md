# Uniform interpolation of four-outcome laws for three distinguishable states

## Abstract

The mixed three-distinguishability region for four outcomes is star-shaped about the uniform law.

**Theorem 1.1 (The four-outcome, three-state case of Conjecture 9).**

Lean statement: `D5/S3/Quantum/Measurements/ThreeDistinguishabilityStarShaped.inRegion_uniform_interpolation`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurements/ThreeDistinguishabilityStarShaped.inRegion_uniform_interpolation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Korzekwa, Kamil; Czachórski, Stanisław; Puchała, Zbigniew; Życzkowski, Karol (2019). *Distinguishing classically indistinguishable states and channels*. DOI: [10.1088/1751-8121/ab30f7](https://doi.org/10.1088/1751-8121/ab30f7). URL: <https://arxiv.org/abs/1812.09083v3>.

*Acknowledgement.* Ingemar Bengtsson, Åsa Ericsson, Marek Kuś, Wojciech Tadej, Karol Życzkowski (2005). *Birkhoff's Polytope and Unistochastic Matrices, N = 3 and N = 4*. DOI: [10.1007/s00220-005-1392-8](https://doi.org/10.1007/s00220-005-1392-8). URL: <https://arxiv.org/abs/math/0402325v2>.

*Acknowledgement.* Grzegorz Rajchel; Adam Gąsiorowski; Karol Życzkowski (2018). *Robust Hadamard Matrices, Unistochastic Rays in Birkhoff Polytope and Equi-Entangled Bases in Composite Spaces*. DOI: [10.1007/s11786-018-0384-y](https://doi.org/10.1007/s11786-018-0384-y). URL: <https://arxiv.org/abs/1804.10715v2>.

*Acknowledgement.* Grzegorz Rajchel-Mieldzioć, Kamil Korzekwa, Zbigniew Puchała, Karol Życzkowski (2021). *Algebraic and geometric structures inside the Birkhoff polytope*. DOI: [10.1063/5.0046581](https://doi.org/10.1063/5.0046581). URL: <https://arxiv.org/abs/2101.11288>.

*Commentary.*

Let p be a probability law on four outcomes. InRegion p means that three positive semidefinite trace-one matrices have common diagonal p and pairwise zero products, equivalently pairwise orthogonal supports. For η = (1/4,1/4,1/4,1/4) and every s in [0,1], the theorem sends p in InRegion to (1−s)η + sp in InRegion. This proves Korzekwa, Czachórski, Puchała and Życzkowski’s Conjecture 9, §III.C, Eq. (31), arXiv:1812.09083v3 PDF p. 7, for d = 4 and M = 3.

Apply ThreeDistinguishabilityMixedPurity.inRegion_iff_cubic to the closed simplex. Its scalar witnesses have pᵢ ≤ 1/3, 0 < t ≤ 1, xᵢ = (1−2pᵢ)²t−(4pᵢ−1)² ≥ 0, and phaseCubic(p,t) = 0. Write pᵢ(r) = (1+raᵢ)/4 with Σᵢ aᵢ = 0. For r > 0, put w = 4r/t−r and yᵢ(r,w) = 1−r(2aᵢ+w aᵢ²). Then w ≥ 3r and xᵢ = (t/4)yᵢ, with inverse t = 4r/(w+r). For the elementary symmetric polynomials eⱼ, set G(y) = e₁(y)²−4e₂(y) and F(y) = G(y)²−64e₄(y). On normalized laws F(x) = t phaseCubic(p,t). Homogeneity and expansion give F(y(r,w)) = 64r³(A(w)+rB(w)).

With sⱼ = eⱼ(a) and K = s₂²−4s₄, the coefficients are A(w) = 8s₃+4wK−4w²s₂s₃+w³s₃² and B(w) = 4K−12ws₂s₃+9w²s₃²−8w³s₃s₄. A positive-radius scalar witness is thus a zero of A(w)+rB(w) with w ≥ 3r and all yᵢ ≥ 0.

Fix an admissible zero (r₀,w₀) on a nonzero direction. The coefficients cᵢ = 2aᵢ+w₀aᵢ² sum to w₀Σᵢ aᵢ² > 0. The first zero radicand at fixed w₀ occurs at R = 1/maxᵢ cᵢ ≥ r₀. There the quartic is the square G(y)². If R > r₀, this gives 0 ≤ 64R³(R−r₀)B(w₀), hence B(w₀) ≥ 0. This evaluation uses the polynomial identity for any R. If R = r₀, G(y) also vanishes. Differentiate the polynomial in r at R. The derivative of G(y)² is zero and the derivative of the product comes only from a chosen vanishing row j. Equating derivatives gives B(w₀) = (∏ᵢ≠ⱼ yᵢ(R,w₀))/R⁴ ≥ 0. Any additional zero row makes this product zero.

At 0 < r < r₀ the radicands at w₀ are strictly positive because each is a convex combination of 1 and its value at r₀. The old root and B(w₀) ≥ 0 give A(w₀)+rB(w₀) ≤ 0. Increase w up to W = min over aᵢ ≠ 0 of (1−2raᵢ)/(raᵢ²). This finite minimum is above w₀, all radicands are nonnegative on [w₀,W], and one vanishes at W. Thus F(y(r,W)) is a square and A(W)+rB(W) ≥ 0. Continuity gives a root w* in the closed bracket. The bracket includes the old parameter when A(w₀)=B(w₀)=0. Since w* ≥ w₀ ≥ 3r₀ > 3r, t = 4r/(w*+r) gives a guarded cubic witness.

For the given p, take aᵢ = 4pᵢ−1, r₀ = 1 and r = s. The probability bounds are preserved by interpolation. The mixed-region equivalence recovers InRegion. The uniform law uses t = 1, the original endpoint uses its original witness, and a uniform input stays uniform. The proof includes zero weights and simultaneous zero radicands.

For the segment from the corner (0,1/3,1/3,1/3), the midpoint is (1/8,7/24,7/24,7/24). There t = 4/7 yields four radicands equal to 1/14. At t = 0 the factor t makes the unnormalized quartic vanish. The first radicand is then −1/4, which fails the guard.

Proposition 12 on the same page lifts pure-state witnesses under coarse-graining and gives the bounding permutohedron’s edges via Eq. (35). Lemma 5 and the full mixed-to-pure equivalence identify the present region with the unistochastic slice [p,p,p,1−3p]. This affine map sends η to the flat matrix. The theorem gives star-shapedness on this slice. Remark 10 relates the conjecture to the separate question for all order-four unistochastic matrices.

Bengtsson et al. resolve both halves of the type-I central line p(u) = (1−3u,1+u,1+u,1+u)/4 in §IV, Eqs. (35)–(40), and Appendix C, Eqs. (56)–(59) and the following lemma. Rajchel, Gąsiorowski and Życzkowski prove the order-four permutation-to-flat rays in §6 and present Haagerup’s membership procedure in Appendix A. Rajchel-Mieldzioć et al. prove star-shapedness for bracelet and factorisable sets in Theorem 14 and for circulant order-four unistochastic matrices in Theorem 17.

**Theorem 1.2 (The uniform law belongs to the region).**

Lean statement: `D5/S3/Quantum/Measurements/ThreeDistinguishabilityStarShaped.uniform_inRegion`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurements/ThreeDistinguishabilityStarShaped.uniform_inRegion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Korzekwa, Kamil; Czachórski, Stanisław; Puchała, Zbigniew; Życzkowski, Karol (2019). *Distinguishing classically indistinguishable states and channels*. DOI: [10.1088/1751-8121/ab30f7](https://doi.org/10.1088/1751-8121/ab30f7). URL: <https://arxiv.org/abs/1812.09083v3>.

*Commentary.*

At p = η, the guarded cubic holds with t = 1 and all four radicands equal to 1/4. This supplies the centre of the interpolation.

## References

- Truth anchor: `D5/S3/Quantum/Measurements/ThreeDistinguishabilityStarShaped.inRegion_uniform_interpolation`
- Truth anchor: `D5/S3/Quantum/Measurements/ThreeDistinguishabilityStarShaped.uniform_inRegion`
- Dependency: [D5/S3/Quantum/Measurements/ThreeDistinguishabilityMixedPurity](ThreeDistinguishabilityMixedPurity.md)
