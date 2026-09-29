# No beta-invertible S_3 symmetry when 3 divides N

## Abstract

When 3 divides N, no copy of the symmetric group S_3 inside the anyon permutation symmetries of the Z_N x Z_N SymTFT has all of its non-identity elements beta-invertible, as conjectured by D.-C. Lu, Z. Sun and Z. Zhang (arXiv:2406.12151, JHEP 11 (2025) 081); so the Z_N x Z_N theory admits no S_3-ality extension of this kind for such N.

**Definition 1.1 (The quadratic form of the SymTFT).**

$$\forall v \in \operatorname{Fin}\left(2\right) + \operatorname{Fin}\left(2\right) \to \operatorname{ZMod}\left(N\right),\; \operatorname{Q}\left(v\right) = v\left(\operatorname{inl}\left(0\right)\right) \cdot v\left(\operatorname{inr}\left(0\right)\right) + v\left(\operatorname{inl}\left(1\right)\right) \cdot v\left(\operatorname{inr}\left(1\right)\right)$$

*Formalization.* `D5/S3/Quantum/Algebra/BetaInvertibleSThreeObstruction.Q` (`✓ std3`).

*Citation.* Da-Chuan Lu; Zhengdi Sun; Zipei Zhang (2024). *Exploring G-ality defects in 2-dim QFTs*. DOI: [10.1007/JHEP11(2025)081](https://doi.org/10.1007/JHEP11(2025)081). URL: <https://arxiv.org/abs/2406.12151v3>.

*Commentary.*

On the anyons (a, a') of the Z_N x Z_N SymTFT, with a in A = (Z/N)^2 the left summand and a' in the dual group identified with (Z/N)^2, Q is the dot product a . a' modulo N; the self-statistics of the anyon is exp(2 pi i Q / N).

**Definition 1.2 (The conjecture for N divisible by 3).**

$$claim \Leftrightarrow (\forall N \in \mathbb{N},\; 3 \mid N \Rightarrow (\neg(\exists rho \in \operatorname{MonoidHom}\left(\operatorname{Perm}\left(\operatorname{Fin}\left(3\right)\right), \operatorname{GL}\left(\operatorname{Fin}\left(2\right) + \operatorname{Fin}\left(2\right), \operatorname{ZMod}\left(N\right)\right)\right),\; (\forall g \in \operatorname{Perm}\left(\operatorname{Fin}\left(3\right)\right),\; \forall v \in \operatorname{Fin}\left(2\right) + \operatorname{Fin}\left(2\right) \to \operatorname{ZMod}\left(N\right),\; \operatorname{Q}\left(rho\left(g\right) v\right) = \operatorname{Q}\left(v\right)) \land (\forall g \in \operatorname{Perm}\left(\operatorname{Fin}\left(3\right)\right),\; g \ne 1 \Rightarrow (\operatorname{IsUnit}\left(\operatorname{det}\left(\left(\operatorname{toBlocks}_{12}\right)\left(rho\left(g\right)\right)\right)\right))))))$$

*Formalization.* `D5/S3/Quantum/Algebra/BetaInvertibleSThreeObstruction.claim` (`✓ std3`).

*Citation.* Da-Chuan Lu; Zhengdi Sun; Zipei Zhang (2024). *Exploring G-ality defects in 2-dim QFTs*. DOI: [10.1007/JHEP11(2025)081](https://doi.org/10.1007/JHEP11(2025)081). URL: <https://arxiv.org/abs/2406.12151v3>.

*Commentary.*

For every N divisible by 3 there is no group homomorphism rho from S_3, the permutations of three letters, to the invertible 4 x 4 matrices over Z/N such that every rho(g) preserves Q and, for every g other than the identity, the upper-right 2 x 2 block beta of rho(g), the component from the dual group to A, has a unit determinant. A subgroup isomorphic to S_3 whose non-identity elements are all beta-invertible is exactly such a homomorphism, which is then injective.

**Theorem 1.3 (Proof of the conjecture).**

$$claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/BetaInvertibleSThreeObstruction.result` (`✓ std3`). ∎

*Resolves.* `Problems/lu-sun-zhang-2024-beta-invertible-s3-obstruction` (proved) by `D5/S3/Quantum/Algebra/BetaInvertibleSThreeObstruction.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"lu-sun-zhang-2024-beta-invertible-s3-obstruction","declaration_gid":"D5/S3/Quantum/Algebra/BetaInvertibleSThreeObstruction.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Da-Chuan Lu; Zhengdi Sun; Zipei Zhang (2024). *Exploring G-ality defects in 2-dim QFTs*. DOI: [10.1007/JHEP11(2025)081](https://doi.org/10.1007/JHEP11(2025)081). URL: <https://arxiv.org/abs/2406.12151v3>.

*Commentary.*

Reduce rho modulo 3. The reduced matrices still preserve Q, since every vector over Z/3 lifts to Z/N, and still have invertible beta blocks at g other than the identity, since the determinant reduces to a unit. Over Z/3 let S_g = delta_g beta_g^{-1}, where delta_g is the lower-right block. The matrix rho(g) sends (0, x) to (beta_g x, delta_g x), and Q vanishes at (0, x), so y . S_g y = 0 for every y; hence S_g has zero diagonal and opposite off-diagonal entries and is determined by its entry S_g(0, 1). If g and h are different non-identity permutations with S_g = S_h, then rho(h) sends (0, z) to rho(g)(0, x) for z = beta_h^{-1} beta_g x, so rho(h^{-1} g) sends (0, x) to (0, z) for every x and its beta block vanishes, although h^{-1} g is not the identity. So g -> S_g(0, 1) maps the five non-identity permutations injectively into Z/3, which has three elements, a contradiction. The same argument bounds every beta-invertible group by p + 1 for any prime p dividing N.

## References

- Truth anchor: `D5/S3/Quantum/Algebra/BetaInvertibleSThreeObstruction.Q`
- Truth anchor: `D5/S3/Quantum/Algebra/BetaInvertibleSThreeObstruction.claim`
- Truth anchor: `D5/S3/Quantum/Algebra/BetaInvertibleSThreeObstruction.result`
