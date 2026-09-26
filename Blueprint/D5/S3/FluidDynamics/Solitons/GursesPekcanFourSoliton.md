# Four-soliton solutions of D_x(D_x^3 + a1 D_t + a2 D_y)^(2k+1) exist only for k = 0

## Abstract

For the Hirota bilinear equation D_x(D_x^3 + a1 D_t + a2 D_y)^(2k+1){f.f} = 0, the four-soliton condition holds identically on the dispersion relation when k = 0 and fails at the wave numbers 1, 3, 4, 5 for every k at least one.

**Definition 1.1 (The polynomial of the bilinear operator).**

$$\operatorname{hirotaP}\left(alpha1, alpha2, m, (k, omega, l)\right) = k \cdot (k^{3} + alpha1 \cdot omega + alpha2 \cdot l)^{m}$$

*Formalization.* `D5/S3/FluidDynamics/Solitons/GursesPekcanFourSoliton.hirotaP` (`✓ std3`).

*Citation.* Metin Gürses, Aslı Pekcan (2025). *Higher order Hirota bilinear forms*. DOI: [10.48550/arXiv.2511.18466](https://doi.org/10.48550/arXiv.2511.18466). URL: <https://arxiv.org/abs/2511.18466v1>.

*Commentary.*

For the soliton parameters p = (k, omega, l) of an exponential exp(kx + omega t + l y), the operator D_x(D_x^3 + a1 D_t + a2 D_y)^m has the polynomial k (k^3 + a1 omega + a2 l)^m.

**Definition 1.2 (The dispersion relation).**

$$\operatorname{dispersion}\left(alpha1, alpha2, (k, omega, l)\right) \Leftrightarrow (k^{3} + alpha1 \cdot omega + alpha2 \cdot l = 0)$$

*Formalization.* `D5/S3/FluidDynamics/Solitons/GursesPekcanFourSoliton.dispersion` (`✓ std3`).

*Citation.* Metin Gürses, Aslı Pekcan (2025). *Higher order Hirota bilinear forms*. DOI: [10.48550/arXiv.2511.18466](https://doi.org/10.48550/arXiv.2511.18466). URL: <https://arxiv.org/abs/2511.18466v1>.

*Commentary.*

The source writes omega = -(k^3 + a2 l)/a1 for a1 nonzero; the relation k^3 + a1 omega + a2 l = 0 is the same condition and also covers a1 = 0 with a2 nonzero.

**Definition 1.3 (The four-soliton condition).**

$$\operatorname{fourSC}\left(P, p\right) = \operatorname{P}\left(p_{1} - p_{2}\right) \cdot \operatorname{P}\left(p_{1} - p_{3}\right) \cdot \operatorname{P}\left(p_{1} - p_{4}\right) \cdot \operatorname{P}\left(p_{2} - p_{3}\right) \cdot \operatorname{P}\left(p_{2} - p_{4}\right) \cdot \operatorname{P}\left(p_{3} - p_{4}\right) \cdot \operatorname{P}\left(p_{1} + p_{2} + p_{3} + p_{4}\right) - \operatorname{P}\left(p_{2} - p_{3}\right) \cdot \operatorname{P}\left(p_{2} - p_{4}\right) \cdot \operatorname{P}\left(p_{3} - p_{4}\right) \cdot \operatorname{P}\left(p_{1} + p_{3}\right) \cdot \operatorname{P}\left(p_{1} + p_{2}\right) \cdot \operatorname{P}\left(p_{1} + p_{4}\right) \cdot \operatorname{P}\left(p_{1} - p_{2} - p_{3} - p_{4}\right) - \operatorname{P}\left(p_{1} - p_{3}\right) \cdot \operatorname{P}\left(p_{1} - p_{4}\right) \cdot \operatorname{P}\left(p_{3} - p_{4}\right) \cdot \operatorname{P}\left(p_{1} + p_{2}\right) \cdot \operatorname{P}\left(p_{2} + p_{3}\right) \cdot \operatorname{P}\left(p_{2} + p_{4}\right) \cdot \operatorname{P}\left(p_{1} - p_{2} + p_{3} + p_{4}\right) - \operatorname{P}\left(p_{1} - p_{2}\right) \cdot \operatorname{P}\left(p_{1} - p_{4}\right) \cdot \operatorname{P}\left(p_{2} - p_{4}\right) \cdot \operatorname{P}\left(p_{1} + p_{3}\right) \cdot \operatorname{P}\left(p_{2} + p_{3}\right) \cdot \operatorname{P}\left(p_{3} + p_{4}\right) \cdot \operatorname{P}\left(p_{1} + p_{2} - p_{3} + p_{4}\right) - \operatorname{P}\left(p_{1} - p_{2}\right) \cdot \operatorname{P}\left(p_{1} - p_{3}\right) \cdot \operatorname{P}\left(p_{2} - p_{3}\right) \cdot \operatorname{P}\left(p_{1} + p_{4}\right) \cdot \operatorname{P}\left(p_{2} + p_{4}\right) \cdot \operatorname{P}\left(p_{3} + p_{4}\right) \cdot \operatorname{P}\left(p_{1} + p_{2} + p_{3} - p_{4}\right) + \operatorname{P}\left(p_{1} - p_{2}\right) \cdot \operatorname{P}\left(p_{3} - p_{4}\right) \cdot \operatorname{P}\left(p_{1} + p_{3}\right) \cdot \operatorname{P}\left(p_{1} + p_{4}\right) \cdot \operatorname{P}\left(p_{2} + p_{3}\right) \cdot \operatorname{P}\left(p_{2} + p_{4}\right) \cdot \operatorname{P}\left(p_{1} + p_{2} - p_{3} - p_{4}\right) + \operatorname{P}\left(p_{1} - p_{3}\right) \cdot \operatorname{P}\left(p_{2} - p_{4}\right) \cdot \operatorname{P}\left(p_{1} + p_{2}\right) \cdot \operatorname{P}\left(p_{1} + p_{4}\right) \cdot \operatorname{P}\left(p_{2} + p_{3}\right) \cdot \operatorname{P}\left(p_{3} + p_{4}\right) \cdot \operatorname{P}\left(p_{1} - p_{2} + p_{3} - p_{4}\right) + \operatorname{P}\left(p_{1} - p_{4}\right) \cdot \operatorname{P}\left(p_{2} - p_{3}\right) \cdot \operatorname{P}\left(p_{1} + p_{2}\right) \cdot \operatorname{P}\left(p_{1} + p_{3}\right) \cdot \operatorname{P}\left(p_{2} + p_{4}\right) \cdot \operatorname{P}\left(p_{3} + p_{4}\right) \cdot \operatorname{P}\left(p_{1} - p_{2} - p_{3} + p_{4}\right)$$

*Formalization.* `D5/S3/FluidDynamics/Solitons/GursesPekcanFourSoliton.fourSC` (`✓ std3`).

*Citation.* Metin Gürses, Aslı Pekcan (2025). *Higher order Hirota bilinear forms*. DOI: [10.48550/arXiv.2511.18466](https://doi.org/10.48550/arXiv.2511.18466). URL: <https://arxiv.org/abs/2511.18466v1>.

*Commentary.*

The eight terms of the source's display, Hietarinta's form with the first sign fixed, for any function P of the parameters and parameters p_1, ..., p_4. The last factor of the fifth term is P(p_1 + p_2 + p_3 - p_4): the source prints P(p_1 - p_2 + p_3 - p_4), the last factor of the seventh term, while the pair factors of the fifth term belong to the sign pattern (+, +, +, -).

**Definition 1.4 (The conjectured lemma of Gurses and Pekcan).**

$$claim \Leftrightarrow ((\forall alpha1 \in \mathbb{R},\; \forall alpha2 \in \mathbb{R},\; ((alpha1, alpha2) \ne (0, 0)) \Rightarrow (\forall p \in \operatorname{Fin}\left(4\right) \to \mathbb{R} \times \mathbb{R} \times \mathbb{R},\; (\forall i \in \operatorname{Fin}\left(4\right),\; \operatorname{dispersion}\left(alpha1, alpha2, p\left(i\right)\right)) \Rightarrow (\operatorname{fourSC}\left(\operatorname{hirotaP}\left(alpha1, alpha2, 1\right), p\right) = 0))) \land (\forall alpha1 \in \mathbb{R},\; \forall alpha2 \in \mathbb{R},\; ((alpha1, alpha2) \ne (0, 0)) \Rightarrow (\forall k \in \mathbb{N},\; (1 \le k) \Rightarrow (\exists p \in \operatorname{Fin}\left(4\right) \to \mathbb{R} \times \mathbb{R} \times \mathbb{R},\; (\forall i \in \operatorname{Fin}\left(4\right),\; \operatorname{dispersion}\left(alpha1, alpha2, p\left(i\right)\right)) \land (\operatorname{fourSC}\left(\operatorname{hirotaP}\left(alpha1, alpha2, 2 \cdot k + 1\right), p\right) \ne 0)))))$$

*Formalization.* `D5/S3/FluidDynamics/Solitons/GursesPekcanFourSoliton.claim` (`✓ std3`).

*Citation.* Metin Gürses, Aslı Pekcan (2025). *Higher order Hirota bilinear forms*. DOI: [10.48550/arXiv.2511.18466](https://doi.org/10.48550/arXiv.2511.18466). URL: <https://arxiv.org/abs/2511.18466v1>.

*Commentary.*

The first conjunct says that for k = 0 the four-soliton condition vanishes at all parameters satisfying the dispersion relation. The second says that for every k at least one there are such parameters at which it does not vanish, so the condition is not satisfied directly.

**Theorem 1.5 (The four-soliton condition holds only for k = 0).**

$$(\forall alpha1 \in \mathbb{R},\; \forall alpha2 \in \mathbb{R},\; ((alpha1, alpha2) \ne (0, 0)) \Rightarrow (\forall p \in \operatorname{Fin}\left(4\right) \to \mathbb{R} \times \mathbb{R} \times \mathbb{R},\; (\forall i \in \operatorname{Fin}\left(4\right),\; \operatorname{dispersion}\left(alpha1, alpha2, p\left(i\right)\right)) \Rightarrow (\operatorname{fourSC}\left(\operatorname{hirotaP}\left(alpha1, alpha2, 1\right), p\right) = 0))) \land (\forall alpha1 \in \mathbb{R},\; \forall alpha2 \in \mathbb{R},\; ((alpha1, alpha2) \ne (0, 0)) \Rightarrow (\forall k \in \mathbb{N},\; (1 \le k) \Rightarrow (\exists p \in \operatorname{Fin}\left(4\right) \to \mathbb{R} \times \mathbb{R} \times \mathbb{R},\; (\forall i \in \operatorname{Fin}\left(4\right),\; \operatorname{dispersion}\left(alpha1, alpha2, p\left(i\right)\right)) \land (\operatorname{fourSC}\left(\operatorname{hirotaP}\left(alpha1, alpha2, 2 \cdot k + 1\right), p\right) \ne 0))))$$

*Proof.* Machine-checked in Lean as `D5/S3/FluidDynamics/Solitons/GursesPekcanFourSoliton.result` (`✓ std3`). ∎

*Resolves.* `Problems/gurses-pekcan-2025-higher-hirota-four-soliton` (proved) by `D5/S3/FluidDynamics/Solitons/GursesPekcanFourSoliton.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"gurses-pekcan-2025-higher-hirota-four-soliton","declaration_gid":"D5/S3/FluidDynamics/Solitons/GursesPekcanFourSoliton.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Metin Gürses, Aslı Pekcan (2025). *Higher order Hirota bilinear forms*. DOI: [10.48550/arXiv.2511.18466](https://doi.org/10.48550/arXiv.2511.18466). URL: <https://arxiv.org/abs/2511.18466v1>.

*Commentary.*

On the dispersion relation a1 omega + a2 l = -k^3, and the map (k, omega, l) to (k, a1 omega + a2 l) is additive, so every value of P at a signed sum of parameters equals x (x^3 + e)^m with x the signed sum of the wave numbers and e minus the signed sum of their cubes. For m = 1 the condition becomes a polynomial identity in the four wave numbers, which holds. For m = 2k + 1 with k at least one, the wave numbers 1, 3, 4, 5 with omega_i = -k_i^3/a1 and l_i = 0 (or omega_i = 0 and l_i = -k_i^3/a2 when a1 = 0) satisfy the dispersion relation, and each of the eight terms is a product of seven factors x (x^3 + e)^m, which collects into 48 g^m F(m) with g = 1360488960000 and F(m) = 13 11^m - 55 (-31)^m + 392 56^m + 525 21^m + 162 18^m - 350 14^m - 567 63^m - 120 (-24)^m. For odd m the positive terms of F(m) are at most 1267 56^m, and 1267 56^m < 567 63^m from m = 7 on by induction; F(3) and F(5) are negative by direct computation. So the condition is negative for every k at least one.

## References

- Truth anchor: `D5/S3/FluidDynamics/Solitons/GursesPekcanFourSoliton.claim`
- Truth anchor: `D5/S3/FluidDynamics/Solitons/GursesPekcanFourSoliton.dispersion`
- Truth anchor: `D5/S3/FluidDynamics/Solitons/GursesPekcanFourSoliton.fourSC`
- Truth anchor: `D5/S3/FluidDynamics/Solitons/GursesPekcanFourSoliton.hirotaP`
- Truth anchor: `D5/S3/FluidDynamics/Solitons/GursesPekcanFourSoliton.result`
