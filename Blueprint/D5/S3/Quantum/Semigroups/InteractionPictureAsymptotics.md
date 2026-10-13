# A counterexample to interaction-picture asymptotics

## Abstract

Finite past interaction integrals do not imply polynomial-generator asymptotics.

F. Madou, I. Remizov, M. Vafadar (eds.), Open problems in one-parameter operator semigroups theory, arXiv:2410.00416v2, p. 21, Problem 29 (A. E. Teretenkov), verbatim: “Problem 29 (A.E. Teretenkov). Let B be a Banach space. Let P be a projection on a finite-dimensional Banach subspace of B. Let L0 + λL be a generator of C0-semigroup U^λ_t on B for all λ ∈ [0, λsup). Let U^0_t leave both PB and its complement (I − P)B invariant, let PLP = 0. Denote L_t ≡ (U^0_t)^{−1} L U^0_t. Let the integrals ∫_{−∞}^{t} dt_1 … ∫_{−∞}^{t_{k−1}} dt_k P L_{t_1} … L_{t_k} P, k = 1, …, n + 1 be finite for all t ⩾ 0. If is it possible to find such a λ-dependent operator r^{n,λ} on PB, which is polynomial in λ, and λ-dependent semigroup u^{n,λ}_t on PB, whose generator is polynomial in λ, such that P(U^0_{t/λ²})^{−1} U^λ_{t/λ²} P = u^{n,λ}_t r^{n,λ} + O(λ^{2n+2}), λ → +0 for all t > 0 ? Let us emphasize that we do not assume here asymptotic behaviour to be uniform in t, it is just assumed for each fixed t > 0. If there are counterexamples, what further restrictions should be assumed to obtain such an asymptotic estimate?”

**Definition 1.1 (Complex three-dimensional matrices).**

$$M3 = \operatorname{Matrix}\left(\operatorname{Fin}\left(3\right), \operatorname{Fin}\left(3\right), \mathbb{C}\right)$$

*Formalization.* `D5/S3/Quantum/Semigroups/InteractionPictureAsymptotics.M3` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* F. Madou; I. Remizov; M. Vafadar (eds.) (2024). *Open problems in one-parameter operator semigroups theory*. DOI: [10.48550/arXiv.2410.00416](https://doi.org/10.48550/arXiv.2410.00416). URL: <https://arxiv.org/abs/2410.00416v2>.

*Commentary.*

M3 is the space of complex 3×3 matrices. In the error estimate it carries the entrywise sup norm. The Banach space in the source correspondence is B=ℂ³ with its sup norm; matrices act as bounded operators. Matrix exponentials are independent of the choice of equivalent norm in finite dimension.

**Definition 1.2 (Interaction-picture coupling).**

$$\forall D: M3, \forall N: M3, \forall s: \mathbb{R}, \operatorname{coupling}\left(D, N, s\right) = \operatorname{exp}\left(\operatorname{smul}\left(\operatorname{ofReal}\left(-s\right), D\right)\right) \cdot N \cdot \operatorname{exp}\left(\operatorname{smul}\left(\operatorname{ofReal}\left(s\right), D\right)\right)$$

*Formalization.* `D5/S3/Quantum/Semigroups/InteractionPictureAsymptotics.coupling` (`✓ std3`).

*Citation.* F. Madou; I. Remizov; M. Vafadar (eds.) (2024). *Open problems in one-parameter operator semigroups theory*. DOI: [10.48550/arXiv.2410.00416](https://doi.org/10.48550/arXiv.2410.00416). URL: <https://arxiv.org/abs/2410.00416v2>.

*Commentary.*

coupling D N s is exp(−sD) N exp(sD), for real s and complex matrices D,N. The source parameters are L₀=D and L=N. The real scalars are embedded in ℂ before matrix scalar multiplication. Bounded generators D+λN define C₀-semigroups for every real λ, and exp(sD) is a group with inverse exp(−sD).

**Definition 1.3 (Past-integrability hypotheses at order one).**

$$\forall P: M3, \forall D: M3, \forall N: M3, \operatorname{Hyp}\left(P, D, N\right) \Leftrightarrow (((P \cdot P = P) \land ((D \cdot P = P \cdot D) \land (P \cdot N \cdot P = 0))) \land ((\forall t: \mathbb{R}, \operatorname{IntegrableOn}\left((s \mapsto P \cdot \operatorname{coupling}\left(D, N, s\right) \cdot P), \operatorname{Iic}\left(t\right)\right)) \land (\forall t: \mathbb{R}, (\forall s1: \mathbb{R}, \operatorname{IntegrableOn}\left((s2 \mapsto P \cdot \operatorname{coupling}\left(D, N, s1\right) \cdot \operatorname{coupling}\left(D, N, s2\right) \cdot P), \operatorname{Iic}\left(s1\right)\right)) \land (\operatorname{IntegrableOn}\left((s1 \mapsto \operatorname{pastIntegral}\left(s1, (s2 \mapsto P \cdot \operatorname{coupling}\left(D, N, s1\right) \cdot \operatorname{coupling}\left(D, N, s2\right) \cdot P)\right)), \operatorname{Iic}\left(t\right)\right)))))$$

*Formalization.* `D5/S3/Quantum/Semigroups/InteractionPictureAsymptotics.Hyp` (`✓ std3`).

*Citation.* F. Madou; I. Remizov; M. Vafadar (eds.) (2024). *Open problems in one-parameter operator semigroups theory*. DOI: [10.48550/arXiv.2410.00416](https://doi.org/10.48550/arXiv.2410.00416). URL: <https://arxiv.org/abs/2410.00416v2>.

*Commentary.*

Hyp P D N requires P²=P, DP=PD, and PNP=0. Commutation implies that the free evolution preserves both PB and (I−P)B. It also requires Lebesgue integrability of the first projected interaction, of each second inner integrand, and of the resulting inner integral, on the indicated past intervals. Every endpoint t is real, including negative endpoints, so this is stronger than requiring only t≥0. In the formula, pastIntegral(a,f) means the Lebesgue integral of f over (−∞,a], and IntegrableOn(f,Iic(a)) is Lebesgue integrability on that interval. These stronger integrability conditions imply the finite-integral hypotheses of the source for n=1.

**Definition 1.4 (Polynomial preparation and generator).**

$$\forall P: M3, \forall D: M3, \forall N: M3, \operatorname{Expansion}\left(P, D, N\right) \Leftrightarrow (\exists m: \mathbb{N}, \exists R: \operatorname{Fin}\left(m\right) \to M3, \exists G: \operatorname{Fin}\left(m\right) \to M3, \forall t: \mathbb{R}, (0 < t) \Rightarrow (\exists C: \mathbb{R}, \exists delta: \mathbb{R}, (0 < delta) \land (\forall l: \mathbb{R}, (0 < l) \Rightarrow ((l < delta) \Rightarrow (\operatorname{norm}\left((P \cdot \operatorname{exp}\left(\operatorname{smul}\left(\operatorname{ofReal}\left(-\frac{t}{l^{2}}\right), D\right)\right) \cdot \operatorname{exp}\left(\operatorname{smul}\left(\operatorname{ofReal}\left(\frac{t}{l^{2}}\right), (D + \operatorname{smul}\left(\operatorname{ofReal}\left(l\right), N\right))\right)\right) \cdot P - \operatorname{exp}\left(\operatorname{smul}\left(\operatorname{ofReal}\left(t\right), \operatorname{poly}\left(G, l\right)\right)\right) \cdot \operatorname{poly}\left(R, l\right))\right) \le C \cdot l^{4})))))$$

*Formalization.* `D5/S3/Quantum/Semigroups/InteractionPictureAsymptotics.Expansion` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* F. Madou; I. Remizov; M. Vafadar (eds.) (2024). *Open problems in one-parameter operator semigroups theory*. DOI: [10.48550/arXiv.2410.00416](https://doi.org/10.48550/arXiv.2410.00416). URL: <https://arxiv.org/abs/2410.00416v2>.

*Commentary.*

Expansion P D N allows arbitrary m∈ℕ and R,G : Fin m → M3. The notation poly(A,λ) means ∑_{j∈Fin m} λʲ Aⱼ, with j interpreted as its natural value and λ embedded in ℂ. Each fixed t>0 has its own real C and δ>0; there is no uniformity in t and no separate positivity condition on C. The error norm is the entrywise sup norm and the error order is λ⁴, corresponding to n=1. Different degrees can be padded with zero coefficients. The coefficients need not be supported on PB. Thus the permitted approximants include all source approximants: for G=PGP and R=PRP, exp(tG)R is the embedded semigroup on PB times its preparation. This embedding correspondence is mathematical reasoning.

**Definition 1.5 (The order-one implication).**

$$claim \Leftrightarrow (\forall P: M3, \forall D: M3, \forall N: M3, (\operatorname{Hyp}\left(P, D, N\right)) \Rightarrow (\operatorname{Expansion}\left(P, D, N\right)))$$

*Formalization.* `D5/S3/Quantum/Semigroups/InteractionPictureAsymptotics.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* F. Madou; I. Remizov; M. Vafadar (eds.) (2024). *Open problems in one-parameter operator semigroups theory*. DOI: [10.48550/arXiv.2410.00416](https://doi.org/10.48550/arXiv.2410.00416). URL: <https://arxiv.org/abs/2410.00416v2>.

*Commentary.*

The claim states that every triple P,D,N of complex 3×3 matrices satisfying Hyp admits Expansion. The dimension is fixed at three and n=1; a counterexample suffices to refute the first question of Problem 29. The projection in the instance has rank two.

**Theorem 1.6 (Past integrability does not ensure the expansion).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Semigroups/InteractionPictureAsymptotics.result` (`✓ std3`). ∎

*Resolves.* `Problems/teretenkov-2024-interaction-picture-asymptotics` (refuted) by `D5/S3/Quantum/Semigroups/InteractionPictureAsymptotics.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"teretenkov-2024-interaction-picture-asymptotics","declaration_gid":"D5/S3/Quantum/Semigroups/InteractionPictureAsymptotics.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* F. Madou; I. Remizov; M. Vafadar (eds.) (2024). *Open problems in one-parameter operator semigroups theory*. DOI: [10.48550/arXiv.2410.00416](https://doi.org/10.48550/arXiv.2410.00416). URL: <https://arxiv.org/abs/2410.00416v2>.

*Commentary.*

Take P=diag(1,0,1), D=diag(−3,−2,−1), N=E₁₂+E₂₃, and E=N²=E₁₃, with one-based matrix coordinates. projection_algebra proves P²=P, DP=PD, PNP=0. coupling_formula gives Lₛ=eˢN. first_integrand is zero, second_integrand is e^(s₁+s₂)E, and inner_integral is e^(2s₁)E. hypotheses proves their required integrability for every real endpoint. The outer integral is e^(2t)E/2 by exact integration. The full identity exp(−sD)exp(s(D+λN))=I+λ(eˢ−1)N+λ²(eˢ−1)²E/2 is exact mathematical reasoning; projected_entry proves its projected (1,3) entry. At s=t/λ² this entry is λ²(e^(t/λ²)−1)²/2≥t²/(2λ²) for t,λ>0. The lemma growth uses t=1 and the fact that an entry norm is at most the matrix norm. polynomial_continuous and locally_bounded show that exp(G(λ))R(λ) is bounded near zero. no_expansion contradicts the order-four error at t=1, and result proves ¬ claim. The finite-dimensional generator and subspace correspondences give a negative answer to the first question of Problem 29. By mathematical reasoning, N³=0 makes all products of three or more interactions vanish, so the same instance meets the hypotheses for n≥2; the higher-order estimate would imply the refuted order-four estimate. This extension is not formalized in the module. The mechanism is exponential contraction of the free evolution and amplification by its inverse: fixed-endpoint past integrability does not control endpoints t/λ² tending to infinity. Isometric free evolution on (I−P)B, or a uniform bound there on both the free evolution and its inverse, would exclude this example. Whether these candidate restrictions suffice, and the second question of Problem 29, are not settled by this result. The relation to Teretenkov arXiv:2008.02820 and Davies' weak-coupling literature is limited to titles and abstracts; their detailed hypotheses and applicability are ASSUMED-UNVERIFIED. No literature priority is established.

## References

- Truth anchor: `D5/S3/Quantum/Semigroups/InteractionPictureAsymptotics.Expansion`
- Truth anchor: `D5/S3/Quantum/Semigroups/InteractionPictureAsymptotics.Hyp`
- Truth anchor: `D5/S3/Quantum/Semigroups/InteractionPictureAsymptotics.M3`
- Truth anchor: `D5/S3/Quantum/Semigroups/InteractionPictureAsymptotics.claim`
- Truth anchor: `D5/S3/Quantum/Semigroups/InteractionPictureAsymptotics.coupling`
- Truth anchor: `D5/S3/Quantum/Semigroups/InteractionPictureAsymptotics.result`
