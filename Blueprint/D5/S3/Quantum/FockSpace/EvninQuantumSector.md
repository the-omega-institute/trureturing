# The exact top eigenvalue in Evnin's finite sectors

## Abstract

Evnin's normally ordered resonant Hamiltonian has greatest real spectral value (N − 1)(N + 2σM)/2 in every nonempty sector for every real σ ≥ 1.

**Definition 1.1 (The weighted sector and its spectral value).**

$$claim \Leftrightarrow (\forall s \in \mathbb{R},\; (1 \le s) \Rightarrow (\forall N \in \mathbb{N},\; \forall M \in \mathbb{N},\; (\operatorname{Nonempty}\left(\operatorname{Sector}\left(M, N, M\right)\right)) \Rightarrow (\operatorname{IsHermitian}\left(\operatorname{hamiltonian}\left(s, N, M\right)\right) \land (\operatorname{IsGreatest}\left(\operatorname{spectrum}\left(\mathbb{R}, \operatorname{hamiltonian}\left(s, N, M\right)\right), \frac{((N: \mathbb{R}) - 1) \cdot ((N: \mathbb{R}) + 2 \cdot s \cdot (M: \mathbb{R}))}{2}\right) \land (\operatorname{occupationVector}\left(\operatorname{raney}\left(s, 1\right)\right) \ne 0 \land (\operatorname{mulVec}\left(\operatorname{hamiltonian}\left(s, N, M\right), \operatorname{occupationVector}\left(\operatorname{raney}\left(s, 1\right)\right)\right) = \operatorname{smul}\left(\frac{((N: \mathbb{R}) - 1) \cdot ((N: \mathbb{R}) + 2 \cdot s \cdot (M: \mathbb{R}))}{2}, \operatorname{occupationVector}\left(\operatorname{raney}\left(s, 1\right)\right)\right)))))))$$

*Formalization.* `D5/S3/Quantum/FockSpace/EvninQuantumSector.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Oleg Evnin (2026). *Quantum estimates for classical polynomial optimization*. DOI: [10.1088/1751-8121/aebddd](https://doi.org/10.1088/1751-8121/aebddd). URL: <https://arxiv.org/html/2607.25445v3>.

*Commentary.*

Write s for σ. The sector is indexed by natural occupations η on modes 0 through M with sum N and momentum sum M. Each coordinate is in the normalized bosonic basis of Eq. (22). For N at least two, the ordered annihilator for modes k and j − k maps into particle number N − 2 and momentum M − j on the same mode list. Its matrix entry is zero unless the column is obtained by adding the two particles to the row. The entry is then the square root of the product of their occupations in distinct modes, or the square root of ηₖ(ηₖ − 1) in the repeated mode.

Write Aⱼ for the Eq. (31) Gamma quotient at r = 1, cⱼ for (1 + j(σ − 1)/2)/Aⱼ, and wⱼₖ for √(AₖAⱼ₋ₖ). The matrix H is the ordered sum from Eqs. (19) and (30), with both pair indices running from 0 to j, and with coefficient cⱼwⱼₖwⱼₗ/2 on the product of the kth pair adjoint and the lth pair. A pair of momentum above M cannot be removed. For N below two H is zero. The vector v has coordinate given by the product over all modes i of √Aᵢ to the power ηᵢ divided by √(ηᵢ!). The numbers N and M in the energy are real casts. The assertion ranges over nonempty sectors, including the one-particle sector and the vacuum of zero momentum.

**Theorem 1.2 (Spectral bound and attainment).**

$$\forall s \in \mathbb{R},\; (1 \le s) \Rightarrow (\forall N \in \mathbb{N},\; \forall M \in \mathbb{N},\; (\operatorname{Nonempty}\left(\operatorname{Sector}\left(M, N, M\right)\right)) \Rightarrow (\operatorname{IsHermitian}\left(\operatorname{hamiltonian}\left(s, N, M\right)\right) \land (\operatorname{IsGreatest}\left(\operatorname{spectrum}\left(\mathbb{R}, \operatorname{hamiltonian}\left(s, N, M\right)\right), \frac{((N: \mathbb{R}) - 1) \cdot ((N: \mathbb{R}) + 2 \cdot s \cdot (M: \mathbb{R}))}{2}\right) \land (\operatorname{occupationVector}\left(\operatorname{raney}\left(s, 1\right)\right) \ne 0 \land (\operatorname{mulVec}\left(\operatorname{hamiltonian}\left(s, N, M\right), \operatorname{occupationVector}\left(\operatorname{raney}\left(s, 1\right)\right)\right) = \operatorname{smul}\left(\frac{((N: \mathbb{R}) - 1) \cdot ((N: \mathbb{R}) + 2 \cdot s \cdot (M: \mathbb{R}))}{2}, \operatorname{occupationVector}\left(\operatorname{raney}\left(s, 1\right)\right)\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FockSpace/EvninQuantumSector.top_finite_sector_eigenvalue` (`✓ std3`). ∎

*Resolves.* `Problems/evnin-2026-quantum-sector-maximum` (proved) by `D5/S3/Quantum/FockSpace/EvninQuantumSector.top_finite_sector_eigenvalue`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"evnin-2026-quantum-sector-maximum","declaration_gid":"D5/S3/Quantum/FockSpace/EvninQuantumSector.top_finite_sector_eigenvalue","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Oleg Evnin (2026). *Quantum estimates for classical polynomial optimization*. DOI: [10.1088/1751-8121/aebddd](https://doi.org/10.1088/1751-8121/aebddd). URL: <https://arxiv.org/html/2607.25445v3>.

*Commentary.*

Each pair annihilator gives a diagonal matrix when multiplied by its adjoint on the left. Each removable column has exactly one lower occupation, and distinct columns cannot share that row. An impossible removal contributes zero, including when the lower sector is empty. Summing the ordered diagonal counts gives N(N − 1), and weighting by pair momentum gives 2M(N − 1). Thus half the sum with block weights 1 + σj is E times the identity.

Lagrange–Bürmann applied to the formal solution T of T = X(1 + T)^σ identifies the coefficients of (1 + T)^r for r = 1, 2 with the Gamma quotients of Eq. (31). The Cauchy product and the Gamma recurrence give cⱼ times the sum of wⱼₖ squared equal to 1 + σj. Expanding the weighted Gram identity writes E times the identity minus H as a sum of adjoint squares with weights cⱼ/4. Its pair differences are wⱼₖ times the lth pair minus wⱼₗ times the kth pair. Each coefficient is nonnegative, so the real spectrum is bounded above by E.

Adding one particle replaces its factorial by the next factorial. The square-root ratio cancels the coefficient of the corresponding annihilator. Applying this twice gives wⱼₖ times the same lower-sector vector for every kth pair, including a repeated mode. Every difference therefore kills v. All its coordinates are positive before casting to complex numbers, so v is nonzero in every nonempty sector. This gives the eigenvalue E and proves attainment. With fewer than two particles the nonempty sectors have zero energy.

## References

- Truth anchor: `D5/S3/Quantum/FockSpace/EvninQuantumSector.claim`
- Truth anchor: `D5/S3/Quantum/FockSpace/EvninQuantumSector.top_finite_sector_eigenvalue`
- Dependency: [D5/S3/Combinatorics/WeightedBond/LagrangeBurmann](../../Combinatorics/WeightedBond/LagrangeBurmann.md)
