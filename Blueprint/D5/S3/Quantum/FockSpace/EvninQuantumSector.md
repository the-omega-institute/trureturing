# The exact top eigenvalue in Evnin's finite sectors

## Abstract

Evnin's normally ordered resonant Hamiltonian has greatest real spectral value (N − 1)(N + 2σM)/2 in every nonempty sector for every real σ ≥ 1.

**Definition 1.1 (Ambient modes).**

$$\operatorname{Mode}\left(L\right) = \operatorname{Fin}\left(L + 1\right)$$

*Formalization.* `D5/S3/Quantum/FockSpace/EvninQuantumSector.Mode` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Oleg Evnin (2026). *Quantum estimates for classical polynomial optimization*. DOI: [10.1088/1751-8121/aebddd](https://doi.org/10.1088/1751-8121/aebddd). URL: <https://arxiv.org/html/2607.25445v3>.

*Commentary.*

The natural number L is the largest ambient mode label. A value of Fin(L + 1) has a natural label from 0 through L.

**Definition 1.2 (Fixed particle number and momentum).**

$$\operatorname{Sector}\left(L, N, M\right) = \{eta: \operatorname{Mode}\left(L\right) \to \mathbb{N} | \sum_{i \in \operatorname{Mode}\left(L\right)} eta\left(i\right) = N \land (\sum_{i \in \operatorname{Mode}\left(L\right)} i \cdot eta\left(i\right) = M)\}$$

*Formalization.* `D5/S3/Quantum/FockSpace/EvninQuantumSector.Sector` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Oleg Evnin (2026). *Quantum estimates for classical polynomial optimization*. DOI: [10.1088/1751-8121/aebddd](https://doi.org/10.1088/1751-8121/aebddd). URL: <https://arxiv.org/html/2607.25445v3>.

*Commentary.*

The sector is a subtype of occupation functions on Mode(L). The first sum fixes particle number and the second fixes momentum using the natural mode labels. The Hamiltonian acts on Sector(M, N, M) in the normalized bosonic basis of Eq. (22).

**Definition 1.3 (Finite occupation sectors).**

$$\operatorname{instFintypeSector}\left(L, N, M\right) : \operatorname{Fintype}\left(\operatorname{Sector}\left(L, N, M\right)\right)$$

*Formalization.* `D5/S3/Quantum/FockSpace/EvninQuantumSector.instFintypeSector` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Oleg Evnin (2026). *Quantum estimates for classical polynomial optimization*. DOI: [10.1088/1751-8121/aebddd](https://doi.org/10.1088/1751-8121/aebddd). URL: <https://arxiv.org/html/2607.25445v3>.

*Commentary.*

The Fintype instance uses Fintype.ofInjective on the map that sends each occupation to its coordinate function into Fin(N + 1). Each occupation is at most its total N, and equality of the bounded functions gives equality of the occupations.

**Definition 1.4 (Decidable sector equality).**

$$\operatorname{instDecidableEqSector}\left(L, N, M\right) : \operatorname{DecidableEq}\left(\operatorname{Sector}\left(L, N, M\right)\right)$$

*Formalization.* `D5/S3/Quantum/FockSpace/EvninQuantumSector.instDecidableEqSector` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Oleg Evnin (2026). *Quantum estimates for classical polynomial optimization*. DOI: [10.1088/1751-8121/aebddd](https://doi.org/10.1088/1751-8121/aebddd). URL: <https://arxiv.org/html/2607.25445v3>.

*Commentary.*

The equality instance is Classical.decEq on Sector(L, N, M).

**Definition 1.5 (Raney coefficients).**

$$\operatorname{raney}\left(s, r, j\right) = \frac{r \cdot \Gamma\left(s \cdot j + r\right)}{\Gamma\left(\left(s - 1\right) \cdot j + r + 1\right) \cdot \Gamma\left(j + 1\right)}$$

*Formalization.* `D5/S3/Quantum/FockSpace/EvninQuantumSector.raney` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Oleg Evnin (2026). *Quantum estimates for classical polynomial optimization*. DOI: [10.1088/1751-8121/aebddd](https://doi.org/10.1088/1751-8121/aebddd). URL: <https://arxiv.org/html/2607.25445v3>.

*Commentary.*

Equation (31) gives this Gamma quotient with real parameters s and r and natural index j. The Hamiltonian and its eigenvector use r = 1. The convolution in the proof also uses r = 2.

**Definition 1.6 (Energy of the attaining state).**

$$\operatorname{energy}\left(s, N, M\right) = \frac{\left((N: \mathbb{R}) - 1\right) \cdot \left((N: \mathbb{R}) + 2 \cdot s \cdot (M: \mathbb{R})\right)}{2}$$

*Formalization.* `D5/S3/Quantum/FockSpace/EvninQuantumSector.energy` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Oleg Evnin (2026). *Quantum estimates for classical polynomial optimization*. DOI: [10.1088/1751-8121/aebddd](https://doi.org/10.1088/1751-8121/aebddd). URL: <https://arxiv.org/html/2607.25445v3>.

*Commentary.*

Both N and M are cast from natural numbers to real numbers before the arithmetic of Eq. (33).

**Definition 1.7 (Factorial occupation vector).**

$$\operatorname{occupationVector}\left(A, eta\right) = (\prod_{i \in \operatorname{Mode}\left(L\right)} \frac{\sqrt{A\left(i\right)}^{eta\left(i\right)}}{\sqrt{(eta\left(i\right))!}}: \mathbb{C})$$

*Formalization.* `D5/S3/Quantum/FockSpace/EvninQuantumSector.occupationVector` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Oleg Evnin (2026). *Quantum estimates for classical polynomial optimization*. DOI: [10.1088/1751-8121/aebddd](https://doi.org/10.1088/1751-8121/aebddd). URL: <https://arxiv.org/html/2607.25445v3>.

*Commentary.*

For real mode weights A, each coordinate is computed in the reals and cast to the complex numbers. In the theorem, A(i) is raney(s, 1, i) and the vector is indexed by Sector(M, N, M).

**Definition 1.8 (Normally ordered Hamiltonian).**

$$\begin{aligned}A_{j} = \operatorname{raney}\left(s, 1, j\right),\quad c_{j} = \frac{1 + \frac{j \cdot \left(s - 1\right)}{2}}{A_{j}}\\w_{j,k} = \sqrt{A_{k} \cdot A_{j - k}}\\\operatorname{hamiltonian}\left(s, N, M\right) = \sum_{j \in \operatorname{Mode}\left(M\right)} \frac{c_{j}}{2} \cdot \sum_{k \in \operatorname{Fin}\left(j + 1\right)} \sum_{l \in \operatorname{Fin}\left(j + 1\right)} w_{j,k} \cdot w_{j,l} \cdot \left(B_{j,k}\right)^{*} \cdot B_{j,l}\quad\operatorname{if} 2 \le N\\\operatorname{hamiltonian}\left(s, N, M\right) = 0\quad\operatorname{if} N < 2\end{aligned}$$

*Formalization.* `D5/S3/Quantum/FockSpace/EvninQuantumSector.hamiltonian` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Oleg Evnin (2026). *Quantum estimates for classical polynomial optimization*. DOI: [10.1088/1751-8121/aebddd](https://doi.org/10.1088/1751-8121/aebddd). URL: <https://arxiv.org/html/2607.25445v3>.

*Commentary.*

For N at least two, B with indices j and k is the ordered annihilator for modes k and j − k. Its columns are indexed by Sector(M, N, M), and its rows by Sector(M, N − 2, M − j). The entry at row ζ and column η vanishes unless η is obtained by adding both particles to ζ. In that case the entry is the real square root of η(k) times η(j − k) for distinct modes, with the entire product under the root. For equal modes the radicand is η(k)(η(k) − 1). Both orders of a distinct-mode pair occur in the ordered sums from Eqs. (19) and (30).

**Definition 1.9 (Proposition on the top spectral value).**

$$claim \Leftrightarrow (\forall s \in \mathbb{R},\; (1 \le s) \Rightarrow (\forall N \in \mathbb{N},\; \forall M \in \mathbb{N},\; (\operatorname{Nonempty}\left(\operatorname{Sector}\left(M, N, M\right)\right)) \Rightarrow (\operatorname{IsHermitian}\left(\operatorname{hamiltonian}\left(s, N, M\right)\right) \land (\operatorname{IsGreatest}\left(\operatorname{spectrum}\left(\mathbb{R}, \operatorname{hamiltonian}\left(s, N, M\right)\right), \operatorname{energy}\left(s, N, M\right)\right) \land (\operatorname{occupationVector}\left(\operatorname{raney}\left(s, 1\right)\right) \ne 0 \land (\operatorname{mulVec}\left(\operatorname{hamiltonian}\left(s, N, M\right), \operatorname{occupationVector}\left(\operatorname{raney}\left(s, 1\right)\right)\right) = \operatorname{smul}\left(\operatorname{energy}\left(s, N, M\right), \operatorname{occupationVector}\left(\operatorname{raney}\left(s, 1\right)\right)\right)))))))$$

*Formalization.* `D5/S3/Quantum/FockSpace/EvninQuantumSector.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Oleg Evnin (2026). *Quantum estimates for classical polynomial optimization*. DOI: [10.1088/1751-8121/aebddd](https://doi.org/10.1088/1751-8121/aebddd). URL: <https://arxiv.org/html/2607.25445v3>.

*Commentary.*

Write s for σ. The assertion ranges over nonempty sectors, including the one-particle sectors and the vacuum of zero momentum. The displayed occupation vector uses the implicit sector indices (M, N, M). Greatest means that the energy belongs to the real spectrum and is an upper bound for it.

**Theorem 1.10 (Spectral bound and attainment).**

$$\forall s \in \mathbb{R},\; (1 \le s) \Rightarrow (\forall N \in \mathbb{N},\; \forall M \in \mathbb{N},\; (\operatorname{Nonempty}\left(\operatorname{Sector}\left(M, N, M\right)\right)) \Rightarrow (\operatorname{IsHermitian}\left(\operatorname{hamiltonian}\left(s, N, M\right)\right) \land (\operatorname{IsGreatest}\left(\operatorname{spectrum}\left(\mathbb{R}, \operatorname{hamiltonian}\left(s, N, M\right)\right), \operatorname{energy}\left(s, N, M\right)\right) \land (\operatorname{occupationVector}\left(\operatorname{raney}\left(s, 1\right)\right) \ne 0 \land (\operatorname{mulVec}\left(\operatorname{hamiltonian}\left(s, N, M\right), \operatorname{occupationVector}\left(\operatorname{raney}\left(s, 1\right)\right)\right) = \operatorname{smul}\left(\operatorname{energy}\left(s, N, M\right), \operatorname{occupationVector}\left(\operatorname{raney}\left(s, 1\right)\right)\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FockSpace/EvninQuantumSector.top_finite_sector_eigenvalue` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Oleg Evnin (2026). *Quantum estimates for classical polynomial optimization*. DOI: [10.1088/1751-8121/aebddd](https://doi.org/10.1088/1751-8121/aebddd). URL: <https://arxiv.org/html/2607.25445v3>.

*Commentary.*

Each pair annihilator gives a diagonal matrix when multiplied by its adjoint on the left. Each removable column has exactly one lower occupation, and distinct columns cannot share that row. An impossible removal contributes zero, including when the lower sector is empty. Summing the ordered diagonal counts gives N(N − 1), and weighting by pair momentum gives 2M(N − 1). Thus half the sum with block weights 1 + σj is E times the identity.

Lagrange–Bürmann applied to the formal solution T of T = X(1 + T)^σ identifies the coefficients of (1 + T)^r for r = 1, 2 with the Gamma quotients of Eq. (31). The Cauchy product and the Gamma recurrence give cⱼ times the sum of wⱼₖ squared equal to 1 + σj. Expanding the weighted Gram identity writes E times the identity minus H as a sum of adjoint squares with weights cⱼ/4. Its pair differences are wⱼₖ times the lth pair minus wⱼₗ times the kth pair. Each coefficient is nonnegative, so the real spectrum is bounded above by E.

Adding one particle replaces its factorial by the next factorial. The square-root ratio cancels the coefficient of the corresponding annihilator. Applying this twice gives wⱼₖ times the same lower-sector vector for every kth pair, including a repeated mode. Every difference therefore kills v. All its coordinates are positive before casting to complex numbers, so v is nonzero in every nonempty sector. This gives the eigenvalue E and proves attainment. With fewer than two particles the nonempty sectors have zero energy.

## References

- Truth anchor: `D5/S3/Quantum/FockSpace/EvninQuantumSector.Mode`
- Truth anchor: `D5/S3/Quantum/FockSpace/EvninQuantumSector.Sector`
- Truth anchor: `D5/S3/Quantum/FockSpace/EvninQuantumSector.claim`
- Truth anchor: `D5/S3/Quantum/FockSpace/EvninQuantumSector.energy`
- Truth anchor: `D5/S3/Quantum/FockSpace/EvninQuantumSector.hamiltonian`
- Truth anchor: `D5/S3/Quantum/FockSpace/EvninQuantumSector.instDecidableEqSector`
- Truth anchor: `D5/S3/Quantum/FockSpace/EvninQuantumSector.instFintypeSector`
- Truth anchor: `D5/S3/Quantum/FockSpace/EvninQuantumSector.occupationVector`
- Truth anchor: `D5/S3/Quantum/FockSpace/EvninQuantumSector.raney`
- Truth anchor: `D5/S3/Quantum/FockSpace/EvninQuantumSector.top_finite_sector_eigenvalue`
- Dependency: [D5/S3/Combinatorics/WeightedBond/LagrangeBurmann](../../Combinatorics/WeightedBond/LagrangeBurmann.md)
