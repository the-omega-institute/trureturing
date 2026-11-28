# The exact top eigenvalue in Evnin's finite sectors

## Abstract

Evnin's normally ordered resonant Hamiltonian has greatest real spectral value (N − 1)(N + 2σM)/2 in every nonempty sector for every real σ ≥ 1.

**Definition 1.1 (Ambient modes).**

$$\forall (L: \mathbb{N}), \operatorname{Mode}\left(L\right) = \operatorname{Fin}\left(L + 1\right)$$

*Formalization.* `D5/S3/Quantum/FockSpace/EvninQuantumSector.Mode` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Oleg Evnin (2026). *Quantum estimates for classical polynomial optimization*. DOI: [10.1088/1751-8121/aebddd](https://doi.org/10.1088/1751-8121/aebddd). URL: <https://arxiv.org/html/2607.25445v3>.

*Commentary.*

The natural number L is the largest ambient mode label. A value of Fin(L + 1) has a natural label from 0 through L.

**Definition 1.2 (Fixed particle number and momentum).**

$$\forall (L: \mathbb{N})(N: \mathbb{N})(M: \mathbb{N}), \operatorname{Sector}\left(L, N, M\right) = \{eta: \operatorname{Mode}\left(L\right) \to \mathbb{N} \mid \sum_{i \in \operatorname{Mode}\left(L\right)} eta\left(i\right) = N \land (\sum_{i \in \operatorname{Mode}\left(L\right)} \operatorname{val}\left(i\right) \cdot eta\left(i\right) = M)\}$$

*Formalization.* `D5/S3/Quantum/FockSpace/EvninQuantumSector.Sector` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Oleg Evnin (2026). *Quantum estimates for classical polynomial optimization*. DOI: [10.1088/1751-8121/aebddd](https://doi.org/10.1088/1751-8121/aebddd). URL: <https://arxiv.org/html/2607.25445v3>.

*Commentary.*

The sector is a subtype of occupation functions on Mode(L). The first sum fixes particle number and the second fixes momentum using the natural mode labels. The Hamiltonian acts on Sector(M, N, M) in the normalized bosonic basis of Eq. (22).

**Definition 1.3 (Finite occupation sectors).**

$$\forall (L: \mathbb{N})(N: \mathbb{N})(M: \mathbb{N}), (\operatorname{instFintypeSector}\left(L, N, M\right): \operatorname{Fintype}\left(\operatorname{Sector}\left(L, N, M\right)\right))$$

*Formalization.* `D5/S3/Quantum/FockSpace/EvninQuantumSector.instFintypeSector` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Oleg Evnin (2026). *Quantum estimates for classical polynomial optimization*. DOI: [10.1088/1751-8121/aebddd](https://doi.org/10.1088/1751-8121/aebddd). URL: <https://arxiv.org/html/2607.25445v3>.

*Commentary.*

The Fintype instance uses Fintype.ofInjective on the map that sends each occupation to its coordinate function into Fin(N + 1). Each occupation is at most its total N, and equality of the bounded functions gives equality of the occupations.

**Definition 1.4 (Decidable sector equality).**

$$\forall (L: \mathbb{N})(N: \mathbb{N})(M: \mathbb{N}), (\operatorname{instDecidableEqSector}\left(L, N, M\right): \operatorname{DecidableEq}\left(\operatorname{Sector}\left(L, N, M\right)\right))$$

*Formalization.* `D5/S3/Quantum/FockSpace/EvninQuantumSector.instDecidableEqSector` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Oleg Evnin (2026). *Quantum estimates for classical polynomial optimization*. DOI: [10.1088/1751-8121/aebddd](https://doi.org/10.1088/1751-8121/aebddd). URL: <https://arxiv.org/html/2607.25445v3>.

*Commentary.*

The equality instance is Classical.decEq on Sector(L, N, M).

**Definition 1.5 (Raney coefficients).**

$$\forall (s: \mathbb{R})(r: \mathbb{R})(j: \mathbb{N}), \operatorname{raney}\left(s, r, j\right) = \frac{r \cdot \Gamma\left(s \cdot \left(\operatorname{cast}_{\mathbb{R}}\right)\left(j\right) + r\right)}{\Gamma\left(\left(s - 1\right) \cdot \left(\operatorname{cast}_{\mathbb{R}}\right)\left(j\right) + r + 1\right) \cdot \Gamma\left(\left(\operatorname{cast}_{\mathbb{R}}\right)\left(j\right) + 1\right)}$$

*Formalization.* `D5/S3/Quantum/FockSpace/EvninQuantumSector.raney` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Oleg Evnin (2026). *Quantum estimates for classical polynomial optimization*. DOI: [10.1088/1751-8121/aebddd](https://doi.org/10.1088/1751-8121/aebddd). URL: <https://arxiv.org/html/2607.25445v3>.

*Commentary.*

Equation (31) gives this Gamma quotient with real parameters s and r and natural index j. The Hamiltonian and its eigenvector use r = 1. The convolution in the proof also uses r = 2.

**Definition 1.6 (Energy of the attaining state).**

$$\forall (s: \mathbb{R})(N: \mathbb{N})(M: \mathbb{N}), \operatorname{energy}\left(s, N, M\right) = \frac{\left(\left(\operatorname{cast}_{\mathbb{R}}\right)\left(N\right) - 1\right) \cdot \left(\left(\operatorname{cast}_{\mathbb{R}}\right)\left(N\right) + 2 \cdot s \cdot \left(\operatorname{cast}_{\mathbb{R}}\right)\left(M\right)\right)}{2}$$

*Formalization.* `D5/S3/Quantum/FockSpace/EvninQuantumSector.energy` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Oleg Evnin (2026). *Quantum estimates for classical polynomial optimization*. DOI: [10.1088/1751-8121/aebddd](https://doi.org/10.1088/1751-8121/aebddd). URL: <https://arxiv.org/html/2607.25445v3>.

*Commentary.*

Both N and M are cast from natural numbers to real numbers before the arithmetic of Eq. (33).

**Definition 1.7 (Factorial occupation vector).**

$$\forall (L: \mathbb{N})(N: \mathbb{N})(M: \mathbb{N})(A: \mathbb{N} \to \mathbb{R})(eta: \operatorname{Sector}\left(L, N, M\right)), \operatorname{occupationVector}\left(A, eta\right) = \operatorname{Complex.ofReal}\left(\prod_{i \in \operatorname{Mode}\left(L\right)} \frac{\sqrt{A\left(\operatorname{val}\left(i\right)\right)}^{\operatorname{val}\left(eta\right)\left(i\right)}}{\sqrt{\left(\operatorname{cast}_{\mathbb{R}}\right)\left((\operatorname{val}\left(eta\right)\left(i\right))!\right)}}\right)$$

*Formalization.* `D5/S3/Quantum/FockSpace/EvninQuantumSector.occupationVector` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Oleg Evnin (2026). *Quantum estimates for classical polynomial optimization*. DOI: [10.1088/1751-8121/aebddd](https://doi.org/10.1088/1751-8121/aebddd). URL: <https://arxiv.org/html/2607.25445v3>.

*Commentary.*

For real mode weights A, each coordinate is computed in the reals and cast to the complex numbers. In the theorem, A(t) is raney(s, 1, t) for each natural label t, and the vector is indexed by Sector(M, N, M).

**Definition 1.8 (Normally ordered Hamiltonian).**

$$\begin{aligned}&\forall (s: \mathbb{R})(N: \mathbb{N})(M: \mathbb{N}), \operatorname{let}\\&\quad A := \lambda (t: \mathbb{N}) \mapsto \operatorname{raney}\left(s, 1, t\right),\\&\quad c := \lambda (t: \mathbb{N}) \mapsto \frac{1 + \frac{\left(\operatorname{cast}_{\mathbb{R}}\right)\left(t\right) \cdot \left(s - 1\right)}{2}}{A\left(t\right)},\\&\quad w := \lambda (j: \operatorname{Mode}\left(M\right))(k: \operatorname{Fin}\left(\operatorname{val}\left(j\right) + 1\right)) \mapsto \sqrt{A\left(\operatorname{val}\left(k\right)\right) \cdot A\left((\operatorname{val}\left(j\right) - \operatorname{val}\left(k\right))_{\mathbb{N}}\right)} \operatorname{in}\\&\quad\operatorname{hamiltonian}\left(s, N, M\right) = \operatorname{if} 2 \le N \operatorname{then}\\&\qquad\operatorname{let} B := \lambda (j: \operatorname{Mode}\left(M\right))(k: \operatorname{Fin}\left(\operatorname{val}\left(j\right) + 1\right)) \mapsto \operatorname{let} u := \langle\operatorname{val}\left(k\right)\rangle_{\operatorname{Mode}\left(M\right)},\quad v := \langle(\operatorname{val}\left(j\right) - \operatorname{val}\left(k\right))_{\mathbb{N}}\rangle_{\operatorname{Mode}\left(M\right)} \operatorname{in}\\&\qquad\lambda (\zeta: \operatorname{Sector}\left(M, (N - 2)_{\mathbb{N}}, (M - \operatorname{val}\left(j\right))_{\mathbb{N}}\right))(eta: \operatorname{Sector}\left(M, N, M\right)) \mapsto \operatorname{if} (\forall (i: \operatorname{Mode}\left(M\right)), \operatorname{val}\left(eta\right)\left(i\right) = \operatorname{val}\left(\zeta\right)\left(i\right) + [i = u]_{\mathbb{N}} + [i = v]_{\mathbb{N}})\\&\qquad\quad\operatorname{then} \operatorname{Complex.ofReal}\left(\sqrt{\left(\operatorname{cast}_{\mathbb{R}}\right)\left(\operatorname{val}\left(eta\right)\left(u\right)\right) \cdot \left(\left(\operatorname{cast}_{\mathbb{R}}\right)\left(\operatorname{val}\left(eta\right)\left(v\right)\right) - [u = v]_{\mathbb{R}}\right)}\right)\quad\operatorname{else} 0\\&\qquad\operatorname{in} \sum_{j \in \operatorname{Mode}\left(M\right)} \operatorname{smul}\left(\frac{c\left(\operatorname{val}\left(j\right)\right)}{2}, \sum_{k \in \operatorname{Fin}\left(\operatorname{val}\left(j\right) + 1\right)} \sum_{l \in \operatorname{Fin}\left(\operatorname{val}\left(j\right) + 1\right)} \operatorname{smul}\left(w\left(j, k\right) \cdot w\left(j, l\right), B\left(j, k\right)^{*} \cdot B\left(j, l\right)\right)\right)\\&\quad\operatorname{else} 0\end{aligned}$$

*Formalization.* `D5/S3/Quantum/FockSpace/EvninQuantumSector.hamiltonian` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Oleg Evnin (2026). *Quantum estimates for classical polynomial optimization*. DOI: [10.1088/1751-8121/aebddd](https://doi.org/10.1088/1751-8121/aebddd). URL: <https://arxiv.org/html/2607.25445v3>.

*Commentary.*

For N at least two, B is the ordered pair annihilation matrix. Angle brackets denote the element of Mode(M) with the indicated natural label. The bracketed equalities in the entry formula are indicators, with value one when true and zero otherwise. The adjoint is conjugate transpose, and smul is the real scalar action on complex matrices. Both orders of a distinct-mode pair occur in the sums from Eqs. (19) and (30).

**Definition 1.9 (Proposition on the top spectral value).**

$$claim \Leftrightarrow (\forall (s: \mathbb{R}), (1 \le s) \Rightarrow (\forall (N: \mathbb{N})(M: \mathbb{N})[\operatorname{Nonempty}\left(\operatorname{Sector}\left(M, N, M\right)\right)], \operatorname{IsHermitian}\left(\operatorname{hamiltonian}\left(s, N, M\right)\right) \land (\operatorname{IsGreatest}\left(\operatorname{spectrum}\left(\mathbb{R}, \operatorname{hamiltonian}\left(s, N, M\right)\right), \operatorname{energy}\left(s, N, M\right)\right) \land ((\operatorname{occupationVector}\left(\operatorname{raney}\left(s, 1\right)\right): \operatorname{Sector}\left(M, N, M\right) \to \mathbb{C}) \ne 0 \land (\operatorname{mulVec}\left(\operatorname{hamiltonian}\left(s, N, M\right), (\operatorname{occupationVector}\left(\operatorname{raney}\left(s, 1\right)\right): \operatorname{Sector}\left(M, N, M\right) \to \mathbb{C})\right) = \operatorname{smul}\left(\operatorname{energy}\left(s, N, M\right), (\operatorname{occupationVector}\left(\operatorname{raney}\left(s, 1\right)\right): \operatorname{Sector}\left(M, N, M\right) \to \mathbb{C})\right))))))$$

*Formalization.* `D5/S3/Quantum/FockSpace/EvninQuantumSector.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Oleg Evnin (2026). *Quantum estimates for classical polynomial optimization*. DOI: [10.1088/1751-8121/aebddd](https://doi.org/10.1088/1751-8121/aebddd). URL: <https://arxiv.org/html/2607.25445v3>.

*Commentary.*

Write s for σ. The assertion ranges over nonempty sectors, including the one-particle sectors and the vacuum of zero momentum. Greatest means that the energy belongs to the real spectrum and is an upper bound for it.

**Theorem 1.10 (Spectral bound and attainment).**

$$\forall (s: \mathbb{R}), (1 \le s) \Rightarrow (\forall (N: \mathbb{N})(M: \mathbb{N})[\operatorname{Nonempty}\left(\operatorname{Sector}\left(M, N, M\right)\right)], \operatorname{IsHermitian}\left(\operatorname{hamiltonian}\left(s, N, M\right)\right) \land (\operatorname{IsGreatest}\left(\operatorname{spectrum}\left(\mathbb{R}, \operatorname{hamiltonian}\left(s, N, M\right)\right), \operatorname{energy}\left(s, N, M\right)\right) \land ((\operatorname{occupationVector}\left(\operatorname{raney}\left(s, 1\right)\right): \operatorname{Sector}\left(M, N, M\right) \to \mathbb{C}) \ne 0 \land (\operatorname{mulVec}\left(\operatorname{hamiltonian}\left(s, N, M\right), (\operatorname{occupationVector}\left(\operatorname{raney}\left(s, 1\right)\right): \operatorname{Sector}\left(M, N, M\right) \to \mathbb{C})\right) = \operatorname{smul}\left(\operatorname{energy}\left(s, N, M\right), (\operatorname{occupationVector}\left(\operatorname{raney}\left(s, 1\right)\right): \operatorname{Sector}\left(M, N, M\right) \to \mathbb{C})\right)))))$$

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
