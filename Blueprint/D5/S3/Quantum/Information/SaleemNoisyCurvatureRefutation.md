# Noisy entanglement curvature can exceed quantum Fisher information

## Abstract

A two-qubit amplitude-damped probe starting at diag(1,11,3,1)/16 has smooth concurrence curvature 1 and quantum Fisher information 8/15 at t=1, kappa=log 2 and g=pi/4.

**Definition 1.1 (First amplitude-damping jump).**

$$jump1 = \operatorname{kroneckerMap}\left(\operatorname{fun} x:\mathbb{C} \mapsto \operatorname{fun} y:\mathbb{C} \mapsto x \cdot y, sigmaMinus, (1:\operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right))\right)$$

*Formalization.* `D5/S3/Quantum/Information/SaleemNoisyCurvatureRefutation.jump1` (`✓ std3`).

*Citation.* Zain H. Saleem; Anil Shaji; Anjala M. Babu; Da-Wei Luo; Quinn Langfitt; Ting Yu; Stephen K. Gray (2025). *Quantum Fisher Information and the Curvature of Entanglement*. DOI: [10.48550/arXiv.2504.13729](https://doi.org/10.48550/arXiv.2504.13729). URL: <https://arxiv.org/abs/2504.13729>.

*Commentary.*

Equation (41), p. 8, and Appendix B use the jump operators σ₋ on the two qubits, with σ₋ = (σx − iσy)/2. The computational basis is |ij⟩ indexed by (i,j) in Fin 2 × Fin 2. The reused sigmaMinus is the matrix [[0,0],[1,0]], so this is σ₋ ⊗ I.

**Definition 1.2 (Second amplitude-damping jump).**

$$jump2 = \operatorname{kroneckerMap}\left(\operatorname{fun} x:\mathbb{C} \mapsto \operatorname{fun} y:\mathbb{C} \mapsto x \cdot y, (1:\operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)), sigmaMinus\right)$$

*Formalization.* `D5/S3/Quantum/Information/SaleemNoisyCurvatureRefutation.jump2` (`✓ std3`).

*Citation.* Zain H. Saleem; Anil Shaji; Anjala M. Babu; Da-Wei Luo; Quinn Langfitt; Ting Yu; Stephen K. Gray (2025). *Quantum Fisher Information and the Curvature of Entanglement*. DOI: [10.48550/arXiv.2504.13729](https://doi.org/10.48550/arXiv.2504.13729). URL: <https://arxiv.org/abs/2504.13729>.

*Commentary.*

Equation (41), p. 8: the second jump is I ⊗ σ₋. Both identity matrices are complex two-by-two matrices.

**Definition 1.3 (Flip-flop Hamiltonian).**

$$\forall g:\mathbb{R}, \operatorname{hamiltonian}\left(g\right) = \operatorname{fun} a:(\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)) \mapsto \operatorname{fun} b:(\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)) \mapsto \operatorname{if} ((a = (0,1)) \land (b = (1,0))) \lor ((a = (1,0)) \land (b = (0,1))) \operatorname{then} (\operatorname{val}\left(g\right):\mathbb{C}) \operatorname{else} 0$$

*Formalization.* `D5/S3/Quantum/Information/SaleemNoisyCurvatureRefutation.hamiltonian` (`✓ std3`).

*Citation.* Zain H. Saleem; Anil Shaji; Anjala M. Babu; Da-Wei Luo; Quinn Langfitt; Ting Yu; Stephen K. Gray (2025). *Quantum Fisher Information and the Curvature of Entanglement*. DOI: [10.48550/arXiv.2504.13729](https://doi.org/10.48550/arXiv.2504.13729). URL: <https://arxiv.org/abs/2504.13729>.

*Commentary.*

Equation (21), p. 4, specialized to etaXY=1: Hprobe = g(σ₋⁽¹⁾σ₊⁽²⁾ + σ₊⁽¹⁾σ₋⁽²⁾). Its only nonzero entries are g at (01,10) and (10,01). The complex cast of g is displayed explicitly.

**Definition 1.4 (Lindblad dissipator).**

$$\forall O:\operatorname{Matrix}\left((\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), (\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), \mathbb{C}\right), \forall rho:\operatorname{Matrix}\left((\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), (\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), \mathbb{C}\right), \operatorname{dissipator}\left(O, rho\right) = O \cdot rho \cdot \operatorname{Matrix}.\operatorname{conjTranspose}\left(O\right) - \operatorname{SMul}.\operatorname{smul}\left((\frac{1}{2}:\mathbb{C}), \operatorname{Matrix}.\operatorname{conjTranspose}\left(O\right) \cdot O \cdot rho + rho \cdot (\operatorname{Matrix}.\operatorname{conjTranspose}\left(O\right) \cdot O)\right)$$

*Formalization.* `D5/S3/Quantum/Information/SaleemNoisyCurvatureRefutation.dissipator` (`✓ std3`).

*Citation.* Zain H. Saleem; Anil Shaji; Anjala M. Babu; Da-Wei Luo; Quinn Langfitt; Ting Yu; Stephen K. Gray (2025). *Quantum Fisher Information and the Curvature of Entanglement*. DOI: [10.48550/arXiv.2504.13729](https://doi.org/10.48550/arXiv.2504.13729). URL: <https://arxiv.org/abs/2504.13729>.

*Commentary.*

Equation (41), p. 8, defines D[O](rho) = O rho O† − (O† O rho + rho O† O)/2. conjTranspose is the matrix adjoint; the factor 1/2 is a complex scalar acting by smul.

**Definition 1.5 (Open evolution generator).**

$$\forall g:\mathbb{R}, \forall kappa:\mathbb{R}, \forall rho:\operatorname{Matrix}\left((\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), (\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), \mathbb{C}\right), \operatorname{generator}\left(g, kappa, rho\right) = \operatorname{SMul}.\operatorname{smul}\left(-I, \operatorname{hamiltonian}\left(g\right) \cdot rho - rho \cdot \operatorname{hamiltonian}\left(g\right)\right) + \operatorname{SMul}.\operatorname{smul}\left((\operatorname{val}\left(kappa\right):\mathbb{C}), \operatorname{dissipator}\left(jump1, rho\right) + \operatorname{dissipator}\left(jump2, rho\right)\right)$$

*Formalization.* `D5/S3/Quantum/Information/SaleemNoisyCurvatureRefutation.generator` (`✓ std3`).

*Citation.* Zain H. Saleem; Anil Shaji; Anjala M. Babu; Da-Wei Luo; Quinn Langfitt; Ting Yu; Stephen K. Gray (2025). *Quantum Fisher Information and the Curvature of Entanglement*. DOI: [10.48550/arXiv.2504.13729](https://doi.org/10.48550/arXiv.2504.13729). URL: <https://arxiv.org/abs/2504.13729>.

*Commentary.*

Equation (41), p. 8: the commutator term is −i[Hprobe,rho], and the two amplitude-damping dissipators each have rate kappa. The rate is cast to the complex numbers before scalar multiplication.

**Definition 1.6 (Solutions of the initial-value problem).**

$$\forall rhoZero:\operatorname{Matrix}\left((\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), (\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), \mathbb{C}\right), \forall kappa:\mathbb{R}, \forall rho:\mathbb{R} \to \mathbb{R} \to \operatorname{Matrix}\left((\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), (\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), \mathbb{C}\right), \operatorname{IsTrajectory}\left(rhoZero, kappa, rho\right) \Leftrightarrow ((\forall g:\mathbb{R}, rho\left(g, 0\right) = rhoZero) \land (\forall g:\mathbb{R}, \forall t:\mathbb{R}, \forall a:(\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), \forall b:(\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), \operatorname{HasDerivAt}\left(\operatorname{fun} s:\mathbb{R} \mapsto rho\left(g, s, a, b\right), \operatorname{generator}\left(g, kappa, rho\left(g, t\right)\right)\left(a, b\right), t\right)))$$

*Formalization.* `D5/S3/Quantum/Information/SaleemNoisyCurvatureRefutation.IsTrajectory` (`✓ std3`).

*Citation.* Zain H. Saleem; Anil Shaji; Anjala M. Babu; Da-Wei Luo; Quinn Langfitt; Ting Yu; Stephen K. Gray (2025). *Quantum Fisher Information and the Curvature of Entanglement*. DOI: [10.48550/arXiv.2504.13729](https://doi.org/10.48550/arXiv.2504.13729). URL: <https://arxiv.org/abs/2504.13729>.

*Commentary.*

Equation (41), p. 8, with initial state rhoZero independent of g. Every matrix entry has the stated time derivative, for every real g and t. HasDerivAt is the real-variable derivative with complex values.

**Definition 1.7 (Spin-flip matrix).**

$$sigmaYY = \operatorname{kroneckerMap}\left(\operatorname{fun} x:\mathbb{C} \mapsto \operatorname{fun} y:\mathbb{C} \mapsto x \cdot y, (!![0,-I;I,0]:\operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)), (!![0,-I;I,0]:\operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right))\right)$$

*Formalization.* `D5/S3/Quantum/Information/SaleemNoisyCurvatureRefutation.sigmaYY` (`✓ std3`).

*Citation.* Zain H. Saleem; Anil Shaji; Anjala M. Babu; Da-Wei Luo; Quinn Langfitt; Ting Yu; Stephen K. Gray (2025). *Quantum Fisher Information and the Curvature of Entanglement*. DOI: [10.48550/arXiv.2504.13729](https://doi.org/10.48550/arXiv.2504.13729). URL: <https://arxiv.org/abs/2504.13729>.

*Commentary.*

Section II, p. 3, uses σy ⊗ σy in the spin-flip product. Here σy is the complex matrix [[0,−i],[i,0]].

**Definition 1.8 (Wootters concurrence).**

$$\forall rho:\operatorname{Matrix}\left((\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), (\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), \mathbb{C}\right), \operatorname{concurrence}\left(rho\right) = \operatorname{let} l=((((rho \cdot sigmaYY \cdot (rho).\operatorname{map}\left(star\right) \cdot sigmaYY).\operatorname{charpoly}).\operatorname{roots}).\operatorname{map}\left(\operatorname{fun} z:\mathbb{C} \mapsto \operatorname{Real}.\operatorname{sqrt}\left((z).\operatorname{re}\right)\right)).\operatorname{sort}\left(\operatorname{fun} x:\mathbb{R} \mapsto \operatorname{fun} y:\mathbb{R} \mapsto y \le x\right); \operatorname{max}\left(0, (l).\operatorname{getD}\left(0, 0\right) - (l).\operatorname{getD}\left(1, 0\right) - (l).\operatorname{getD}\left(2, 0\right) - (l).\operatorname{getD}\left(3, 0\right)\right)$$

*Formalization.* `D5/S3/Quantum/Information/SaleemNoisyCurvatureRefutation.concurrence` (`✓ std3`).

*Citation.* Zain H. Saleem; Anil Shaji; Anjala M. Babu; Da-Wei Luo; Quinn Langfitt; Ting Yu; Stephen K. Gray (2025). *Quantum Fisher Information and the Curvature of Entanglement*. DOI: [10.48550/arXiv.2504.13729](https://doi.org/10.48550/arXiv.2504.13729). URL: <https://arxiv.org/abs/2504.13729>.

*Commentary.*

Section II, p. 3: 'the λi are the square roots of the eigenvalues, in decreasing order, of the matrix R = ρ(σy ⊗ σy)ρ∗(σy ⊗ σy).' The concurrence formula takes max(0,λ1−λ2−λ3−λ4). The characteristic-polynomial roots retain algebraic multiplicity; map applies sqrt to each real part, then sort orders the resulting real multiset decreasingly. List.getD uses zero-based indices and default zero. The star in Matrix.map conjugates each entry, without transposing.

**Definition 1.9 (Derivative with respect to the coupling).**

$$\forall rho:\mathbb{R} \to \mathbb{R} \to \operatorname{Matrix}\left((\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), (\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), \mathbb{C}\right), \forall g:\mathbb{R}, \forall t:\mathbb{R}, \operatorname{derivG}\left(rho, g, t\right) = \operatorname{Matrix}.\operatorname{of}\left(\operatorname{fun} a:(\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)) \mapsto \operatorname{fun} b:(\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)) \mapsto \operatorname{deriv}\left(\operatorname{fun} h:\mathbb{R} \mapsto rho\left(h, t, a, b\right), g\right)\right)$$

*Formalization.* `D5/S3/Quantum/Information/SaleemNoisyCurvatureRefutation.derivG` (`✓ std3`).

*Citation.* Zain H. Saleem; Anil Shaji; Anjala M. Babu; Da-Wei Luo; Quinn Langfitt; Ting Yu; Stephen K. Gray (2025). *Quantum Fisher Information and the Curvature of Entanglement*. DOI: [10.48550/arXiv.2504.13729](https://doi.org/10.48550/arXiv.2504.13729). URL: <https://arxiv.org/abs/2504.13729>.

*Commentary.*

Section II, equation (7), p. 3: 'we define the curvature of entanglement (CoE) as' CoE ≡ −∂g² C(rho). The matrix derivative here differentiates each entry in g at fixed t; Matrix.of constructs the matrix with those entries.

**Definition 1.10 (Symmetric logarithmic derivative).**

$$\forall rho:\operatorname{Matrix}\left((\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), (\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), \mathbb{C}\right), \forall dRho:\operatorname{Matrix}\left((\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), (\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), \mathbb{C}\right), \forall L:\operatorname{Matrix}\left((\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), (\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), \mathbb{C}\right), \operatorname{IsSLD}\left(rho, dRho, L\right) \Leftrightarrow ((\operatorname{Matrix}.\operatorname{IsHermitian}\left(L\right)) \land (dRho = \operatorname{SMul}.\operatorname{smul}\left((\frac{1}{2}:\mathbb{C}), rho \cdot L + L \cdot rho\right)))$$

*Formalization.* `D5/S3/Quantum/Information/SaleemNoisyCurvatureRefutation.IsSLD` (`✓ std3`).

*Citation.* Zain H. Saleem; Anil Shaji; Anjala M. Babu; Da-Wei Luo; Quinn Langfitt; Ting Yu; Stephen K. Gray (2025). *Quantum Fisher Information and the Curvature of Entanglement*. DOI: [10.48550/arXiv.2504.13729](https://doi.org/10.48550/arXiv.2504.13729). URL: <https://arxiv.org/abs/2504.13729>.

*Commentary.*

Section II, p. 2: the Hermitian SLD L satisfies dRho=(rho L+L rho)/2, and QFI=Tr(rho L²). The displayed predicate includes both Hermiticity and the SLD equation.

**Definition 1.11 (The noisy curvature conjecture).**

$$claim \Leftrightarrow (\forall rhoZero:\operatorname{Matrix}\left((\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), (\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), \mathbb{C}\right), \forall kappa:\mathbb{R}, \forall t:\mathbb{R}, \forall rho:\mathbb{R} \to \mathbb{R} \to \operatorname{Matrix}\left((\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), (\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), \mathbb{C}\right), (\operatorname{IsDensity}\left(rhoZero\right)) \Rightarrow \left((0 < kappa) \Rightarrow \left((0 < t) \Rightarrow \left((\operatorname{IsTrajectory}\left(rhoZero, kappa, rho\right)) \Rightarrow \forall g:\mathbb{R}, (\operatorname{ContDiffAt}\left(\mathbb{R}, 2, \operatorname{fun} h:\mathbb{R} \mapsto \operatorname{concurrence}\left(rho\left(h, t\right)\right), g\right)) \Rightarrow \forall L:\operatorname{Matrix}\left((\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), (\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), \mathbb{C}\right), (\operatorname{IsSLD}\left(rho\left(g, t\right), \operatorname{derivG}\left(rho, g, t\right), L\right)) \Rightarrow -(\operatorname{deriv}\left(\operatorname{deriv}\left(\operatorname{fun} h:\mathbb{R} \mapsto \operatorname{concurrence}\left(rho\left(h, t\right)\right)\right), g\right)) \le ((rho\left(g, t\right) \cdot L \cdot L).\operatorname{trace}).\operatorname{re}\right)\right)\right))$$

*Formalization.* `D5/S3/Quantum/Information/SaleemNoisyCurvatureRefutation.claim` (`✓ std3`).

*Citation.* Zain H. Saleem; Anil Shaji; Anjala M. Babu; Da-Wei Luo; Quinn Langfitt; Ting Yu; Stephen K. Gray (2025). *Quantum Fisher Information and the Curvature of Entanglement*. DOI: [10.48550/arXiv.2504.13729](https://doi.org/10.48550/arXiv.2504.13729). URL: <https://arxiv.org/abs/2504.13729>.

*Commentary.*

Section IV.B, p. 9: 'For the case with decay also there are more general examples we can consider but in all cases we conjecture that CoE ≤ QFI with equality at specific points.' Encoding: rhoZero is any density matrix, kappa and t are positive real numbers, and rho solves (41) with that initial state. At every g where the concurrence is twice continuously differentiable, the negative second derivative is at most the real part of Tr(rho L²), for every Hermitian SLD L. IsDensity is the reused predicate PosSemidef and trace one. Matrix indices are pairs, with the first coordinate the first qubit. The twice-continuously-differentiable condition restricts the comparison to smooth points.

**Theorem 1.12 (Refutation at positive damping).**

$$\neg (\forall rhoZero:\operatorname{Matrix}\left((\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), (\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), \mathbb{C}\right), \forall kappa:\mathbb{R}, \forall t:\mathbb{R}, \forall rho:\mathbb{R} \to \mathbb{R} \to \operatorname{Matrix}\left((\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), (\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), \mathbb{C}\right), (\operatorname{IsDensity}\left(rhoZero\right)) \Rightarrow \left((0 < kappa) \Rightarrow \left((0 < t) \Rightarrow \left((\operatorname{IsTrajectory}\left(rhoZero, kappa, rho\right)) \Rightarrow \forall g:\mathbb{R}, (\operatorname{ContDiffAt}\left(\mathbb{R}, 2, \operatorname{fun} h:\mathbb{R} \mapsto \operatorname{concurrence}\left(rho\left(h, t\right)\right), g\right)) \Rightarrow \forall L:\operatorname{Matrix}\left((\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), (\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), \mathbb{C}\right), (\operatorname{IsSLD}\left(rho\left(g, t\right), \operatorname{derivG}\left(rho, g, t\right), L\right)) \Rightarrow -(\operatorname{deriv}\left(\operatorname{deriv}\left(\operatorname{fun} h:\mathbb{R} \mapsto \operatorname{concurrence}\left(rho\left(h, t\right)\right)\right), g\right)) \le ((rho\left(g, t\right) \cdot L \cdot L).\operatorname{trace}).\operatorname{re}\right)\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/SaleemNoisyCurvatureRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/saleem-et-al-2025-noisy-curvature-of-entanglement` (refuted) by `D5/S3/Quantum/Information/SaleemNoisyCurvatureRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"saleem-et-al-2025-noisy-curvature-of-entanglement","declaration_gid":"D5/S3/Quantum/Information/SaleemNoisyCurvatureRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Zain H. Saleem; Anil Shaji; Anjala M. Babu; Da-Wei Luo; Quinn Langfitt; Ting Yu; Stephen K. Gray (2025). *Quantum Fisher Information and the Curvature of Entanglement*. DOI: [10.48550/arXiv.2504.13729](https://doi.org/10.48550/arXiv.2504.13729). URL: <https://arxiv.org/abs/2504.13729>.

*Commentary.*

Take rhoZero=diag(1,11,3,1)/16, kappa=log 2 and t=1. At g=pi/4 the evolved state is [[1,0,0,0],[0,15,8i,0],[0,−8i,15,0],[0,0,0,33]]/64. Its spin-flip spectrum is {529,49,33,33}/4096. Near that point its concurrence equals sin(2g)/4−sqrt(33)/32, hence its curvature is 1. The Hermitian matrix L=diag(0,−16/15,16/15,0) satisfies the SLD equation and gives QFI=8/15. The conjectured inequality would require 1≤8/15.

## References

- Truth anchor: `D5/S3/Quantum/Information/SaleemNoisyCurvatureRefutation.IsSLD`
- Truth anchor: `D5/S3/Quantum/Information/SaleemNoisyCurvatureRefutation.IsTrajectory`
- Truth anchor: `D5/S3/Quantum/Information/SaleemNoisyCurvatureRefutation.claim`
- Truth anchor: `D5/S3/Quantum/Information/SaleemNoisyCurvatureRefutation.concurrence`
- Truth anchor: `D5/S3/Quantum/Information/SaleemNoisyCurvatureRefutation.derivG`
- Truth anchor: `D5/S3/Quantum/Information/SaleemNoisyCurvatureRefutation.dissipator`
- Truth anchor: `D5/S3/Quantum/Information/SaleemNoisyCurvatureRefutation.generator`
- Truth anchor: `D5/S3/Quantum/Information/SaleemNoisyCurvatureRefutation.hamiltonian`
- Truth anchor: `D5/S3/Quantum/Information/SaleemNoisyCurvatureRefutation.jump1`
- Truth anchor: `D5/S3/Quantum/Information/SaleemNoisyCurvatureRefutation.jump2`
- Truth anchor: `D5/S3/Quantum/Information/SaleemNoisyCurvatureRefutation.result`
- Truth anchor: `D5/S3/Quantum/Information/SaleemNoisyCurvatureRefutation.sigmaYY`
- Dependency: [D5/S3/Quantum/Dynamics/PronkoFredkinNonCyclicAnnihilation](../Dynamics/PronkoFredkinNonCyclicAnnihilation.md)
- Dependency: [D5/S3/Quantum/Entanglement/StructuredNegativityCoincidenceRefutation](../Entanglement/StructuredNegativityCoincidenceRefutation.md)
