# The mass gap of the four Hofstadter bands

## Abstract

The third and fourth Hofstadter bands have a uniform gap at Fermi energy two for every nonzero mass in the interval from minus two to two.

**Definition 1.1 (The Bloch Hamiltonian).**

$$\forall \left(k_{1}: \mathbb{R}\right), \left(\forall \left(k_{2}: \mathbb{R}\right), \left(\forall \left(m: \mathbb{R}\right), \left(\left(\operatorname{D5.S3.SpectralTopology.HalfFluxHofstadterMassGap.bloch}\left(k_{1}, k_{2}, m\right): \operatorname{Matrix}\left(\operatorname{Fin}\left(4\right), \operatorname{Fin}\left(4\right), \mathbb{C}\right)\right) = -\left(\begin{pmatrix}\operatorname{Complex.ofReal}\left(\left(2: \mathbb{R}\right) + m\right)&\left(1: \mathbb{C}\right) - \operatorname{Complex.I} \cdot \operatorname{Complex.exp}\left(\left(2: \mathbb{C}\right) \cdot \operatorname{Complex.I} \cdot \operatorname{Complex.ofReal}\left(k_{1}\right)\right)&\left(1: \mathbb{C}\right) - \operatorname{Complex.I} \cdot \operatorname{Complex.exp}\left(\left(2: \mathbb{C}\right) \cdot \operatorname{Complex.I} \cdot \operatorname{Complex.ofReal}\left(k_{2}\right)\right)&\left(0: \mathbb{C}\right)\\\left(1: \mathbb{C}\right) + \operatorname{Complex.I} \cdot \operatorname{Complex.exp}\left(-\left(\left(2: \mathbb{C}\right)\right) \cdot \operatorname{Complex.I} \cdot \operatorname{Complex.ofReal}\left(k_{1}\right)\right)&\left(0: \mathbb{C}\right)&\left(0: \mathbb{C}\right)&-\left(\operatorname{Complex.I}\right) + \operatorname{Complex.exp}\left(\left(2: \mathbb{C}\right) \cdot \operatorname{Complex.I} \cdot \operatorname{Complex.ofReal}\left(k_{2}\right)\right)\\\left(1: \mathbb{C}\right) + \operatorname{Complex.I} \cdot \operatorname{Complex.exp}\left(-\left(\left(2: \mathbb{C}\right)\right) \cdot \operatorname{Complex.I} \cdot \operatorname{Complex.ofReal}\left(k_{2}\right)\right)&\left(0: \mathbb{C}\right)&\left(0: \mathbb{C}\right)&\left(1: \mathbb{C}\right) + \operatorname{Complex.I} \cdot \operatorname{Complex.exp}\left(\left(2: \mathbb{C}\right) \cdot \operatorname{Complex.I} \cdot \operatorname{Complex.ofReal}\left(k_{1}\right)\right)\\\left(0: \mathbb{C}\right)&\operatorname{Complex.I} + \operatorname{Complex.exp}\left(-\left(\left(2: \mathbb{C}\right)\right) \cdot \operatorname{Complex.I} \cdot \operatorname{Complex.ofReal}\left(k_{2}\right)\right)&\left(1: \mathbb{C}\right) - \operatorname{Complex.I} \cdot \operatorname{Complex.exp}\left(-\left(\left(2: \mathbb{C}\right)\right) \cdot \operatorname{Complex.I} \cdot \operatorname{Complex.ofReal}\left(k_{1}\right)\right)&-\left(\operatorname{Complex.ofReal}\left(\left(2: \mathbb{R}\right) + m\right)\right)\end{pmatrix}\right)\right)\right)\right)$$

*Formalization.* `D5/S3/SpectralTopology/HalfFluxHofstadterMassGap.bloch` (`✓ std3`).

*Citation.* Simone Fabbri; Giovanna Marcelli; Alessandro Giuliani (2026). *The conductivity matrix at the topological phase transition*. URL: <https://arxiv.org/abs/2609.03832v1>.

*Commentary.*

This is the complex four-by-four Bloch matrix of the pi/2-flux Hofstadter model, with its overall minus sign. The real momenta k₁ and k₂ are unrestricted, and the real mass m enters through d = 2 + m. Each real quantity in a complex entry is included by Complex.ofReal. The matrix is equation Hofst_Hamiltonian in the source, TeX lines 663–671; the mass substitution is at lines 686–687.

**Theorem 1.2 (Hermiticity for all real parameters).**

$$\forall \left(k_{1}: \mathbb{R}\right), \left(\forall \left(k_{2}: \mathbb{R}\right), \left(\forall \left(m: \mathbb{R}\right), \left(\operatorname{Matrix.IsHermitian}\left(\operatorname{D5.S3.SpectralTopology.HalfFluxHofstadterMassGap.bloch}\left(k_{1}, k_{2}, m\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/SpectralTopology/HalfFluxHofstadterMassGap.bloch_isHermitian` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Simone Fabbri; Giovanna Marcelli; Alessandro Giuliani (2026). *The conductivity matrix at the topological phase transition*. URL: <https://arxiv.org/abs/2609.03832v1>.

*Commentary.*

The diagonal entries are real, and opposite off-diagonal entries are complex conjugates. For real k, conjugating exp(2ik) gives exp(−2ik), and conjugating the latter gives exp(2ik). Checking the sixteen entries therefore identifies the conjugate transpose with the original matrix. No restriction on the mass or the momenta is needed.

**Definition 1.3 (The energy bands in increasing order).**

$$\forall \left(k_{1}: \mathbb{R}\right), \left(\forall \left(k_{2}: \mathbb{R}\right), \left(\forall \left(m: \mathbb{R}\right), \left(\forall \left(j: \operatorname{Fin}\left(4\right)\right), \left(\left(\operatorname{D5.S3.SpectralTopology.HalfFluxHofstadterMassGap.band}\left(k_{1}, k_{2}, m, j\right): \mathbb{R}\right) = \left(\operatorname{Matrix.IsHermitian.eigenvalues}_{0}\right)\left(\operatorname{D5.S3.SpectralTopology.HalfFluxHofstadterMassGap.bloch_{isHermitian}}\left(k_{1}, k_{2}, m\right), \operatorname{Fin.rev}\left(j\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/SpectralTopology/HalfFluxHofstadterMassGap.band` (`✓ std3`).

*Citation.* Simone Fabbri; Giovanna Marcelli; Alessandro Giuliani (2026). *The conductivity matrix at the topological phase transition*. URL: <https://arxiv.org/abs/2609.03832v1>.

*Commentary.*

The index j belongs to Fin 4, so j = 0, 1, 2, 3 names the source's first, second, third and fourth bands. Matrix.IsHermitian.eigenvalues₀ lists the real eigenvalues in decreasing order; Fin.rev reverses the index to obtain increasing order, retaining multiplicity. This expresses the convention for energy bands at TeX line 354.

**Definition 1.4 (The Fermi energy).**

$$\left(\operatorname{D5.S3.SpectralTopology.HalfFluxHofstadterMassGap.fermiEnergy}: \mathbb{R}\right) = \operatorname{D5.S3.SpectralTopology.HalfFluxHofstadterMassGap.band}\left(\frac{\operatorname{Real.pi}}{\left(4: \mathbb{R}\right)}, \frac{\operatorname{Real.pi}}{\left(4: \mathbb{R}\right)}, \left(0: \mathbb{R}\right), \left(2: \operatorname{Fin}\left(4\right)\right)\right)$$

*Formalization.* `D5/S3/SpectralTopology/HalfFluxHofstadterMassGap.fermiEnergy` (`✓ std3`).

*Citation.* Simone Fabbri; Giovanna Marcelli; Alessandro Giuliani (2026). *The conductivity matrix at the topological phase transition*. URL: <https://arxiv.org/abs/2609.03832v1>.

*Commentary.*

The Fermi energy is the third band at zero mass and at the Fermi point (π/4, π/4). The point is specified at TeX line 674, and the energy is defined at lines 686–687. Its equality with the fourth band at that point is a separate part of the gap assertion.

**Definition 1.5 (A uniform gap at every nonzero allowed mass).**

$$\left(\operatorname{D5.S3.SpectralTopology.HalfFluxHofstadterMassGap.claim}\right) \Leftrightarrow \left(\left(\operatorname{D5.S3.SpectralTopology.HalfFluxHofstadterMassGap.band}\left(\frac{\operatorname{Real.pi}}{\left(4: \mathbb{R}\right)}, \frac{\operatorname{Real.pi}}{\left(4: \mathbb{R}\right)}, \left(0: \mathbb{R}\right), \left(3: \operatorname{Fin}\left(4\right)\right)\right) = \operatorname{D5.S3.SpectralTopology.HalfFluxHofstadterMassGap.fermiEnergy}\right) \land \left(\forall \left(m: \mathbb{R}\right), \left(\left(-\left(\left(2: \mathbb{R}\right)\right) \le m\right) \to \left(\left(m \le \left(2: \mathbb{R}\right)\right) \to \left(\left(m \ne \left(0: \mathbb{R}\right)\right) \to \left(\exists \left(\delta: \mathbb{R}\right), \left(\left(\left(0: \mathbb{R}\right) < \delta\right) \land \left(\forall \left(k_{1}: \mathbb{R}\right), \left(\forall \left(k_{2}: \mathbb{R}\right), \left(\left(\operatorname{D5.S3.SpectralTopology.HalfFluxHofstadterMassGap.fermiEnergy} + \delta \le \operatorname{D5.S3.SpectralTopology.HalfFluxHofstadterMassGap.band}\left(k_{1}, k_{2}, m, \left(3: \operatorname{Fin}\left(4\right)\right)\right)\right) \land \left(\operatorname{D5.S3.SpectralTopology.HalfFluxHofstadterMassGap.band}\left(k_{1}, k_{2}, m, \left(2: \operatorname{Fin}\left(4\right)\right)\right) \le \operatorname{D5.S3.SpectralTopology.HalfFluxHofstadterMassGap.fermiEnergy} - \delta\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/SpectralTopology/HalfFluxHofstadterMassGap.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Simone Fabbri; Giovanna Marcelli; Alessandro Giuliani (2026). *The conductivity matrix at the topological phase transition*. URL: <https://arxiv.org/abs/2609.03832v1>.

*Commentary.*

At zero mass the fourth band at the Fermi point equals the Fermi energy. For each m with −2 ≤ m ≤ 2 and m ≠ 0, one positive real δ separates the fourth band above that energy and the third band below it, simultaneously for every pair of real momenta. The bound may depend on m but not on the momenta. This is the uniform inequality form of the question at TeX lines 689–690. It quantifies over all real momenta, without taking extrema or requiring a choice of fundamental domain.

**Theorem 1.6 (A positive gap of at least m squared over five hundred).**

$$\left(\operatorname{D5.S3.SpectralTopology.HalfFluxHofstadterMassGap.band}\left(\frac{\operatorname{Real.pi}}{\left(4: \mathbb{R}\right)}, \frac{\operatorname{Real.pi}}{\left(4: \mathbb{R}\right)}, \left(0: \mathbb{R}\right), \left(3: \operatorname{Fin}\left(4\right)\right)\right) = \operatorname{D5.S3.SpectralTopology.HalfFluxHofstadterMassGap.fermiEnergy}\right) \land \left(\forall \left(m: \mathbb{R}\right), \left(\left(-\left(\left(2: \mathbb{R}\right)\right) \le m\right) \to \left(\left(m \le \left(2: \mathbb{R}\right)\right) \to \left(\left(m \ne \left(0: \mathbb{R}\right)\right) \to \left(\exists \left(\delta: \mathbb{R}\right), \left(\left(\left(0: \mathbb{R}\right) < \delta\right) \land \left(\forall \left(k_{1}: \mathbb{R}\right), \left(\forall \left(k_{2}: \mathbb{R}\right), \left(\left(\operatorname{D5.S3.SpectralTopology.HalfFluxHofstadterMassGap.fermiEnergy} + \delta \le \operatorname{D5.S3.SpectralTopology.HalfFluxHofstadterMassGap.band}\left(k_{1}, k_{2}, m, \left(3: \operatorname{Fin}\left(4\right)\right)\right)\right) \land \left(\operatorname{D5.S3.SpectralTopology.HalfFluxHofstadterMassGap.band}\left(k_{1}, k_{2}, m, \left(2: \operatorname{Fin}\left(4\right)\right)\right) \le \operatorname{D5.S3.SpectralTopology.HalfFluxHofstadterMassGap.fermiEnergy} - \delta\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/SpectralTopology/HalfFluxHofstadterMassGap.result` (`✓ std3`). ∎

*Resolves.* `Problems/fabbri-marcelli-giuliani-2026-half-flux-hofstadter-mass-gap` (proved) by `D5/S3/SpectralTopology/HalfFluxHofstadterMassGap.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"fabbri-marcelli-giuliani-2026-half-flux-hofstadter-mass-gap","declaration_gid":"D5/S3/SpectralTopology/HalfFluxHofstadterMassGap.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Simone Fabbri; Giovanna Marcelli; Alessandro Giuliani (2026). *The conductivity matrix at the topological phase transition*. URL: <https://arxiv.org/abs/2609.03832v1>.

*Commentary.*

First put d = 2 + m and consider the real expression q = (y₁ − d)² + (y₂ − d)² + 2 − d², where y₁ ≤ 1 and y₂ ≤ 1. If m ≥ −2, then d ≥ 0. For d ≤ 1, the two squares give q ≥ 2 − d² ≥ (d − 2)²/2. For d > 1, each square is at least (d − 1)², so q ≥ 2(d − 1)² + 2 − d² = (d − 2)². Thus q ≥ m²/2 in both cases.

Set z₁ = exp(2ik₁), z₂ = exp(2ik₂), y₁ = Im z₁ and y₂ = Im z₂. The phases have norm one, hence y₁ ≤ 1 and y₂ ≤ 1. Write H for the Bloch matrix and K = H − 2I. Permuting coordinates into the order (1,4,2,3) gives a block matrix with upper-left block A = diag(−d − 2, d − 2), lower-right block −2I₂, and upper-right block B whose rows are (−1 + iz₁, −1 + iz₂) and (−i − conjugate(z₂), −1 + i conjugate(z₁)).

The Schur matrix S = A + BBᴴ/2 has diagonal entries s − d and d − s, where s = y₁ + y₂, and upper-right entry t = (1 − i)(1 − z₁ + z₂ + z₁z₂)/2; its lower-left entry is the conjugate of t. The unit-circle equations for z₁ and z₂ give |t|² = 2(1 − y₁y₂), so det S = −q. The lower triangular block matrix P with diagonal blocks I₂ and lower-left block Bᴴ/2 has determinant one, and PᴴKP = diag(S, −2I₂) in the permuted coordinates. Taking determinants gives det K = −4q. Consequently q > 0 whenever m ≥ −2 and m ≠ 0. Adding the scalar matrix −2I subtracts two from each ordered eigenvalue without changing its position.

The Hermitian two-by-two matrix S has negative determinant, so the product of its two real eigenvalues is negative. Exactly one of them is positive. Factoring the characteristic polynomial of diag(S, −2I₂) shows that this block matrix also has exactly one positive eigenvalue. Inertia is preserved by the invertible congruence P and by the coordinate permutation, so K has positive index one. Its nonzero determinant gives rank four, and the sum of the positive and negative indices equals the rank. The negative index is therefore three.

For −2 ≤ m ≤ 2, one has |d| ≤ 4. Every off-diagonal entry of K has norm at most two, and the diagonal estimates give a row sum of norms at most ten. Gershgorin's theorem places every eigenvalue in a disk centered at a diagonal entry with radius the sum of the other entry norms in that row. The triangle inequality therefore bounds the absolute value of every eigenvalue of K by ten.

At k₁ = k₂ = π/4 and m = 0 the positive phases equal i and the negative phases equal −i. Substitution gives the characteristic polynomial X(X + 4)(X − 2)². Its complex roots, with multiplicity, are 2, 2, 0 and −4. Sorting their real parts identifies both the third and fourth bands with two; in particular the Fermi energy is two.

Now take m ≥ −2 with m ≠ 0. In decreasing order, the top eigenvalue of K is positive: otherwise all four would be nonpositive, contradicting positive index one. Its second eigenvalue is negative: otherwise only the last two could be negative, contradicting negative index three. Reversing the indices and adding two gives band k₁ k₂ m 2 < 2 and 2 < band k₁ k₂ m 3.

Finally, det K = −4q and q ≥ m²/2 imply |det K| ≥ 2m². The absolute determinant is the product of the four absolute eigenvalues. After singling out any one eigenvalue, the other three factors have product at most 10³ = 1000. Hence every band satisfies |band k₁ k₂ m j − 2| ≥ m²/500. Choose δ = m²/500, which is positive for nonzero m. The strict signs of the third and fourth bands remove the absolute values in the two required directions. Replacing two by the Fermi energy proves both uniform inequalities, together with the equality at zero mass.

## References

- Truth anchor: `D5/S3/SpectralTopology/HalfFluxHofstadterMassGap.band`
- Truth anchor: `D5/S3/SpectralTopology/HalfFluxHofstadterMassGap.bloch`
- Truth anchor: `D5/S3/SpectralTopology/HalfFluxHofstadterMassGap.bloch_isHermitian`
- Truth anchor: `D5/S3/SpectralTopology/HalfFluxHofstadterMassGap.claim`
- Truth anchor: `D5/S3/SpectralTopology/HalfFluxHofstadterMassGap.fermiEnergy`
- Truth anchor: `D5/S3/SpectralTopology/HalfFluxHofstadterMassGap.result`
- Dependency: [D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIISLnUnipotentCommutators](../FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIISLnUnipotentCommutators.md)
- Dependency: [D5/S3/Quantum/Matrix/LinGProperty/ScalarPerturbation](../Quantum/Matrix/LinGProperty/ScalarPerturbation.md)
- Dependency: [D5/S3/SpectralTopology/PointGapExactInertia](PointGapExactInertia.md)
- Dependency: [D5/S3/Weil/Pick/InvertibleHermitianInertiaPullback](../Weil/Pick/InvertibleHermitianInertiaPullback.md)
