# Zernike operators and normal ordering

## Abstract

Polynomial differential operators and the normal-order filtration for Zernike Hamiltonians.

Operators are complex linear endomorphisms of MvPolynomial (Fin 2) Complex. Multiplication is composition, 1 is the identity, and a centered dot denotes scalar multiplication. Polynomial coordinates 0 and 1 represent the source coordinates 1 and 2. All exponents and all subtractions between exponents are natural-number operations.

**Definition 1.1 (q).**

$$\forall (i: \operatorname{Fin}\left(2\right)), \operatorname{q}\left(i\right) = \operatorname{LinearMap}.\operatorname{mulLeft}(\mathbb{C}, \operatorname{X}\left(i\right))$$

*Formalization.* `D5/S3/Quantum/CampoamorStursbergZernikeLadderCore.q` (`✓ std3`).

*Citation.* R. Campoamor-Stursberg, F. J. Herranz, D. Latini, I. Marquette, A. Blasco (2026). *Generalized quantum Zernike Hamiltonians: Polynomial Higgs-type algebras and algebraic derivation of the spectrum*. DOI: [10.1088/1361-6544/ae64a2](https://doi.org/10.1088/1361-6544/ae64a2). URL: <https://arxiv.org/abs/2502.02491v2>.

*Commentary.*

Equation (2.1): multiplication by the coordinate polynomial.

**Definition 1.2 (p).**

$$\forall (i: \operatorname{Fin}\left(2\right)), \operatorname{p}\left(i\right) = (-(\operatorname{Complex}.\operatorname{I})) \cdot (\operatorname{pderiv}\left(i\right).toLinearMap)$$

*Formalization.* `D5/S3/Quantum/CampoamorStursbergZernikeLadderCore.p` (`✓ std3`).

*Citation.* R. Campoamor-Stursberg, F. J. Herranz, D. Latini, I. Marquette, A. Blasco (2026). *Generalized quantum Zernike Hamiltonians: Polynomial Higgs-type algebras and algebraic derivation of the spectrum*. DOI: [10.1088/1361-6544/ae64a2](https://doi.org/10.1088/1361-6544/ae64a2). URL: <https://arxiv.org/abs/2502.02491v2>.

*Commentary.*

Equation (2.1): minus the imaginary unit times the partial derivative.

**Definition 1.3 (dot).**

$$dot = (\operatorname{q}\left(0\right)) * (\operatorname{p}\left(0\right)) + (\operatorname{q}\left(1\right)) * (\operatorname{p}\left(1\right))$$

*Formalization.* `D5/S3/Quantum/CampoamorStursbergZernikeLadderCore.dot` (`✓ std3`).

*Citation.* R. Campoamor-Stursberg, F. J. Herranz, D. Latini, I. Marquette, A. Blasco (2026). *Generalized quantum Zernike Hamiltonians: Polynomial Higgs-type algebras and algebraic derivation of the spectrum*. DOI: [10.1088/1361-6544/ae64a2](https://doi.org/10.1088/1361-6544/ae64a2). URL: <https://arxiv.org/abs/2502.02491v2>.

*Commentary.*

The ordered contraction of coordinates and momenta.

**Definition 1.4 (angularMomentum).**

$$angularMomentum = (\operatorname{q}\left(0\right)) * (\operatorname{p}\left(1\right)) - (\operatorname{q}\left(1\right)) * (\operatorname{p}\left(0\right))$$

*Formalization.* `D5/S3/Quantum/CampoamorStursbergZernikeLadderCore.angularMomentum` (`✓ std3`).

*Citation.* R. Campoamor-Stursberg, F. J. Herranz, D. Latini, I. Marquette, A. Blasco (2026). *Generalized quantum Zernike Hamiltonians: Polynomial Higgs-type algebras and algebraic derivation of the spectrum*. DOI: [10.1088/1361-6544/ae64a2](https://doi.org/10.1088/1361-6544/ae64a2). URL: <https://arxiv.org/abs/2502.02491v2>.

*Commentary.*

Equation (2.5): angular momentum.

**Definition 1.5 (hamiltonian).**

$$\forall (N: \mathbb{N}), \forall (gamma: \mathbb{N} \to \mathbb{C}), \operatorname{hamiltonian}\left(N, gamma\right) = (\operatorname{p}\left(0\right))^{2} + (\operatorname{p}\left(1\right))^{2} + \sum_{k \in \operatorname{Finset}.\operatorname{Icc}(1, N)} ((\operatorname{gamma}\left(k\right)) \cdot ((dot)^{k}))$$

*Formalization.* `D5/S3/Quantum/CampoamorStursbergZernikeLadderCore.hamiltonian` (`✓ std3`).

*Citation.* R. Campoamor-Stursberg, F. J. Herranz, D. Latini, I. Marquette, A. Blasco (2026). *Generalized quantum Zernike Hamiltonians: Polynomial Higgs-type algebras and algebraic derivation of the spectrum*. DOI: [10.1088/1361-6544/ae64a2](https://doi.org/10.1088/1361-6544/ae64a2). URL: <https://arxiv.org/abs/2502.02491v2>.

*Commentary.*

Equation (2.3), for every natural N and every complex coefficient sequence.

**Definition 1.6 (monomial).**

$$\forall (a: \mathbb{N}), \forall (b: \mathbb{N}), \forall (c: \mathbb{N}), \forall (d: \mathbb{N}), \operatorname{monomial}\left(a, b, c, d\right) = ((((\operatorname{q}\left(0\right))^{a}) * ((\operatorname{q}\left(1\right))^{b})) * ((\operatorname{p}\left(0\right))^{c})) * ((\operatorname{p}\left(1\right))^{d})$$

*Formalization.* `D5/S3/Quantum/CampoamorStursbergZernikeLadderCore.monomial` (`✓ std3`).

*Citation.* R. Campoamor-Stursberg, F. J. Herranz, D. Latini, I. Marquette, A. Blasco (2026). *Generalized quantum Zernike Hamiltonians: Polynomial Higgs-type algebras and algebraic derivation of the spectrum*. DOI: [10.1088/1361-6544/ae64a2](https://doi.org/10.1088/1361-6544/ae64a2). URL: <https://arxiv.org/abs/2502.02491v2>.

*Commentary.*

The normal-ordered monomial has total degree a+b+c+d and grading a+b-c-d.

**Definition 1.7 (corrections).**

$$\forall (N: \mathbb{N}), \operatorname{corrections}\left(N\right) = \operatorname{Submodule}.\operatorname{span}(\mathbb{C}, \{A: \operatorname{Module}.\operatorname{End}(\mathbb{C}, \operatorname{MvPolynomial}\left(\operatorname{Fin}\left(2\right), \mathbb{C}\right)) | \exists a: \mathbb{N}, \exists b: \mathbb{N}, \exists c: \mathbb{N}, \exists d: \mathbb{N}, (a + b = c + d) \land (1 \leq a + b + c + d) \land (a + b + c + d \leq (2) * (N)) \land (A = \operatorname{monomial}\left(a, b, c, d\right))\})$$

*Formalization.* `D5/S3/Quantum/CampoamorStursbergZernikeLadderCore.corrections` (`✓ std3`).

*Citation.* R. Campoamor-Stursberg, F. J. Herranz, D. Latini, I. Marquette, A. Blasco (2026). *Generalized quantum Zernike Hamiltonians: Polynomial Higgs-type algebras and algebraic derivation of the spectrum*. DOI: [10.1088/1361-6544/ae64a2](https://doi.org/10.1088/1361-6544/ae64a2). URL: <https://arxiv.org/abs/2502.02491v2>.

*Commentary.*

Equation (2.6): the complex span of normal-ordered monomials of positive degree at most 2N and grading zero.

**Definition 1.8 (IsSymmetry).**

$$\forall (N: \mathbb{N}), \forall (gamma: \mathbb{N} \to \mathbb{C}), \forall (T: \operatorname{Module}.\operatorname{End}(\mathbb{C}, \operatorname{MvPolynomial}\left(\operatorname{Fin}\left(2\right), \mathbb{C}\right))), \forall (I: \operatorname{Module}.\operatorname{End}(\mathbb{C}, \operatorname{MvPolynomial}\left(\operatorname{Fin}\left(2\right), \mathbb{C}\right))), \operatorname{IsSymmetry}\left(N, gamma, T, I\right) = ((I - T \in \operatorname{corrections}\left(N\right)) \land ((I) * (\operatorname{hamiltonian}\left(N, gamma\right)) - (\operatorname{hamiltonian}\left(N, gamma\right)) * (I) = 0))$$

*Formalization.* `D5/S3/Quantum/CampoamorStursbergZernikeLadderCore.IsSymmetry` (`✓ std3`).

*Citation.* R. Campoamor-Stursberg, F. J. Herranz, D. Latini, I. Marquette, A. Blasco (2026). *Generalized quantum Zernike Hamiltonians: Polynomial Higgs-type algebras and algebraic derivation of the spectrum*. DOI: [10.1088/1361-6544/ae64a2](https://doi.org/10.1088/1361-6544/ae64a2). URL: <https://arxiv.org/abs/2502.02491v2>.

*Commentary.*

Equations (2.6) and (2.7): the difference from the kinetic term lies in the correction span, and the operator commutes with the Hamiltonian.

**Definition 1.9 (k1).**

$$k1 = angularMomentum$$

*Formalization.* `D5/S3/Quantum/CampoamorStursbergZernikeLadderCore.k1` (`✓ std3`).

*Citation.* R. Campoamor-Stursberg, F. J. Herranz, D. Latini, I. Marquette, A. Blasco (2026). *Generalized quantum Zernike Hamiltonians: Polynomial Higgs-type algebras and algebraic derivation of the spectrum*. DOI: [10.1088/1361-6544/ae64a2](https://doi.org/10.1088/1361-6544/ae64a2). URL: <https://arxiv.org/abs/2502.02491v2>.

*Commentary.*

Equation (2.8): K1 is angular momentum.

**Definition 1.10 (k2).**

$$\forall (I: \operatorname{Module}.\operatorname{End}(\mathbb{C}, \operatorname{MvPolynomial}\left(\operatorname{Fin}\left(2\right), \mathbb{C}\right))), \forall (J: \operatorname{Module}.\operatorname{End}(\mathbb{C}, \operatorname{MvPolynomial}\left(\operatorname{Fin}\left(2\right), \mathbb{C}\right))), \operatorname{k2}\left(I, J\right) = (\frac{1}{2}) \cdot (J - I)$$

*Formalization.* `D5/S3/Quantum/CampoamorStursbergZernikeLadderCore.k2` (`✓ std3`).

*Citation.* R. Campoamor-Stursberg, F. J. Herranz, D. Latini, I. Marquette, A. Blasco (2026). *Generalized quantum Zernike Hamiltonians: Polynomial Higgs-type algebras and algebraic derivation of the spectrum*. DOI: [10.1088/1361-6544/ae64a2](https://doi.org/10.1088/1361-6544/ae64a2). URL: <https://arxiv.org/abs/2502.02491v2>.

*Commentary.*

Equation (2.8): half the difference of the two symmetries.

**Definition 1.11 (k3).**

$$\forall (I: \operatorname{Module}.\operatorname{End}(\mathbb{C}, \operatorname{MvPolynomial}\left(\operatorname{Fin}\left(2\right), \mathbb{C}\right))), \forall (J: \operatorname{Module}.\operatorname{End}(\mathbb{C}, \operatorname{MvPolynomial}\left(\operatorname{Fin}\left(2\right), \mathbb{C}\right))), \operatorname{k3}\left(I, J\right) = (k1) * (\operatorname{k2}\left(I, J\right)) - (\operatorname{k2}\left(I, J\right)) * (k1)$$

*Formalization.* `D5/S3/Quantum/CampoamorStursbergZernikeLadderCore.k3` (`✓ std3`).

*Citation.* R. Campoamor-Stursberg, F. J. Herranz, D. Latini, I. Marquette, A. Blasco (2026). *Generalized quantum Zernike Hamiltonians: Polynomial Higgs-type algebras and algebraic derivation of the spectrum*. DOI: [10.1088/1361-6544/ae64a2](https://doi.org/10.1088/1361-6544/ae64a2). URL: <https://arxiv.org/abs/2502.02491v2>.

*Commentary.*

Equation (2.8): the commutator of angular momentum with k2.

**Definition 1.12 (phi1).**

$$\forall (N: \mathbb{N}), \forall (gamma: \mathbb{N} \to \mathbb{C}), \forall (H: \operatorname{Module}.\operatorname{End}(\mathbb{C}, \operatorname{MvPolynomial}\left(\operatorname{Fin}\left(2\right), \mathbb{C}\right))), \forall (K: \operatorname{Module}.\operatorname{End}(\mathbb{C}, \operatorname{MvPolynomial}\left(\operatorname{Fin}\left(2\right), \mathbb{C}\right))), \operatorname{phi1}\left(N, gamma, H, K\right) = (\frac{1}{4}) \cdot (H - \sum_{k \in \operatorname{Finset}.\operatorname{Icc}(1, N)} (((((2) * (\operatorname{Complex}.\operatorname{I}))^{k}) * (\operatorname{gamma}\left(k\right))) \cdot ((K)^{k})))$$

*Formalization.* `D5/S3/Quantum/CampoamorStursbergZernikeLadderCore.phi1` (`✓ std3`).

*Citation.* R. Campoamor-Stursberg, F. J. Herranz, D. Latini, I. Marquette, A. Blasco (2026). *Generalized quantum Zernike Hamiltonians: Polynomial Higgs-type algebras and algebraic derivation of the spectrum*. DOI: [10.1088/1361-6544/ae64a2](https://doi.org/10.1088/1361-6544/ae64a2). URL: <https://arxiv.org/abs/2502.02491v2>.

*Commentary.*

Equation (5.1): the first factor of the structure function.

**Definition 1.13 (phi2).**

$$\forall (N: \mathbb{N}), \forall (gamma: \mathbb{N} \to \mathbb{C}), \forall (H: \operatorname{Module}.\operatorname{End}(\mathbb{C}, \operatorname{MvPolynomial}\left(\operatorname{Fin}\left(2\right), \mathbb{C}\right))), \forall (K: \operatorname{Module}.\operatorname{End}(\mathbb{C}, \operatorname{MvPolynomial}\left(\operatorname{Fin}\left(2\right), \mathbb{C}\right))), \operatorname{phi2}\left(N, gamma, H, K\right) = H - \sum_{k \in \operatorname{Finset}.\operatorname{Icc}(1, N)} (((((-(2)) * (\operatorname{Complex}.\operatorname{I}))^{k}) * (\operatorname{gamma}\left(k\right))) \cdot ((K - 1)^{k}))$$

*Formalization.* `D5/S3/Quantum/CampoamorStursbergZernikeLadderCore.phi2` (`✓ std3`).

*Citation.* R. Campoamor-Stursberg, F. J. Herranz, D. Latini, I. Marquette, A. Blasco (2026). *Generalized quantum Zernike Hamiltonians: Polynomial Higgs-type algebras and algebraic derivation of the spectrum*. DOI: [10.1088/1361-6544/ae64a2](https://doi.org/10.1088/1361-6544/ae64a2). URL: <https://arxiv.org/abs/2502.02491v2>.

*Commentary.*

Equation (5.1): the second factor of the structure function.

**Definition 1.14 (phi).**

$$\forall (N: \mathbb{N}), \forall (gamma: \mathbb{N} \to \mathbb{C}), \forall (H: \operatorname{Module}.\operatorname{End}(\mathbb{C}, \operatorname{MvPolynomial}\left(\operatorname{Fin}\left(2\right), \mathbb{C}\right))), \forall (K: \operatorname{Module}.\operatorname{End}(\mathbb{C}, \operatorname{MvPolynomial}\left(\operatorname{Fin}\left(2\right), \mathbb{C}\right))), \operatorname{phi}\left(N, gamma, H, K\right) = (\operatorname{phi1}\left(N, gamma, H, K\right)) * (\operatorname{phi2}\left(N, gamma, H, K\right))$$

*Formalization.* `D5/S3/Quantum/CampoamorStursbergZernikeLadderCore.phi` (`✓ std3`).

*Citation.* R. Campoamor-Stursberg, F. J. Herranz, D. Latini, I. Marquette, A. Blasco (2026). *Generalized quantum Zernike Hamiltonians: Polynomial Higgs-type algebras and algebraic derivation of the spectrum*. DOI: [10.1088/1361-6544/ae64a2](https://doi.org/10.1088/1361-6544/ae64a2). URL: <https://arxiv.org/abs/2502.02491v2>.

*Commentary.*

Equation (2.10): the ordered product of phi1 and phi2.

**Definition 1.15 (DivDiff.peval).**

$$\forall (B: Type), [\operatorname{Ring}\left(B\right)] [\operatorname{Algebra}\left(\mathbb{C}, B\right)], \forall (N: \mathbb{N}), \forall (gamma: \mathbb{N} \to \mathbb{C}), \forall (s: B), \operatorname{peval}\left(N, gamma, s\right) = \sum_{k \in \operatorname{Finset}.\operatorname{Icc}(1, N)} ((\operatorname{gamma}\left(k\right)) \cdot ((s)^{k}))$$

*Formalization.* `D5/S3/Quantum/CampoamorStursbergZernikeLadderCore.peval` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Evaluation of the finite polynomial with coefficients gamma and exponents 1 through N.

**Definition 1.16 (DivDiff.divided).**

$$\forall (B: Type), [\operatorname{Ring}\left(B\right)] [\operatorname{Algebra}\left(\mathbb{C}, B\right)], \forall (N: \mathbb{N}), \forall (gamma: \mathbb{N} \to \mathbb{C}), \forall (s: B), \forall (t: B), \operatorname{divided}\left(N, gamma, s, t\right) = \sum_{k \in \operatorname{Finset}.\operatorname{Icc}(1, N)} ((\operatorname{gamma}\left(k\right)) \cdot (\sum_{j \in \operatorname{Finset}.\operatorname{range}(k)} (((s)^{k - 1 - j}) * ((t)^{j}))))$$

*Formalization.* `D5/S3/Quantum/CampoamorStursbergZernikeLadderCore.divided` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The polynomial divided difference, expressed as a finite geometric sum; no inverse or distinctness assumption is needed.

**Theorem 1.17 (Weyl.pp).**

$$\forall (i: \operatorname{Fin}\left(2\right)), \forall (j: \operatorname{Fin}\left(2\right)), (\operatorname{p}\left(i\right)) * (\operatorname{p}\left(j\right)) = (\operatorname{p}\left(j\right)) * (\operatorname{p}\left(i\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/CampoamorStursbergZernikeLadderCore.pp` (`✓ std3`). ∎

*Citation.* R. Campoamor-Stursberg, F. J. Herranz, D. Latini, I. Marquette, A. Blasco (2026). *Generalized quantum Zernike Hamiltonians: Polynomial Higgs-type algebras and algebraic derivation of the spectrum*. DOI: [10.1088/1361-6544/ae64a2](https://doi.org/10.1088/1361-6544/ae64a2). URL: <https://arxiv.org/abs/2502.02491v2>.

*Commentary.*

The momenta commute.

**Theorem 1.18 (Weyl.qq).**

$$\forall (i: \operatorname{Fin}\left(2\right)), \forall (j: \operatorname{Fin}\left(2\right)), (\operatorname{q}\left(i\right)) * (\operatorname{q}\left(j\right)) = (\operatorname{q}\left(j\right)) * (\operatorname{q}\left(i\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/CampoamorStursbergZernikeLadderCore.qq` (`✓ std3`). ∎

*Citation.* R. Campoamor-Stursberg, F. J. Herranz, D. Latini, I. Marquette, A. Blasco (2026). *Generalized quantum Zernike Hamiltonians: Polynomial Higgs-type algebras and algebraic derivation of the spectrum*. DOI: [10.1088/1361-6544/ae64a2](https://doi.org/10.1088/1361-6544/ae64a2). URL: <https://arxiv.org/abs/2502.02491v2>.

*Commentary.*

The coordinates commute.

**Theorem 1.19 (Weyl.pq).**

$$\forall (i: \operatorname{Fin}\left(2\right)), \forall (j: \operatorname{Fin}\left(2\right)), (\operatorname{p}\left(i\right)) * (\operatorname{q}\left(j\right)) = (\operatorname{q}\left(j\right)) * (\operatorname{p}\left(i\right)) - (if i = j then \operatorname{Complex}.\operatorname{I} else 0) \cdot (1: \operatorname{Module}.\operatorname{End}(\mathbb{C}, \operatorname{MvPolynomial}\left(\operatorname{Fin}\left(2\right), \mathbb{C}\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/CampoamorStursbergZernikeLadderCore.pq` (`✓ std3`). ∎

*Citation.* R. Campoamor-Stursberg, F. J. Herranz, D. Latini, I. Marquette, A. Blasco (2026). *Generalized quantum Zernike Hamiltonians: Polynomial Higgs-type algebras and algebraic derivation of the spectrum*. DOI: [10.1088/1361-6544/ae64a2](https://doi.org/10.1088/1361-6544/ae64a2). URL: <https://arxiv.org/abs/2502.02491v2>.

*Commentary.*

The coordinate and momentum commutator is the Heisenberg relation.

**Theorem 1.20 (DivDiff.peval_commute_left).**

$$\forall (B: Type), [\operatorname{Ring}\left(B\right)] [\operatorname{Algebra}\left(\mathbb{C}, B\right)], \forall (N: \mathbb{N}), \forall (gamma: \mathbb{N} \to \mathbb{C}), \forall (r: B), \forall (s: B), (\operatorname{Commute}\left(r, s\right)) \implies (\operatorname{Commute}\left(r, \operatorname{peval}\left(N, gamma, s\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/CampoamorStursbergZernikeLadderCore.peval_commute_left` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. Campoamor-Stursberg, F. J. Herranz, D. Latini, I. Marquette, A. Blasco (2026). *Generalized quantum Zernike Hamiltonians: Polynomial Higgs-type algebras and algebraic derivation of the spectrum*. DOI: [10.1088/1361-6544/ae64a2](https://doi.org/10.1088/1361-6544/ae64a2). URL: <https://arxiv.org/abs/2502.02491v2>.

*Commentary.*

An operator commuting with an argument commutes with its polynomial evaluation.

**Theorem 1.21 (DivDiff.divided_commute_left).**

$$\forall (B: Type), [\operatorname{Ring}\left(B\right)] [\operatorname{Algebra}\left(\mathbb{C}, B\right)], \forall (N: \mathbb{N}), \forall (gamma: \mathbb{N} \to \mathbb{C}), \forall (r: B), \forall (s: B), \forall (t: B), ((\operatorname{Commute}\left(r, s\right)) \land (\operatorname{Commute}\left(r, t\right))) \implies (\operatorname{Commute}\left(r, \operatorname{divided}\left(N, gamma, s, t\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/CampoamorStursbergZernikeLadderCore.divided_commute_left` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. Campoamor-Stursberg, F. J. Herranz, D. Latini, I. Marquette, A. Blasco (2026). *Generalized quantum Zernike Hamiltonians: Polynomial Higgs-type algebras and algebraic derivation of the spectrum*. DOI: [10.1088/1361-6544/ae64a2](https://doi.org/10.1088/1361-6544/ae64a2). URL: <https://arxiv.org/abs/2502.02491v2>.

*Commentary.*

Commutation with both arguments implies commutation with the divided difference.

**Theorem 1.22 (DivDiff.intertwine_divided).**

$$\forall (B: Type), [\operatorname{Ring}\left(B\right)] [\operatorname{Algebra}\left(\mathbb{C}, B\right)], \forall (N: \mathbb{N}), \forall (gamma: \mathbb{N} \to \mathbb{C}), \forall (r: B), \forall (s: B), \forall (t: B), \forall (u: B), \forall (v: B), (((s) * (r) = (r) * (u)) \land ((t) * (r) = (r) * (v))) \implies ((\operatorname{divided}\left(N, gamma, s, t\right)) * (r) = (r) * (\operatorname{divided}\left(N, gamma, u, v\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/CampoamorStursbergZernikeLadderCore.intertwine_divided` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. Campoamor-Stursberg, F. J. Herranz, D. Latini, I. Marquette, A. Blasco (2026). *Generalized quantum Zernike Hamiltonians: Polynomial Higgs-type algebras and algebraic derivation of the spectrum*. DOI: [10.1088/1361-6544/ae64a2](https://doi.org/10.1088/1361-6544/ae64a2). URL: <https://arxiv.org/abs/2502.02491v2>.

*Commentary.*

Simultaneous intertwining of two arguments intertwines their divided difference.

**Theorem 1.23 (HamiltonianIdentity.symmetry).**

$$\forall (B: Type), [\operatorname{Ring}\left(B\right)] [\operatorname{Algebra}\left(\mathbb{C}, B\right)], \forall (N: \mathbb{N}), \forall (gamma: \mathbb{N} \to \mathbb{C}), \forall (alpha: \mathbb{C}), \forall (D: B), \forall (A: B), \forall (T: B), \forall (R: B), \forall (U: B), ((\operatorname{Commute}\left(D, A\right)) \land (\operatorname{Commute}\left(D, U\right)) \land ((D) * (T) = (T) * (D + (alpha) \cdot (1))) \land ((A) * (T) = (T) * (A)) \land ((D) * (R) = (R) * (D + (alpha) \cdot (1))) \land ((T) * (R) = (R) * (T)) \land ((T) * (U) = (U) * (T) - (alpha) \cdot (R)) \land ((U) * (T) = (R) * (D - A))) \implies ((T + \operatorname{peval}\left(N, gamma, D\right)) * (R + (U) * (\operatorname{divided}\left(N, gamma, D, A + (alpha) \cdot (1)\right))) = (R + (U) * (\operatorname{divided}\left(N, gamma, D, A + (alpha) \cdot (1)\right))) * (T + \operatorname{peval}\left(N, gamma, D\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/CampoamorStursbergZernikeLadderCore.symmetry` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. Campoamor-Stursberg, F. J. Herranz, D. Latini, I. Marquette, A. Blasco (2026). *Generalized quantum Zernike Hamiltonians: Polynomial Higgs-type algebras and algebraic derivation of the spectrum*. DOI: [10.1088/1361-6544/ae64a2](https://doi.org/10.1088/1361-6544/ae64a2). URL: <https://arxiv.org/abs/2502.02491v2>.

*Commentary.*

Shift relations make the divided-difference ladder commute with the polynomial Hamiltonian.

**Theorem 1.24 (ProductIdentity.factorization).**

$$\forall (B: Type), [\operatorname{Ring}\left(B\right)] [\operatorname{Algebra}\left(\mathbb{C}, B\right)], \forall (N: \mathbb{N}), \forall (gamma: \mathbb{N} \to \mathbb{C}), \forall (alpha: \mathbb{C}), \forall (D: B), \forall (A: B), \forall (T: B), \forall (R: B), \forall (S: B), \forall (U: B), \forall (V: B), ((\operatorname{Commute}\left(D, A\right)) \land ((D) * (S) = (S) * (D + (alpha) \cdot (1))) \land ((A + (alpha) \cdot (1)) * (S) = (S) * (A)) \land ((D) * (V) = (V) * (D)) \land ((A + (alpha) \cdot (1)) * (V) = (V) * (A)) \land ((D) * (T) = (T) * (D + (alpha) \cdot (1))) \land ((A) * (T) = (T) * (A)) \land ((R) * (S) = (T) * (T)) \land ((R) * (V) = (T) * (D - \left((alpha) \cdot (1) - A\right))) \land ((U) * (S) = (T) * (D + (alpha) \cdot (1) - A)) \land ((U) * (V) = (D - \left((alpha) \cdot (1) - A\right)) * (D - A))) \implies ((R + (U) * (\operatorname{divided}\left(N, gamma, D, A + (alpha) \cdot (1)\right))) * (S + (V) * (\operatorname{divided}\left(N, gamma, D, (alpha) \cdot (1) - A\right))) = (T + \operatorname{peval}\left(N, gamma, D\right) - \operatorname{peval}\left(N, gamma, A\right)) * (T + \operatorname{peval}\left(N, gamma, D\right) - \operatorname{peval}\left(N, gamma, (alpha) \cdot (1) - A\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/CampoamorStursbergZernikeLadderCore.factorization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. Campoamor-Stursberg, F. J. Herranz, D. Latini, I. Marquette, A. Blasco (2026). *Generalized quantum Zernike Hamiltonians: Polynomial Higgs-type algebras and algebraic derivation of the spectrum*. DOI: [10.1088/1361-6544/ae64a2](https://doi.org/10.1088/1361-6544/ae64a2). URL: <https://arxiv.org/abs/2502.02491v2>.

*Commentary.*

The two ordered ladders multiply to the two factors obtained from the polynomial evaluations.

**Theorem 1.25 (Corrections.monotone).**

$$\forall (N: \mathbb{N}), \forall (M: \mathbb{N}), (N \leq M) \implies (\operatorname{corrections}\left(N\right) \leq \operatorname{corrections}\left(M\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/CampoamorStursbergZernikeLadderCore.monotone` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. Campoamor-Stursberg, F. J. Herranz, D. Latini, I. Marquette, A. Blasco (2026). *Generalized quantum Zernike Hamiltonians: Polynomial Higgs-type algebras and algebraic derivation of the spectrum*. DOI: [10.1088/1361-6544/ae64a2](https://doi.org/10.1088/1361-6544/ae64a2). URL: <https://arxiv.org/abs/2502.02491v2>.

*Commentary.*

Increasing N enlarges the correction span.

**Theorem 1.26 (Corrections.firstOrder_mem).**

$$\forall (N: \mathbb{N}), (1 \leq N) \implies (\forall (i: \operatorname{Fin}\left(2\right)), \forall (j: \operatorname{Fin}\left(2\right)), (\operatorname{q}\left(i\right)) * (\operatorname{p}\left(j\right)) \in \operatorname{corrections}\left(N\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/CampoamorStursbergZernikeLadderCore.firstOrder_mem` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. Campoamor-Stursberg, F. J. Herranz, D. Latini, I. Marquette, A. Blasco (2026). *Generalized quantum Zernike Hamiltonians: Polynomial Higgs-type algebras and algebraic derivation of the spectrum*. DOI: [10.1088/1361-6544/ae64a2](https://doi.org/10.1088/1361-6544/ae64a2). URL: <https://arxiv.org/abs/2502.02491v2>.

*Commentary.*

Every coordinate-momentum product belongs to the correction span for N at least one.

**Theorem 1.27 (Corrections.dot_mem).**

$$\forall (N: \mathbb{N}), (1 \leq N) \implies (dot \in \operatorname{corrections}\left(N\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/CampoamorStursbergZernikeLadderCore.dot_mem` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. Campoamor-Stursberg, F. J. Herranz, D. Latini, I. Marquette, A. Blasco (2026). *Generalized quantum Zernike Hamiltonians: Polynomial Higgs-type algebras and algebraic derivation of the spectrum*. DOI: [10.1088/1361-6544/ae64a2](https://doi.org/10.1088/1361-6544/ae64a2). URL: <https://arxiv.org/abs/2502.02491v2>.

*Commentary.*

The coordinate-momentum contraction belongs to the same span.

**Theorem 1.28 (Corrections.dot_pow_mul_mem).**

$$\forall (N: \mathbb{N}), \forall (r: \mathbb{N}), \forall (A: \operatorname{Module}.\operatorname{End}(\mathbb{C}, \operatorname{MvPolynomial}\left(\operatorname{Fin}\left(2\right), \mathbb{C}\right))), (A \in \operatorname{corrections}\left(N\right)) \implies (((dot)^{r}) * (A) \in \operatorname{corrections}\left(N + r\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/CampoamorStursbergZernikeLadderCore.dot_pow_mul_mem` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. Campoamor-Stursberg, F. J. Herranz, D. Latini, I. Marquette, A. Blasco (2026). *Generalized quantum Zernike Hamiltonians: Polynomial Higgs-type algebras and algebraic derivation of the spectrum*. DOI: [10.1088/1361-6544/ae64a2](https://doi.org/10.1088/1361-6544/ae64a2). URL: <https://arxiv.org/abs/2502.02491v2>.

*Commentary.*

Multiplication by dot to the power r preserves grading zero and increases the positive total-degree bound by at most 2r.

**Theorem 1.29 (Corrections.C_pow_mul_mem).**

$$\forall (N: \mathbb{N}), \forall (r: \mathbb{N}), \forall (A: \operatorname{Module}.\operatorname{End}(\mathbb{C}, \operatorname{MvPolynomial}\left(\operatorname{Fin}\left(2\right), \mathbb{C}\right))), (A \in \operatorname{corrections}\left(N\right)) \implies (\forall (s: \mathbb{C}), (((s) \cdot (angularMomentum))^{r}) * (A) \in \operatorname{corrections}\left(N + r\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/CampoamorStursbergZernikeLadderCore.C_pow_mul_mem` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. Campoamor-Stursberg, F. J. Herranz, D. Latini, I. Marquette, A. Blasco (2026). *Generalized quantum Zernike Hamiltonians: Polynomial Higgs-type algebras and algebraic derivation of the spectrum*. DOI: [10.1088/1361-6544/ae64a2](https://doi.org/10.1088/1361-6544/ae64a2). URL: <https://arxiv.org/abs/2502.02491v2>.

*Commentary.*

The same filtration estimate holds for any scalar multiple of angular momentum.

## References

- Truth anchor: `D5/S3/Quantum/CampoamorStursbergZernikeLadderCore.C_pow_mul_mem`
- Truth anchor: `D5/S3/Quantum/CampoamorStursbergZernikeLadderCore.IsSymmetry`
- Truth anchor: `D5/S3/Quantum/CampoamorStursbergZernikeLadderCore.angularMomentum`
- Truth anchor: `D5/S3/Quantum/CampoamorStursbergZernikeLadderCore.corrections`
- Truth anchor: `D5/S3/Quantum/CampoamorStursbergZernikeLadderCore.divided`
- Truth anchor: `D5/S3/Quantum/CampoamorStursbergZernikeLadderCore.divided_commute_left`
- Truth anchor: `D5/S3/Quantum/CampoamorStursbergZernikeLadderCore.dot`
- Truth anchor: `D5/S3/Quantum/CampoamorStursbergZernikeLadderCore.dot_mem`
- Truth anchor: `D5/S3/Quantum/CampoamorStursbergZernikeLadderCore.dot_pow_mul_mem`
- Truth anchor: `D5/S3/Quantum/CampoamorStursbergZernikeLadderCore.factorization`
- Truth anchor: `D5/S3/Quantum/CampoamorStursbergZernikeLadderCore.firstOrder_mem`
- Truth anchor: `D5/S3/Quantum/CampoamorStursbergZernikeLadderCore.hamiltonian`
- Truth anchor: `D5/S3/Quantum/CampoamorStursbergZernikeLadderCore.intertwine_divided`
- Truth anchor: `D5/S3/Quantum/CampoamorStursbergZernikeLadderCore.k1`
- Truth anchor: `D5/S3/Quantum/CampoamorStursbergZernikeLadderCore.k2`
- Truth anchor: `D5/S3/Quantum/CampoamorStursbergZernikeLadderCore.k3`
- Truth anchor: `D5/S3/Quantum/CampoamorStursbergZernikeLadderCore.monomial`
- Truth anchor: `D5/S3/Quantum/CampoamorStursbergZernikeLadderCore.monotone`
- Truth anchor: `D5/S3/Quantum/CampoamorStursbergZernikeLadderCore.p`
- Truth anchor: `D5/S3/Quantum/CampoamorStursbergZernikeLadderCore.peval`
- Truth anchor: `D5/S3/Quantum/CampoamorStursbergZernikeLadderCore.peval_commute_left`
- Truth anchor: `D5/S3/Quantum/CampoamorStursbergZernikeLadderCore.phi`
- Truth anchor: `D5/S3/Quantum/CampoamorStursbergZernikeLadderCore.phi1`
- Truth anchor: `D5/S3/Quantum/CampoamorStursbergZernikeLadderCore.phi2`
- Truth anchor: `D5/S3/Quantum/CampoamorStursbergZernikeLadderCore.pp`
- Truth anchor: `D5/S3/Quantum/CampoamorStursbergZernikeLadderCore.pq`
- Truth anchor: `D5/S3/Quantum/CampoamorStursbergZernikeLadderCore.q`
- Truth anchor: `D5/S3/Quantum/CampoamorStursbergZernikeLadderCore.qq`
- Truth anchor: `D5/S3/Quantum/CampoamorStursbergZernikeLadderCore.symmetry`
