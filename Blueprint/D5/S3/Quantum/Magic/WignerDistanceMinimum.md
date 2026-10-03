# Wigner distance minimum attainment

## Abstract

The free Wigner polytopes are compact and nonempty, so the source minimum defining C is attained and minimal in the L1 norm.

**Definition 1.1 (The phase-point carrier).**

$$PhasePoint = \operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)$$

*Formalization.* `D5/S3/Quantum/Magic/WignerDistanceMinimum.PhasePoint` (`✓ std3`).

*Citation.* Soumyojyoti Dutta; Tushar (2026). *A Phase-Space Geometric Measure of Magic in Qubit Systems*. DOI: [10.48550/arXiv.2603.20792](https://doi.org/10.48550/arXiv.2603.20792). URL: <https://arxiv.org/abs/2603.20792v3>.

*Commentary.*

A phase point is a pair (q,p) of binary indices, with Fin 2 representing the elements 0 and 1 of the paper's F₂.

**Definition 1.2 (The Wootters phase-point operator).**

$$\forall a \in PhasePoint,\; \operatorname{phasePoint}\left(a\right) = \operatorname{smul}\left(\frac{1}{2}, (1 + \operatorname{smul}\left((0 - 1)^{\operatorname{val}\left(\operatorname{snd}\left(a\right)\right)}, \operatorname{pauliMatrix}\left(X\right)\right) + \operatorname{smul}\left((0 - 1)^{\operatorname{val}\left(\operatorname{fst}\left(a\right)\right) + \operatorname{val}\left(\operatorname{snd}\left(a\right)\right)}, \operatorname{pauliMatrix}\left(Y\right)\right) + \operatorname{smul}\left((0 - 1)^{\operatorname{val}\left(\operatorname{fst}\left(a\right)\right)}, \operatorname{pauliMatrix}\left(Z\right)\right))\right)$$

*Formalization.* `D5/S3/Quantum/Magic/WignerDistanceMinimum.phasePoint` (`✓ std3`).

*Citation.* Soumyojyoti Dutta; Tushar (2026). *A Phase-Space Geometric Measure of Magic in Qubit Systems*. DOI: [10.48550/arXiv.2603.20792](https://doi.org/10.48550/arXiv.2603.20792). URL: <https://arxiv.org/abs/2603.20792v3>.

*Commentary.*

Page 3: "The single-qubit phase-point operators are indexed by αₖ = (qₖ, pₖ) ∈ F₂²:" followed by A_(qₖ,pₖ) = ½(I + (−1)^pₖ X + (−1)^(qₖ+pₖ) Y + (−1)^qₖ Z). Here q = fst(a), p = snd(a), and val reads their natural-number representatives. The coefficient ½ and the sign powers are complex scalars; 1 inside the matrix sum is the identity matrix.

**Definition 1.3 (The product frame).**

$$\forall a \in PhasePoint \times PhasePoint,\; \operatorname{phasePointTwo}\left(a\right) = \operatorname{kronecker}\left(\operatorname{phasePoint}\left(\operatorname{fst}\left(a\right)\right), \operatorname{phasePoint}\left(\operatorname{snd}\left(a\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Magic/WignerDistanceMinimum.phasePointTwo` (`✓ std3`).

*Citation.* Soumyojyoti Dutta; Tushar (2026). *A Phase-Space Geometric Measure of Magic in Qubit Systems*. DOI: [10.48550/arXiv.2603.20792](https://doi.org/10.48550/arXiv.2603.20792). URL: <https://arxiv.org/abs/2603.20792v3>.

*Commentary.*

Page 3: "For n qubits, A_α = A_α₁ ⊗ ··· ⊗ A_αₙ, and the discrete Wigner function is" W_ρ(α) = (1/2ⁿ) tr(ρ A_α). phasePointTwo uses n = 2. kronecker denotes the matrix tensor product in the product computational basis.

**Definition 1.4 (The Wigner transform).**

$$\forall iota \in Type,\; \forall alpha \in Type,\; [\operatorname{Fintype}\left(iota\right)], \forall A \in alpha \to \operatorname{Matrix}\left(iota, iota, \mathbb{C}\right),\; \forall rho \in \operatorname{Matrix}\left(iota, iota, \mathbb{C}\right),\; \forall a \in alpha,\; \operatorname{Wigner}\left(A, rho\right)\left(a\right) = \frac{\operatorname{re}\left(\operatorname{trace}\left(rho \cdot A\left(a\right)\right)\right)}{\operatorname{realCast}\left(\operatorname{card}\left(iota\right)\right)}$$

*Formalization.* `D5/S3/Quantum/Magic/WignerDistanceMinimum.Wigner` (`✓ std3`).

*Citation.* Soumyojyoti Dutta; Tushar (2026). *A Phase-Space Geometric Measure of Magic in Qubit Systems*. DOI: [10.48550/arXiv.2603.20792](https://doi.org/10.48550/arXiv.2603.20792). URL: <https://arxiv.org/abs/2603.20792v3>.

*Commentary.*

Page 3: "For n qubits, A_α = A_α₁ ⊗ ··· ⊗ A_αₙ, and the discrete Wigner function is" W_ρ(α) = (1/2ⁿ) tr(ρ A_α). The generic transform divides the real part of the trace by the Hilbert-space dimension, card(ι); for one and two qubits this is 2 and 4. The trace is real on Hermitian states. The division is real division after casting card(ι) to R.

**Definition 1.5 (One-qubit Wigner coordinates).**

$$\forall rho \in QubitMatrix,\; \operatorname{WignerOne}\left(rho\right) = \operatorname{Wigner}\left(phasePoint, rho\right)$$

*Formalization.* `D5/S3/Quantum/Magic/WignerDistanceMinimum.WignerOne` (`✓ std3`).

*Citation.* Soumyojyoti Dutta; Tushar (2026). *A Phase-Space Geometric Measure of Magic in Qubit Systems*. DOI: [10.48550/arXiv.2603.20792](https://doi.org/10.48550/arXiv.2603.20792). URL: <https://arxiv.org/abs/2603.20792v3>.

*Commentary.*

WignerOne is the transform in the four-point single-qubit frame.

**Definition 1.6 (Two-qubit Wigner coordinates).**

$$\forall rho \in TwoQubitMatrix,\; \operatorname{WignerTwo}\left(rho\right) = \operatorname{Wigner}\left(phasePointTwo, rho\right)$$

*Formalization.* `D5/S3/Quantum/Magic/WignerDistanceMinimum.WignerTwo` (`✓ std3`).

*Citation.* Soumyojyoti Dutta; Tushar (2026). *A Phase-Space Geometric Measure of Magic in Qubit Systems*. DOI: [10.48550/arXiv.2603.20792](https://doi.org/10.48550/arXiv.2603.20792). URL: <https://arxiv.org/abs/2603.20792v3>.

*Commentary.*

WignerTwo is the transform in the sixteen-point product frame.

**Definition 1.7 (The phased Pauli group on two qubits).**

$$\forall P \in TwoQubitMatrix,\; (P \in pauliTwo) \Leftrightarrow (\exists c \in \mathbb{C},\; (c \in \{1,0 - 1,i,0 - i\}) \land (\exists p \in Pauli,\; \exists q \in Pauli,\; P = \operatorname{smul}\left(c, \operatorname{kronecker}\left(\operatorname{pauliMatrix}\left(p\right), \operatorname{pauliMatrix}\left(q\right)\right)\right)))$$

*Formalization.* `D5/S3/Quantum/Magic/WignerDistanceMinimum.pauliTwo` (`✓ std3`).

*Citation.* Soumyojyoti Dutta; Tushar (2026). *A Phase-Space Geometric Measure of Magic in Qubit Systems*. DOI: [10.48550/arXiv.2603.20792](https://doi.org/10.48550/arXiv.2603.20792). URL: <https://arxiv.org/abs/2603.20792v3>.

*Commentary.*

Page 3: "The n-qubit Pauli group Pₙ consists of n-fold tensor products of {I, X, Y, Z} with phases {±1, ±i}." These are the actual phased tensor-product matrices, including all four phases.

**Definition 1.8 (Stabilizer states from their subgroups).**

$$\forall iota \in Type,\; [\operatorname{Fintype}\left(iota\right)], [\operatorname{DecidableEq}\left(iota\right)], \forall P \in \operatorname{Set}\left((\operatorname{Matrix}\left(iota, iota, \mathbb{C}\right))\right),\; \forall rho \in \operatorname{Matrix}\left(iota, iota, \mathbb{C}\right),\; (rho \in \operatorname{Stab}\left(P\right)) \Leftrightarrow (\exists S \in \operatorname{Subgroup}\left(\operatorname{unitaryGroup}\left(iota, \mathbb{C}\right)\right),\; \exists psi \in iota \to \mathbb{C},\; (((((\forall g \in S,\; \operatorname{val}\left(\operatorname{val}\left(g\right)\right) \in P) \land (\operatorname{NatCard}\left(S\right) = \operatorname{card}\left(iota\right))) \land (\forall g \in S,\; \forall h \in S,\; g \cdot h = h \cdot g)) \land (\sum_{j:iota} (\operatorname{norm}\left(psi\left(j\right)\right))^{2} = 1)) \land (\forall v \in iota \to \mathbb{C},\; (\forall g \in S,\; \operatorname{mulVec}\left(\operatorname{val}\left(\operatorname{val}\left(g\right)\right), v\right) = v) \Leftrightarrow (\exists c \in \mathbb{C},\; v = \operatorname{smul}\left(c, psi\right)))) \land (rho = \operatorname{vecMulVec}\left(psi, \operatorname{star}\left(psi\right)\right)))$$

*Formalization.* `D5/S3/Quantum/Magic/WignerDistanceMinimum.Stab` (`✓ std3`).

*Citation.* Soumyojyoti Dutta; Tushar (2026). *A Phase-Space Geometric Measure of Magic in Qubit Systems*. DOI: [10.48550/arXiv.2603.20792](https://doi.org/10.48550/arXiv.2603.20792). URL: <https://arxiv.org/abs/2603.20792v3>.

*Commentary.*

Page 3: "A stabilizer state is the unique +1 eigenstate of an abelian subgroup S ≤ Pₙ of size 2ⁿ." Stab(P) requires an actual subgroup of the matrix unitary group whose matrices belong to P, with cardinality equal to the Hilbert-space dimension. The subgroup is abelian, ψ is normalized, and its common +1 eigenspace is exactly the complex line spanned by ψ. The density is the outer product ψψ*. NatCard denotes Nat.card; card denotes Fintype.card. The two val calls unwrap the subgroup and unitary subtypes. mulVec is matrix action, smul is scalar multiplication, and vecMulVec is the outer product.

**Definition 1.9 (The free Wigner polytope).**

$$\forall iota \in Type,\; \forall alpha \in Type,\; [\operatorname{Fintype}\left(iota\right)], [\operatorname{DecidableEq}\left(iota\right)], \forall A \in alpha \to \operatorname{Matrix}\left(iota, iota, \mathbb{C}\right),\; \forall P \in \operatorname{Set}\left((\operatorname{Matrix}\left(iota, iota, \mathbb{C}\right))\right),\; \operatorname{Wfree}\left(A, P\right) = \operatorname{convexHull}\left(\mathbb{R}, \operatorname{image}\left(\operatorname{Wigner}\left(A\right), \operatorname{Stab}\left(P\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Magic/WignerDistanceMinimum.Wfree` (`✓ std3`).

*Citation.* Soumyojyoti Dutta; Tushar (2026). *A Phase-Space Geometric Measure of Magic in Qubit Systems*. DOI: [10.48550/arXiv.2603.20792](https://doi.org/10.48550/arXiv.2603.20792). URL: <https://arxiv.org/abs/2603.20792v3>.

*Commentary.*

Page 3: "The stabilizer Wigner polytope is Wfree := conv{W_σ : σ ∈ Stabₙ} ⊂ R^(4ⁿ)." The imported pauliSet is the phased one-qubit Pauli group. Wfree(A,P) takes the real convex hull of the image of the subgroup-defined stabilizer set under Wigner(A). image is set image, so the representation includes every free mixture.

**Definition 1.10 (The single-qubit Wigner distance).**

$$\forall rho \in QubitMatrix,\; \operatorname{COne}\left(rho\right) = \operatorname{infDist}\left(\operatorname{toLp}\left(1, \operatorname{WignerOne}\left(rho\right)\right), \operatorname{image}\left(\operatorname{toLp}\left(1\right), \operatorname{Wfree}\left(phasePoint, pauliSet\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Magic/WignerDistanceMinimum.COne` (`✓ std3`).

*Citation.* Soumyojyoti Dutta; Tushar (2026). *A Phase-Space Geometric Measure of Magic in Qubit Systems*. DOI: [10.48550/arXiv.2603.20792](https://doi.org/10.48550/arXiv.2603.20792). URL: <https://arxiv.org/abs/2603.20792v3>.

*Commentary.*

Page 3, Definition 3.1 (Wigner distance): "C(ρ) := min_{W_f ∈ Wfree} ‖W_ρ − W_f‖₁." COne uses the paper's four-point frame and actual local stabilizer polytope. COne_min proves attainment and minimality for every qubit matrix.

**Definition 1.11 (The two-qubit Wigner distance).**

$$\forall rho \in TwoQubitMatrix,\; \operatorname{CTwo}\left(rho\right) = \operatorname{infDist}\left(\operatorname{toLp}\left(1, \operatorname{WignerTwo}\left(rho\right)\right), \operatorname{image}\left(\operatorname{toLp}\left(1\right), \operatorname{Wfree}\left(phasePointTwo, pauliTwo\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Magic/WignerDistanceMinimum.CTwo` (`✓ std3`).

*Citation.* Soumyojyoti Dutta; Tushar (2026). *A Phase-Space Geometric Measure of Magic in Qubit Systems*. DOI: [10.48550/arXiv.2603.20792](https://doi.org/10.48550/arXiv.2603.20792). URL: <https://arxiv.org/abs/2603.20792v3>.

*Commentary.*

Page 3, Definition 3.1 (Wigner distance): "C(ρ) := min_{W_f ∈ Wfree} ‖W_ρ − W_f‖₁." CTwo uses the sixteen-point frame and actual two-qubit stabilizer polytope, including entangled stabilizers. CTwo_min proves attainment and minimality for every two-qubit matrix.

**Definition 1.12 (Pauli spectral projectors).**

$$\forall p \in Pauli,\; \forall epsilon \in \operatorname{Fin}\left(2\right),\; \operatorname{spectral}\left(p, epsilon\right) = \operatorname{smul}\left(\frac{1}{2}, (1 + \operatorname{smul}\left((0 - 1)^{\operatorname{val}\left(epsilon\right)}, \operatorname{pauliMatrix}\left(p\right)\right))\right)$$

*Formalization.* `D5/S3/Quantum/Magic/WignerDistanceMinimum.spectral` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a nonidentity Pauli p, spectral(p,epsilon) is the rank-one projector onto its eigenvalue (-1)^epsilon. The identity case is included in the definition.

**Definition 1.13 (Explicit Pauli eigenvectors).**

$$\forall epsilon \in \operatorname{Fin}\left(2\right),\; (((\operatorname{eigenVector}\left(I, epsilon\right) = [1,0]) \land (\operatorname{eigenVector}\left(X, epsilon\right) = [\operatorname{complexCast}\left(\operatorname{inv}\left(\operatorname{sqrt}\left(2\right)\right)\right),(0 - 1)^{\operatorname{val}\left(epsilon\right)} \cdot \operatorname{complexCast}\left(\operatorname{inv}\left(\operatorname{sqrt}\left(2\right)\right)\right)])) \land (\operatorname{eigenVector}\left(Y, epsilon\right) = [\operatorname{complexCast}\left(\operatorname{inv}\left(\operatorname{sqrt}\left(2\right)\right)\right),i \cdot (0 - 1)^{\operatorname{val}\left(epsilon\right)} \cdot \operatorname{complexCast}\left(\operatorname{inv}\left(\operatorname{sqrt}\left(2\right)\right)\right)])) \land (\operatorname{eigenVector}\left(Z, epsilon\right) = \operatorname{ite}\left(epsilon = 0, [1,0], [0,1]\right))$$

*Formalization.* `D5/S3/Quantum/Magic/WignerDistanceMinimum.eigenVector` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The bracket notation denotes a two-component complex vector. The scalar r is the complex cast of the inverse square root of 2, and t = (-1)^epsilon. The four cases are I: [1,0], X: [r,tr], Y: [r,itr], and Z: [1,0] for epsilon = 0 and [0,1] otherwise.

**Theorem 1.14 (Actual local stabilizer subgroups).**

$$\forall p \in Pauli,\; \forall epsilon \in \operatorname{Fin}\left(2\right),\; (p \ne I) \Rightarrow ((\operatorname{spectral}\left(p, epsilon\right) \in \operatorname{Stab}\left(pauliSet\right)) \land (\exists U \in \operatorname{MonoidHom}\left(\operatorname{Multiplicative}\left(\operatorname{ZMod}\left(2\right)\right), \operatorname{unitaryGroup}\left(\operatorname{Fin}\left(2\right), \mathbb{C}\right)\right),\; (((((\operatorname{Injective}\left(U\right)) \land (\forall x \in \operatorname{Multiplicative}\left(\operatorname{ZMod}\left(2\right)\right),\; \operatorname{val}\left(U\left(x\right)\right) \in pauliSet)) \land (\forall x \in \operatorname{Multiplicative}\left(\operatorname{ZMod}\left(2\right)\right),\; \operatorname{trace}\left(\operatorname{val}\left(U\left(x\right)\right)\right) = \operatorname{ite}\left(x = 1, 2, 0\right))) \land (\sum_{j:\operatorname{Fin}\left(2\right)} (\operatorname{norm}\left(\operatorname{eigenVector}\left(p, epsilon\right)\left(j\right)\right))^{2} = 1)) \land (\operatorname{smul}\left(\operatorname{inv}\left(\operatorname{complexCast}\left(\operatorname{card}\left(\operatorname{Multiplicative}\left(\operatorname{ZMod}\left(2\right)\right)\right)\right)\right), \sum_{x:\operatorname{Multiplicative}\left(\operatorname{ZMod}\left(2\right)\right)} \operatorname{val}\left(U\left(x\right)\right)\right) = \operatorname{vecMulVec}\left(\operatorname{eigenVector}\left(p, epsilon\right), \operatorname{star}\left(\operatorname{eigenVector}\left(p, epsilon\right)\right)\right))) \land (\operatorname{spectral}\left(p, epsilon\right) = \operatorname{vecMulVec}\left(\operatorname{eigenVector}\left(p, epsilon\right), \operatorname{star}\left(\operatorname{eigenVector}\left(p, epsilon\right)\right)\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Magic/WignerDistanceMinimum.spectral_stabilizer` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each nonidentity Pauli spectral projector is an actual stabilizer state. An injective homomorphism from the multiplicative cyclic group of order two supplies its subgroup. Its nonidentity matrix has trace zero, its eigenvector is normalized, and its group average is exactly the eigenvector's outer product.

**Theorem 1.15 (Actual product stabilizer subgroups).**

$$\forall p \in Pauli,\; \forall q \in Pauli,\; \forall epsilon \in \operatorname{Fin}\left(2\right),\; \forall delta \in \operatorname{Fin}\left(2\right),\; (p \ne I) \Rightarrow ((q \ne I) \Rightarrow (\operatorname{kronecker}\left(\operatorname{spectral}\left(p, epsilon\right), \operatorname{spectral}\left(q, delta\right)\right) \in \operatorname{Stab}\left(pauliTwo\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Magic/WignerDistanceMinimum.spectral_product_stabilizer` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Tensoring two Pauli spectral projectors gives a stabilizer state in the full phased two-qubit Pauli group. The construction uses the product of the two local cyclic subgroups and the tensor eigenvector.

**Theorem 1.16 (The single-qubit Wigner distance attains the source minimum).**

$$\forall rho \in QubitMatrix,\; \exists f \in PhasePoint \to \mathbb{R},\; (f \in \operatorname{Wfree}\left(phasePoint, pauliSet\right)) \land ((\operatorname{COne}\left(rho\right) = \operatorname{norm}\left(\operatorname{toLp}\left(1, \operatorname{WignerOne}\left(rho\right) - f\right)\right)) \land (\forall g \in PhasePoint \to \mathbb{R},\; (g \in \operatorname{Wfree}\left(phasePoint, pauliSet\right)) \Rightarrow (\operatorname{COne}\left(rho\right) \le \operatorname{norm}\left(\operatorname{toLp}\left(1, \operatorname{WignerOne}\left(rho\right) - g\right)\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Magic/WignerDistanceMinimum.COne_min` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

$$
\operatorname{COne}\left(rho\right) = \min_{f \in \operatorname{Wfree}\left(phasePoint, pauliSet\right)} \operatorname{norm}\left(\operatorname{toLp}\left(1, \operatorname{WignerOne}\left(rho\right) - f\right)\right)
$$

For every qubit matrix rho, the source formula C(rho) := min_{W_f ∈ Wfree} ‖W_rho − W_f‖₁ is attained by some f in the compact nonempty free polytope, and COne rho is no larger than every free candidate.

**Theorem 1.17 (The two-qubit Wigner distance attains the source minimum).**

$$\forall rho \in TwoQubitMatrix,\; \exists f \in PhasePoint \times PhasePoint \to \mathbb{R},\; (f \in \operatorname{Wfree}\left(phasePointTwo, pauliTwo\right)) \land ((\operatorname{CTwo}\left(rho\right) = \operatorname{norm}\left(\operatorname{toLp}\left(1, \operatorname{WignerTwo}\left(rho\right) - f\right)\right)) \land (\forall g \in PhasePoint \times PhasePoint \to \mathbb{R},\; (g \in \operatorname{Wfree}\left(phasePointTwo, pauliTwo\right)) \Rightarrow (\operatorname{CTwo}\left(rho\right) \le \operatorname{norm}\left(\operatorname{toLp}\left(1, \operatorname{WignerTwo}\left(rho\right) - g\right)\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Magic/WignerDistanceMinimum.CTwo_min` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

$$
\operatorname{CTwo}\left(rho\right) = \min_{f \in \operatorname{Wfree}\left(phasePointTwo, pauliTwo\right)} \operatorname{norm}\left(\operatorname{toLp}\left(1, \operatorname{WignerTwo}\left(rho\right) - f\right)\right)
$$

For every two-qubit matrix rho, the same source minimum C(rho) := min_{W_f ∈ Wfree} ‖W_rho − W_f‖₁ is attained by some f in the compact nonempty two-qubit free polytope, and CTwo rho is no larger than every free candidate.

## References

- Truth anchor: `D5/S3/Quantum/Magic/WignerDistanceMinimum.COne`
- Truth anchor: `D5/S3/Quantum/Magic/WignerDistanceMinimum.COne_min`
- Truth anchor: `D5/S3/Quantum/Magic/WignerDistanceMinimum.CTwo`
- Truth anchor: `D5/S3/Quantum/Magic/WignerDistanceMinimum.CTwo_min`
- Truth anchor: `D5/S3/Quantum/Magic/WignerDistanceMinimum.PhasePoint`
- Truth anchor: `D5/S3/Quantum/Magic/WignerDistanceMinimum.Stab`
- Truth anchor: `D5/S3/Quantum/Magic/WignerDistanceMinimum.Wfree`
- Truth anchor: `D5/S3/Quantum/Magic/WignerDistanceMinimum.Wigner`
- Truth anchor: `D5/S3/Quantum/Magic/WignerDistanceMinimum.WignerOne`
- Truth anchor: `D5/S3/Quantum/Magic/WignerDistanceMinimum.WignerTwo`
- Truth anchor: `D5/S3/Quantum/Magic/WignerDistanceMinimum.eigenVector`
- Truth anchor: `D5/S3/Quantum/Magic/WignerDistanceMinimum.pauliTwo`
- Truth anchor: `D5/S3/Quantum/Magic/WignerDistanceMinimum.phasePoint`
- Truth anchor: `D5/S3/Quantum/Magic/WignerDistanceMinimum.phasePointTwo`
- Truth anchor: `D5/S3/Quantum/Magic/WignerDistanceMinimum.spectral`
- Truth anchor: `D5/S3/Quantum/Magic/WignerDistanceMinimum.spectral_product_stabilizer`
- Truth anchor: `D5/S3/Quantum/Magic/WignerDistanceMinimum.spectral_stabilizer`
- Dependency: [D5/S3/Quantum/Information/BinaryStabilizerLocalInequivalence](../Information/BinaryStabilizerLocalInequivalence.md)
- Dependency: [D5/S3/Quantum/Information/StabilizerPairLocalUnitaryInequivalence](../Information/StabilizerPairLocalUnitaryInequivalence.md)
- Dependency: [D5/S3/QuantumBounds/CHSHWitness](../../QuantumBounds/CHSHWitness.md)
