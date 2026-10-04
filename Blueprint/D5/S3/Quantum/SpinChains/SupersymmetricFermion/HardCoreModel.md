# Supersymmetric fermion chain: HardCoreModel

## Abstract

Jordan-Wigner fermions, hard-core compression and the M1 boundary sum rule.

Nat, Real, Complex and Bool denote the natural numbers, real numbers, complex numbers and the two occupation values false and true. Assignment(N) is Fin N → Bool. All finite-type sums and products range over the displayed type; range(N) is {0,...,N−1}. Subtraction in Nat is truncated at zero; mod is natural remainder, inv is field inverse, smul is scalar multiplication and div is field division. asReal and the annotation Complex retain scalar casts. val denotes the value of a Fin index or subtype; mk displays a Fin value with its proof component suppressed. adjoint is the conjugate transpose on matrices and the genuine Hilbert adjoint on linear operators. A mapsto denotes a function; const denotes a constant function with the domain supplied by its type. Lambda applications express local let substitutions. spinZ denotes qubitZ transported through finTwoEquiv : Fin 2 ≃ Bool; spinP is 1−visibleProjector. Matrixsingle(false,true,1) is Mathlib’s elementary matrix on Boolean indices, with entry 1 at the empty-row/occupied-column pair and 0 elsewhere. tensorOp(w) is the tensor product transported to Boolean coordinates: its entry at s,t is ∏_(i : Fin N) w(i)(s(i))(t(i)). These are local notations, not additional operators. boolReindex transports a matrix from Fin N → Fin 2 to Fin N → Bool through the pointwise finTwoEquiv. finTwoReindex transports the Boolean visibleProjector to Fin 2 indices; localOp is the existing single-site tensor operator. submatrix(A,Subtypeval,Subtypeval) restricts both matrix indices to the hard-core subtype. All other names refer to the displayed definitions or Mathlib operations; function names omit dots and underscores.

**Definition 1.1 (HardCore).**

$$\forall N \in \mathit{Nat},\; (\mathrm{HardCore}\left(N\right):\mathit{Type}) = \mathrm{Subtype}\left(s:\mathrm{Assignment}\left(N\right)\mapsto(\mathrm{Adm}\left(N, s\right))\right)$$

*Formalization.* `D5/S3/Quantum/SpinChains/SupersymmetricFermion/HardCoreModel.HardCore` (`✓ std3`).

*Citation.* Matteo Beccaria; Christian Hagendorf (2012). *A staggered fermion chain with supersymmetry on open intervals*. DOI: [10.1088/1751-8113/45/36/365201](https://doi.org/10.1088/1751-8113/45/36/365201). URL: <https://arxiv.org/abs/1206.4194v2>.

*Commentary.*

Section 2.1, printed page 3: “nearest-neighbour exclusion: at most one of two adjacent sites may be occupied.” “We shall work with free boundary conditions what is equivalent to add two inaccessible but empty sites at j = 0 and j = N + 1.” The operators use the supercharge, projectors and Hamiltonian of that section. HardCore is the subtype defined by Adm(N,s), the admissible-word predicate of AdmissibleCount. ForbiddenNeighbourDeterminant.adm_iff_no_adjacent_true identifies that predicate with nearest-neighbour exclusion.

**Definition 1.2 (HardCoreSpace).**

$$\forall N \in \mathit{Nat},\; (\mathrm{HardCoreSpace}\left(N\right):\mathit{Type}) = \mathrm{EuclideanSpace}\left(\mathit{Complex}, \mathrm{HardCore}\left(N\right)\right)$$

*Formalization.* `D5/S3/Quantum/SpinChains/SupersymmetricFermion/HardCoreModel.HardCoreSpace` (`✓ std3`).

*Citation.* Matteo Beccaria; Christian Hagendorf (2012). *A staggered fermion chain with supersymmetry on open intervals*. DOI: [10.1088/1751-8113/45/36/365201](https://doi.org/10.1088/1751-8113/45/36/365201). URL: <https://arxiv.org/abs/1206.4194v2>.

*Commentary.*

Section 2.1, printed page 3: “nearest-neighbour exclusion: at most one of two adjacent sites may be occupied.” “We shall work with free boundary conditions what is equivalent to add two inaccessible but empty sites at j = 0 and j = N + 1.” The operators use the supercharge, projectors and Hamiltonian of that section. The displayed equation defines HardCoreSpace.

**Definition 1.3 (Operator).**

$$\forall N \in \mathit{Nat},\; (\mathrm{Operator}\left(N\right):\mathit{Type}) = \mathrm{Matrix}\left(\mathrm{HardCore}\left(N\right), \mathrm{HardCore}\left(N\right), \mathit{Complex}\right)$$

*Formalization.* `D5/S3/Quantum/SpinChains/SupersymmetricFermion/HardCoreModel.Operator` (`✓ std3`).

*Citation.* Matteo Beccaria; Christian Hagendorf (2012). *A staggered fermion chain with supersymmetry on open intervals*. DOI: [10.1088/1751-8113/45/36/365201](https://doi.org/10.1088/1751-8113/45/36/365201). URL: <https://arxiv.org/abs/1206.4194v2>.

*Commentary.*

Section 2.1, printed page 3: “nearest-neighbour exclusion: at most one of two adjacent sites may be occupied.” “We shall work with free boundary conditions what is equivalent to add two inaccessible but empty sites at j = 0 and j = N + 1.” The operators use the supercharge, projectors and Hamiltonian of that section. The displayed equation defines Operator.

**Definition 1.4 (occupied).**

$$\forall N \in \mathit{Nat},\; \forall s \in \mathrm{Assignment}\left(N\right),\; \forall j \in \mathit{Nat},\; (\mathrm{occupied}\left(N, s, j\right):\mathit{Bool}) = \mathrm{ite}\left((0 < j) \land (j \le N), s\left(\mathrm{mk}\left((j) - (1)\right)\right), \mathit{false}\right)$$

*Formalization.* `D5/S3/Quantum/SpinChains/SupersymmetricFermion/HardCoreModel.occupied` (`✓ std3`).

*Citation.* Matteo Beccaria; Christian Hagendorf (2012). *A staggered fermion chain with supersymmetry on open intervals*. DOI: [10.1088/1751-8113/45/36/365201](https://doi.org/10.1088/1751-8113/45/36/365201). URL: <https://arxiv.org/abs/1206.4194v2>.

*Commentary.*

Section 2.1, printed page 3: “nearest-neighbour exclusion: at most one of two adjacent sites may be occupied.” “We shall work with free boundary conditions what is equivalent to add two inaccessible but empty sites at j = 0 and j = N + 1.” The operators use the supercharge, projectors and Hamiltonian of that section. The displayed equation defines occupied.

**Definition 1.5 (annihilationAt).**

$$\forall N \in \mathit{Nat},\; \forall i \in \mathrm{Fin}\left(N\right),\; (\mathrm{annihilationAt}\left(N, i\right):\mathrm{Operator}\left(N\right)) = s,t\mapsto(\mathrm{ite}\left((\mathrm{val}\left(t, i\right) = \mathit{true}) \land (\mathrm{val}\left(s\right) = \mathrm{Functionupdate}\left(\mathrm{val}\left(t\right), i, \mathit{false}\right)), ((-1:\mathit{Complex}))^{\mathrm{prefixCount}\left(\mathrm{val}\left(t\right), i\right)}, 0\right))$$

*Formalization.* `D5/S3/Quantum/SpinChains/SupersymmetricFermion/HardCoreModel.annihilationAt` (`✓ std3`).

*Citation.* Matteo Beccaria; Christian Hagendorf (2012). *A staggered fermion chain with supersymmetry on open intervals*. DOI: [10.1088/1751-8113/45/36/365201](https://doi.org/10.1088/1751-8113/45/36/365201). URL: <https://arxiv.org/abs/1206.4194v2>.

*Commentary.*

Section 2.1, printed page 3: “nearest-neighbour exclusion: at most one of two adjacent sites may be occupied.” “We shall work with free boundary conditions what is equivalent to add two inaccessible but empty sites at j = 0 and j = N + 1.” The operators use the supercharge, projectors and Hamiltonian of that section. The displayed equation defines annihilationAt.

**Definition 1.6 (c).**

$$\forall N \in \mathit{Nat},\; \forall j \in \mathit{Nat},\; (\mathrm{c}\left(N, j\right):\mathrm{Operator}\left(N\right)) = \mathrm{ite}\left((0 < j) \land (j \le N), \mathrm{annihilationAt}\left(\mathrm{mk}\left((j) - (1)\right)\right), 0\right)$$

*Formalization.* `D5/S3/Quantum/SpinChains/SupersymmetricFermion/HardCoreModel.c` (`✓ std3`).

*Citation.* Matteo Beccaria; Christian Hagendorf (2012). *A staggered fermion chain with supersymmetry on open intervals*. DOI: [10.1088/1751-8113/45/36/365201](https://doi.org/10.1088/1751-8113/45/36/365201). URL: <https://arxiv.org/abs/1206.4194v2>.

*Commentary.*

Section 2.1, printed page 3: “nearest-neighbour exclusion: at most one of two adjacent sites may be occupied.” “We shall work with free boundary conditions what is equivalent to add two inaccessible but empty sites at j = 0 and j = N + 1.” The operators use the supercharge, projectors and Hamiltonian of that section. The displayed equation defines c.

**Definition 1.7 (number).**

$$\forall N \in \mathit{Nat},\; \forall j \in \mathit{Nat},\; (\mathrm{number}\left(N, j\right):\mathrm{Operator}\left(N\right)) = \mathrm{Matrixdiagonal}\left(s\mapsto(\mathrm{ite}\left(\mathrm{occupied}\left(\mathrm{val}\left(s\right), j\right), 1, 0\right))\right)$$

*Formalization.* `D5/S3/Quantum/SpinChains/SupersymmetricFermion/HardCoreModel.number` (`✓ std3`).

*Citation.* Matteo Beccaria; Christian Hagendorf (2012). *A staggered fermion chain with supersymmetry on open intervals*. DOI: [10.1088/1751-8113/45/36/365201](https://doi.org/10.1088/1751-8113/45/36/365201). URL: <https://arxiv.org/abs/1206.4194v2>.

*Commentary.*

Section 2.1, printed page 3: “nearest-neighbour exclusion: at most one of two adjacent sites may be occupied.” “We shall work with free boundary conditions what is equivalent to add two inaccessible but empty sites at j = 0 and j = N + 1.” The operators use the supercharge, projectors and Hamiltonian of that section. The displayed equation defines number.

**Definition 1.8 (P).**

$$\forall N \in \mathit{Nat},\; \forall j \in \mathit{Nat},\; (\mathrm{P}\left(N, j\right):\mathrm{Operator}\left(N\right)) = (1) - (\mathrm{number}\left(j\right))$$

*Formalization.* `D5/S3/Quantum/SpinChains/SupersymmetricFermion/HardCoreModel.P` (`✓ std3`).

*Citation.* Matteo Beccaria; Christian Hagendorf (2012). *A staggered fermion chain with supersymmetry on open intervals*. DOI: [10.1088/1751-8113/45/36/365201](https://doi.org/10.1088/1751-8113/45/36/365201). URL: <https://arxiv.org/abs/1206.4194v2>.

*Commentary.*

Section 2.1, printed page 3: “nearest-neighbour exclusion: at most one of two adjacent sites may be occupied.” “We shall work with free boundary conditions what is equivalent to add two inaccessible but empty sites at j = 0 and j = N + 1.” The operators use the supercharge, projectors and Hamiltonian of that section. The displayed equation defines P.

**Definition 1.9 (d).**

$$\forall N \in \mathit{Nat},\; \forall j \in \mathit{Nat},\; (\mathrm{d}\left(N, j\right):\mathrm{Operator}\left(N\right)) = ((\mathrm{P}\left((j) - (1)\right)) \cdot (\mathrm{c}\left(j\right))) \cdot (\mathrm{P}\left((j) + (1)\right))$$

*Formalization.* `D5/S3/Quantum/SpinChains/SupersymmetricFermion/HardCoreModel.d` (`✓ std3`).

*Citation.* Matteo Beccaria; Christian Hagendorf (2012). *A staggered fermion chain with supersymmetry on open intervals*. DOI: [10.1088/1751-8113/45/36/365201](https://doi.org/10.1088/1751-8113/45/36/365201). URL: <https://arxiv.org/abs/1206.4194v2>.

*Commentary.*

Section 2.1, printed page 3: “nearest-neighbour exclusion: at most one of two adjacent sites may be occupied.” “We shall work with free boundary conditions what is equivalent to add two inaccessible but empty sites at j = 0 and j = N + 1.” The operators use the supercharge, projectors and Hamiltonian of that section. The displayed equation defines d.

**Definition 1.10 (periodThree).**

$$\forall a \in \mathit{Real},\; \forall b \in \mathit{Real},\; \forall cc \in \mathit{Real},\; \forall j \in \mathit{Nat},\; \mathrm{asReal}\left(\mathrm{periodThree}\left(a, b, \mathit{cc}, j\right)\right) = \mathrm{ite}\left(\mathrm{mod}\left(j, 3\right) = 1, a, \mathrm{ite}\left(\mathrm{mod}\left(j, 3\right) = 2, b, \mathit{cc}\right)\right)$$

*Formalization.* `D5/S3/Quantum/SpinChains/SupersymmetricFermion/HardCoreModel.periodThree` (`✓ std3`).

*Citation.* Matteo Beccaria; Christian Hagendorf (2012). *A staggered fermion chain with supersymmetry on open intervals*. DOI: [10.1088/1751-8113/45/36/365201](https://doi.org/10.1088/1751-8113/45/36/365201). URL: <https://arxiv.org/abs/1206.4194v2>.

*Commentary.*

Section 2.1, printed page 3: “nearest-neighbour exclusion: at most one of two adjacent sites may be occupied.” “We shall work with free boundary conditions what is equivalent to add two inaccessible but empty sites at j = 0 and j = N + 1.” The operators use the supercharge, projectors and Hamiltonian of that section. The displayed equation defines periodThree.

**Definition 1.11 (stagII).**

$$\forall y \in \mathit{Real},\; (\mathrm{stagII}\left(y\right):\mathit{Nat} \to \mathit{Real}) = \mathrm{periodThree}\left(y, y, 1\right)$$

*Formalization.* `D5/S3/Quantum/SpinChains/SupersymmetricFermion/HardCoreModel.stagII` (`✓ std3`).

*Citation.* Matteo Beccaria; Christian Hagendorf (2012). *A staggered fermion chain with supersymmetry on open intervals*. DOI: [10.1088/1751-8113/45/36/365201](https://doi.org/10.1088/1751-8113/45/36/365201). URL: <https://arxiv.org/abs/1206.4194v2>.

*Commentary.*

Section 2.1, printed page 3: “nearest-neighbour exclusion: at most one of two adjacent sites may be occupied.” “We shall work with free boundary conditions what is equivalent to add two inaccessible but empty sites at j = 0 and j = N + 1.” The operators use the supercharge, projectors and Hamiltonian of that section. The displayed equation defines stagII.

**Definition 1.12 (Qmat).**

$$\forall N \in \mathit{Nat},\; \forall coupling \in \mathit{Nat} \to \mathit{Real},\; (\mathrm{Qmat}\left(N, \mathit{coupling}\right):\mathrm{Operator}\left(N\right)) = \sum_{j\in\mathrm{Finsetrange}\left(N\right)}(\mathrm{smul}\left((\mathit{coupling}\left((j) + (1)\right):\mathit{Complex}), \mathrm{d}\left((j) + (1)\right)\right))$$

*Formalization.* `D5/S3/Quantum/SpinChains/SupersymmetricFermion/HardCoreModel.Qmat` (`✓ std3`).

*Citation.* Matteo Beccaria; Christian Hagendorf (2012). *A staggered fermion chain with supersymmetry on open intervals*. DOI: [10.1088/1751-8113/45/36/365201](https://doi.org/10.1088/1751-8113/45/36/365201). URL: <https://arxiv.org/abs/1206.4194v2>.

*Commentary.*

Section 2.1, printed page 3: “nearest-neighbour exclusion: at most one of two adjacent sites may be occupied.” “We shall work with free boundary conditions what is equivalent to add two inaccessible but empty sites at j = 0 and j = N + 1.” The operators use the supercharge, projectors and Hamiltonian of that section. The displayed equation defines Qmat.

**Definition 1.13 (Q).**

$$\forall N \in \mathit{Nat},\; \forall coupling \in \mathit{Nat} \to \mathit{Real},\; (\mathrm{Q}\left(N, \mathit{coupling}\right):\mathrm{LinearMap}\left(\mathit{Complex}, \mathrm{HardCoreSpace}\left(N\right), \mathrm{HardCoreSpace}\left(N\right)\right)) = \mathrm{MatrixtoEuclideanLin}\left(\mathrm{Qmat}\left(N, \mathit{coupling}\right)\right)$$

*Formalization.* `D5/S3/Quantum/SpinChains/SupersymmetricFermion/HardCoreModel.Q` (`✓ std3`).

*Citation.* Matteo Beccaria; Christian Hagendorf (2012). *A staggered fermion chain with supersymmetry on open intervals*. DOI: [10.1088/1751-8113/45/36/365201](https://doi.org/10.1088/1751-8113/45/36/365201). URL: <https://arxiv.org/abs/1206.4194v2>.

*Commentary.*

Section 2.1, printed page 3: “nearest-neighbour exclusion: at most one of two adjacent sites may be occupied.” “We shall work with free boundary conditions what is equivalent to add two inaccessible but empty sites at j = 0 and j = N + 1.” The operators use the supercharge, projectors and Hamiltonian of that section. The displayed equation defines Q.

**Definition 1.14 (H).**

$$\forall N \in \mathit{Nat},\; \forall coupling \in \mathit{Nat} \to \mathit{Real},\; (\mathrm{H}\left(N, \mathit{coupling}\right):\mathrm{LinearMap}\left(\mathit{Complex}, \mathrm{HardCoreSpace}\left(N\right), \mathrm{HardCoreSpace}\left(N\right)\right)) = ((\mathrm{Q}\left(N, \mathit{coupling}\right)) \cdot (\mathrm{adjoint}\left(\mathrm{Q}\left(N, \mathit{coupling}\right)\right))) + ((\mathrm{adjoint}\left(\mathrm{Q}\left(N, \mathit{coupling}\right)\right)) \cdot (\mathrm{Q}\left(N, \mathit{coupling}\right)))$$

*Formalization.* `D5/S3/Quantum/SpinChains/SupersymmetricFermion/HardCoreModel.H` (`✓ std3`).

*Citation.* Matteo Beccaria; Christian Hagendorf (2012). *A staggered fermion chain with supersymmetry on open intervals*. DOI: [10.1088/1751-8113/45/36/365201](https://doi.org/10.1088/1751-8113/45/36/365201). URL: <https://arxiv.org/abs/1206.4194v2>.

*Commentary.*

Section 2.1, printed page 3: “nearest-neighbour exclusion: at most one of two adjacent sites may be occupied.” “We shall work with free boundary conditions what is equivalent to add two inaccessible but empty sites at j = 0 and j = N + 1.” The operators use the supercharge, projectors and Hamiltonian of that section. The displayed equation defines H.

**Definition 1.15 (density).**

$$\forall N \in \mathit{Nat},\; \forall j \in \mathit{Nat},\; \forall psi \in \mathrm{HardCoreSpace}\left(N\right),\; (\mathrm{density}\left(N, j, \mathit{psi}\right):\mathit{Complex}) = \mathrm{div}\left(\mathrm{inner}\left(\mathit{Complex}, \mathit{psi}, \mathrm{MatrixtoEuclideanLin}\left(\mathrm{number}\left(j\right), \mathit{psi}\right)\right), \mathrm{inner}\left(\mathit{Complex}, \mathit{psi}, \mathit{psi}\right)\right)$$

*Formalization.* `D5/S3/Quantum/SpinChains/SupersymmetricFermion/HardCoreModel.density` (`✓ std3`).

*Citation.* Matteo Beccaria; Christian Hagendorf (2012). *A staggered fermion chain with supersymmetry on open intervals*. DOI: [10.1088/1751-8113/45/36/365201](https://doi.org/10.1088/1751-8113/45/36/365201). URL: <https://arxiv.org/abs/1206.4194v2>.

*Commentary.*

Section 2.1, printed page 3: “nearest-neighbour exclusion: at most one of two adjacent sites may be occupied.” “We shall work with free boundary conditions what is equivalent to add two inaccessible but empty sites at j = 0 and j = N + 1.” The operators use the supercharge, projectors and Hamiltonian of that section. The displayed equation defines density.

**Definition 1.16 (Rmat).**

$$\forall N \in \mathit{Nat},\; \forall a \in \mathit{Real},\; \forall b \in \mathit{Real},\; \forall cc \in \mathit{Real},\; (\mathrm{Rmat}\left(N, a, b, \mathit{cc}\right):\mathrm{Operator}\left(N\right)) = ((((\mathrm{smul}\left(\mathrm{asReal}\left((a) \cdot ((\mathit{cc})^{2})\right), \mathrm{adjoint}\left(\mathrm{d}\left(1\right)\right)\right)) - (\mathrm{smul}\left(\mathrm{asReal}\left(((a)^{2}) \cdot (\mathit{cc})\right), \mathrm{adjoint}\left(\mathrm{d}\left(N\right)\right)\right))) + (\sum_{k\in\mathrm{Finsetrange}\left((N) - (2)\right)}((j\mapsto(\mathrm{smul}\left(\mathrm{asReal}\left((\mathrm{periodThree}\left(a, b, \mathit{cc}, j\right)) \cdot ((\mathrm{periodThree}\left(a, b, \mathit{cc}, (j) - (1)\right))^{2})\right), (\mathrm{number}\left((j) - (2)\right)) \cdot (\mathrm{adjoint}\left(\mathrm{d}\left(j\right)\right))\right)))\left((k) + (3)\right)))) - (\sum_{k\in\mathrm{Finsetrange}\left((N) - (2)\right)}((j\mapsto(\mathrm{smul}\left(\mathrm{asReal}\left((\mathrm{periodThree}\left(a, b, \mathit{cc}, j\right)) \cdot ((\mathrm{periodThree}\left(a, b, \mathit{cc}, (j) + (1)\right))^{2})\right), (\mathrm{number}\left((j) + (2)\right)) \cdot (\mathrm{adjoint}\left(\mathrm{d}\left(j\right)\right))\right)))\left((k) + (1)\right)))) + (\mathrm{smul}\left(\mathrm{asReal}\left(((a) \cdot (b)) \cdot (\mathit{cc})\right), \sum_{k\in\mathrm{Finsetrange}\left((N) - (2)\right)}((j\mapsto(((((\mathrm{P}\left((j) - (1)\right)) \cdot (\mathrm{adjoint}\left(\mathrm{c}\left(j\right)\right))) \cdot (\mathrm{adjoint}\left(\mathrm{c}\left((j) + (2)\right)\right))) \cdot (\mathrm{c}\left((j) + (1)\right))) \cdot (\mathrm{P}\left((j) + (3)\right))))\left((k) + (1)\right))\right))$$

*Formalization.* `D5/S3/Quantum/SpinChains/SupersymmetricFermion/HardCoreModel.Rmat` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed equation defines Rmat.

**Theorem 1.17 (Occupation from fermion annihilation).**

$$\forall N \in \mathit{Nat},\; \forall j \in \mathit{Nat},\; (\mathrm{adjoint}\left(\mathrm{c}\left(N, j\right)\right)) \cdot (\mathrm{c}\left(N, j\right)) = \mathrm{number}\left(N, j\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/SpinChains/SupersymmetricFermion/HardCoreModel.annihilator_number` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The product c(j)†c(j) is the occupation diagonal, including the zero operator outside the chain. Erasing an occupied site preserves nearest-neighbour exclusion. Erasure is injective on configurations with that site occupied, and the Jordan-Wigner signs cancel between the adjoint and annihilator. Hence the projector P(j) equals 1 minus the fermion number c(j)†c(j) used in the source model.

## References

- Truth anchor: `D5/S3/Quantum/SpinChains/SupersymmetricFermion/HardCoreModel.H`
- Truth anchor: `D5/S3/Quantum/SpinChains/SupersymmetricFermion/HardCoreModel.HardCore`
- Truth anchor: `D5/S3/Quantum/SpinChains/SupersymmetricFermion/HardCoreModel.HardCoreSpace`
- Truth anchor: `D5/S3/Quantum/SpinChains/SupersymmetricFermion/HardCoreModel.Operator`
- Truth anchor: `D5/S3/Quantum/SpinChains/SupersymmetricFermion/HardCoreModel.P`
- Truth anchor: `D5/S3/Quantum/SpinChains/SupersymmetricFermion/HardCoreModel.Q`
- Truth anchor: `D5/S3/Quantum/SpinChains/SupersymmetricFermion/HardCoreModel.Qmat`
- Truth anchor: `D5/S3/Quantum/SpinChains/SupersymmetricFermion/HardCoreModel.Rmat`
- Truth anchor: `D5/S3/Quantum/SpinChains/SupersymmetricFermion/HardCoreModel.annihilationAt`
- Truth anchor: `D5/S3/Quantum/SpinChains/SupersymmetricFermion/HardCoreModel.annihilator_number`
- Truth anchor: `D5/S3/Quantum/SpinChains/SupersymmetricFermion/HardCoreModel.c`
- Truth anchor: `D5/S3/Quantum/SpinChains/SupersymmetricFermion/HardCoreModel.d`
- Truth anchor: `D5/S3/Quantum/SpinChains/SupersymmetricFermion/HardCoreModel.density`
- Truth anchor: `D5/S3/Quantum/SpinChains/SupersymmetricFermion/HardCoreModel.number`
- Truth anchor: `D5/S3/Quantum/SpinChains/SupersymmetricFermion/HardCoreModel.occupied`
- Truth anchor: `D5/S3/Quantum/SpinChains/SupersymmetricFermion/HardCoreModel.periodThree`
- Truth anchor: `D5/S3/Quantum/SpinChains/SupersymmetricFermion/HardCoreModel.stagII`
- Dependency: [D5/S1/Words/AdmissibleWords/AdmissibleCount](../../../../S1/Words/AdmissibleWords/AdmissibleCount.md)
- Dependency: [D5/S3/Quantum/FockSpace/ForbiddenNeighbourDeterminant](../../FockSpace/ForbiddenNeighbourDeterminant.md)
- Dependency: [D5/S3/Quantum/SpinChains/SupersymmetricFermion/JordanWigner](JordanWigner.md)
