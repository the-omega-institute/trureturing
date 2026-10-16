# Two negative eigenvalues in a Hildebrand matrix

## Abstract

An admissible Hildebrand matrix for a four-by-four bipartite spectrum has at least two negative eigenvalues.

Fin(d) consists of the indices 0 through d − 1. Increments denotes D5.S3.Arith.Lattices.Klartag.Walk.Increments. Its type Increments.UT(d) is the upper triangle {(i,j) : Fin(d) × Fin(d) | i ≤ j}. NikolovSegal.SLnRootAction.PositiveIndex(d) is the strict upper triangle {(i,j) : Fin(d) × Fin(d) | i < j}. Subtype.val forgets the inequality, and Subtype.property supplies it; Prod.fst and Prod.snd select the coordinates. Equiv(S,T) is the type of bijections from S to T. Fintype.card is finite cardinality. Fin.castLE(r) denotes the value-preserving inclusion into the displayed target Fin type, with its inequality proof suppressed. Fin.rev reverses the target order. Matrix.conjTranspose is conjugate transpose. RHLinalg.negIndex takes Hermitian evidence and counts the strictly negative eigenvalues with multiplicity.

**Definition 1.1 (Ordering the upper triangle).**

$$\forall d \in \mathit{Nat},\; \operatorname{\mathit{PlusOrdering}}\left(d\right) = \operatorname{\mathit{Equiv}}\left(\operatorname{\mathit{Increments}}.\operatorname{\mathit{UT}}\left(d\right), \operatorname{\mathit{Fin}}\left(\operatorname{\mathit{Fintype}}.\operatorname{\mathit{card}}\left(\operatorname{\mathit{Increments}}.\operatorname{\mathit{UT}}\left(d\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/HildebrandNegativeIndexRefutation.PlusOrdering` (`✓ std3`).

*Citation.* Roland Hildebrand (2007). *Positive partial transpose from spectra*. DOI: [10.1103/PhysRevA.76.052325](https://doi.org/10.1103/PhysRevA.76.052325). URL: <https://arxiv.org/abs/quant-ph/0502170>.

*Commentary.*

An ordering assigns each pair i ≤ j a distinct zero-based rank. There are d(d + 1)/2 pairs, including the diagonal. Adding one to every rank gives Hildebrand's ordering of S₊ onto {1,…,d(d + 1)/2}.

**Definition 1.2 (Ordering the strict upper triangle).**

$$\forall d \in \mathit{Nat},\; \operatorname{\mathit{MinusOrdering}}\left(d\right) = \operatorname{\mathit{Equiv}}\left(\operatorname{\mathit{NikolovSegal}}.\operatorname{\mathit{SLnRootAction}}.\operatorname{\mathit{PositiveIndex}}\left(d\right), \operatorname{\mathit{Fin}}\left(\operatorname{\mathit{Fintype}}.\operatorname{\mathit{card}}\left(\operatorname{\mathit{NikolovSegal}}.\operatorname{\mathit{SLnRootAction}}.\operatorname{\mathit{PositiveIndex}}\left(d\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/HildebrandNegativeIndexRefutation.MinusOrdering` (`✓ std3`).

*Citation.* Roland Hildebrand (2007). *Positive partial transpose from spectra*. DOI: [10.1103/PhysRevA.76.052325](https://doi.org/10.1103/PhysRevA.76.052325). URL: <https://arxiv.org/abs/quant-ph/0502170>.

*Commentary.*

An ordering assigns each pair i < j a distinct zero-based rank. There are d(d − 1)/2 pairs. Adding one to each rank gives Hildebrand's ordering of S₋.

**Definition 1.3 (Including the strict upper triangle).**

$$\forall d \in \mathit{Nat},\; \forall p \in \operatorname{\mathit{NikolovSegal}}.\operatorname{\mathit{SLnRootAction}}.\operatorname{\mathit{PositiveIndex}}\left(d\right),\; (\operatorname{\mathit{minusToPlus}}\left(p\right):\operatorname{\mathit{Increments}}.\operatorname{\mathit{UT}}\left(d\right)) = \operatorname{\mathit{Subtype}}.\operatorname{\mathit{mk}}\left(\operatorname{\mathit{Subtype}}.\operatorname{\mathit{val}}\left(p\right), \operatorname{\mathit{le}_{\mathit{of}_{\mathit{lt}}}}\left(\operatorname{\mathit{Subtype}}.\operatorname{\mathit{property}}\left(p\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/HildebrandNegativeIndexRefutation.minusToPlus` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Roland Hildebrand (2007). *Positive partial transpose from spectra*. DOI: [10.1103/PhysRevA.76.052325](https://doi.org/10.1103/PhysRevA.76.052325). URL: <https://arxiv.org/abs/quant-ph/0502170>.

*Commentary.*

The inclusion retains the coordinate pair and uses i < j to obtain i ≤ j. It lets the plus ordering act on the pairs of S₋.

**Definition 1.4 (Compatibility of the two orderings).**

$$\forall d \in \mathit{Nat},\; \forall sigmaP \in \operatorname{\mathit{PlusOrdering}}\left(d\right),\; \forall sigmaM \in \operatorname{\mathit{MinusOrdering}}\left(d\right),\; \forall x \in \operatorname{\mathit{Fin}}\left(d\right) \to \mathit{Real},\; (\operatorname{\mathit{Compatible}}\left(\mathit{sigmaP}, \mathit{sigmaM}, x\right)) \Leftrightarrow ((\forall p \in \operatorname{\mathit{Increments}}.\operatorname{\mathit{UT}}\left(d\right),\; \forall q \in \operatorname{\mathit{Increments}}.\operatorname{\mathit{UT}}\left(d\right),\; (\mathit{sigmaP}\left(p\right) < \mathit{sigmaP}\left(q\right)) \Rightarrow (x\left(\operatorname{\mathit{Prod}}.\operatorname{\mathit{fst}}\left(\operatorname{\mathit{Subtype}}.\operatorname{\mathit{val}}\left(q\right)\right)\right) \cdot x\left(\operatorname{\mathit{Prod}}.\operatorname{\mathit{snd}}\left(\operatorname{\mathit{Subtype}}.\operatorname{\mathit{val}}\left(q\right)\right)\right) \le x\left(\operatorname{\mathit{Prod}}.\operatorname{\mathit{fst}}\left(\operatorname{\mathit{Subtype}}.\operatorname{\mathit{val}}\left(p\right)\right)\right) \cdot x\left(\operatorname{\mathit{Prod}}.\operatorname{\mathit{snd}}\left(\operatorname{\mathit{Subtype}}.\operatorname{\mathit{val}}\left(p\right)\right)\right))) \land (\forall p \in \operatorname{\mathit{NikolovSegal}}.\operatorname{\mathit{SLnRootAction}}.\operatorname{\mathit{PositiveIndex}}\left(d\right),\; \forall q \in \operatorname{\mathit{NikolovSegal}}.\operatorname{\mathit{SLnRootAction}}.\operatorname{\mathit{PositiveIndex}}\left(d\right),\; (\mathit{sigmaP}\left(\operatorname{\mathit{minusToPlus}}\left(p\right)\right) < \mathit{sigmaP}\left(\operatorname{\mathit{minusToPlus}}\left(q\right)\right)) \Rightarrow (\mathit{sigmaM}\left(p\right) < \mathit{sigmaM}\left(q\right))))$$

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/HildebrandNegativeIndexRefutation.Compatible` (`✓ std3`).

*Citation.* Roland Hildebrand (2007). *Positive partial transpose from spectra*. DOI: [10.1103/PhysRevA.76.052325](https://doi.org/10.1103/PhysRevA.76.052325). URL: <https://arxiv.org/abs/quant-ph/0502170>.

*Commentary.*

Hildebrand's Definition 1 requires the products xᵢxⱼ to decrease weakly as the plus rank increases. On the strict upper triangle, the minus ordering must respect the plus ordering. Ties among products are allowed. This predicate is defined for every real vector x; strict decrease and positivity of x enter the next definition.

**Definition 1.5 (The set of admissible pairs Σ±).**

$$\forall d \in \mathit{Nat},\; \forall sigmaP \in \operatorname{\mathit{PlusOrdering}}\left(d\right),\; \forall sigmaM \in \operatorname{\mathit{MinusOrdering}}\left(d\right),\; (\operatorname{\mathit{Admissible}}\left(\mathit{sigmaP}, \mathit{sigmaM}\right)) \Leftrightarrow (\exists x \in \operatorname{\mathit{Fin}}\left(d\right) \to \mathit{Real},\; (\operatorname{\mathit{StrictAnti}}\left(x\right)) \land ((\forall i \in \operatorname{\mathit{Fin}}\left(d\right),\; 0 < x\left(i\right)) \land (\operatorname{\mathit{Compatible}}\left(\mathit{sigmaP}, \mathit{sigmaM}, x\right))))$$

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/HildebrandNegativeIndexRefutation.Admissible` (`✓ std3`).

*Citation.* Roland Hildebrand (2007). *Positive partial transpose from spectra*. DOI: [10.1103/PhysRevA.76.052325](https://doi.org/10.1103/PhysRevA.76.052325). URL: <https://arxiv.org/abs/quant-ph/0502170>.

*Commentary.*

A pair belongs to Hildebrand's Σ± exactly when it is compatible with some strictly decreasing positive vector. StrictAnti(x) means xⱼ < xᵢ whenever i < j. The existential condition includes every compatible ordering arising from such a vector.

**Definition 1.6 (Reversing a plus rank in the spectrum).**

$$\forall d \in \mathit{Nat},\; \forall r \in \operatorname{\mathit{Fin}}\left(\operatorname{\mathit{Fintype}}.\operatorname{\mathit{card}}\left(\operatorname{\mathit{Increments}}.\operatorname{\mathit{UT}}\left(d\right)\right)\right),\; (\operatorname{\mathit{plusIndex}}\left(r\right):\operatorname{\mathit{Fin}}\left(d \cdot d\right)) = \operatorname{\mathit{Fin}}.\operatorname{\mathit{rev}}\left((\operatorname{\mathit{Fin}}.\operatorname{\mathit{castLE}}\left(r\right):\operatorname{\mathit{Fin}}\left(d \cdot d\right))\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/HildebrandNegativeIndexRefutation.plusIndex` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Roland Hildebrand (2007). *Positive partial transpose from spectra*. DOI: [10.1103/PhysRevA.76.052325](https://doi.org/10.1103/PhysRevA.76.052325). URL: <https://arxiv.org/abs/quant-ph/0502170>.

*Commentary.*

The plus rank r is included in Fin(d²) and then reversed, so its spectrum index has value d² − 1 − r. If the one-based rank is σ₊ = r + 1, this is the source entry λ_{d²+1−σ₊}. The inclusion exists because the upper triangle is a subset of Fin(d) × Fin(d).

**Definition 1.7 (Including a minus rank in the spectrum).**

$$\forall d \in \mathit{Nat},\; \forall r \in \operatorname{\mathit{Fin}}\left(\operatorname{\mathit{Fintype}}.\operatorname{\mathit{card}}\left(\operatorname{\mathit{NikolovSegal}}.\operatorname{\mathit{SLnRootAction}}.\operatorname{\mathit{PositiveIndex}}\left(d\right)\right)\right),\; (\operatorname{\mathit{minusIndex}}\left(r\right):\operatorname{\mathit{Fin}}\left(d \cdot d\right)) = (\operatorname{\mathit{Fin}}.\operatorname{\mathit{castLE}}\left(r\right):\operatorname{\mathit{Fin}}\left(d \cdot d\right))$$

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/HildebrandNegativeIndexRefutation.minusIndex` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Roland Hildebrand (2007). *Positive partial transpose from spectra*. DOI: [10.1103/PhysRevA.76.052325](https://doi.org/10.1103/PhysRevA.76.052325). URL: <https://arxiv.org/abs/quant-ph/0502170>.

*Commentary.*

The minus rank keeps its value when included in Fin(d²). For the one-based rank σ₋ = r + 1, the corresponding source entry is λ_{σ₋}. The strict upper triangle is a subset of Fin(d) × Fin(d), giving the required cardinality bound.

**Definition 1.8 (The signed spectral array Λ).**

$$\forall d \in \mathit{Nat},\; \forall lam \in \operatorname{\mathit{Fin}}\left(d \cdot d\right) \to \mathit{Real},\; \forall sigmaP \in \operatorname{\mathit{PlusOrdering}}\left(d\right),\; \forall sigmaM \in \operatorname{\mathit{MinusOrdering}}\left(d\right),\; (\operatorname{\mathit{hildebrandArray}}\left(d, \mathit{lam}, \mathit{sigmaP}, \mathit{sigmaM}\right):\operatorname{\mathit{Matrix}}\left(\operatorname{\mathit{Fin}}\left(d\right), \operatorname{\mathit{Fin}}\left(d\right), \mathit{Complex}\right)) = \lambda (i:\operatorname{\mathit{Fin}}\left(d\right)) \mapsto (\lambda (j:\operatorname{\mathit{Fin}}\left(d\right)) \mapsto (\operatorname{\mathit{if}} (\mathit{hij}:i \le j) \operatorname{\mathit{then}} (\mathit{lam}\left(\operatorname{\mathit{plusIndex}}\left(\mathit{sigmaP}\left(\operatorname{\mathit{Subtype}}.\operatorname{\mathit{mk}}\left((i,j), \mathit{hij}\right)\right)\right)\right):\mathit{Complex}) \operatorname{\mathit{else}} -(\mathit{lam}\left(\operatorname{\mathit{minusIndex}}\left(\mathit{sigmaM}\left(\operatorname{\mathit{Subtype}}.\operatorname{\mathit{mk}}\left((j,i), \operatorname{\mathit{lt}_{\mathit{of}_{\mathit{not}_{\mathit{ge}}}}}\left(\mathit{hij}\right)\right)\right)\right)\right):\mathit{Complex})))$$

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/HildebrandNegativeIndexRefutation.hildebrandArray` (`✓ std3`).

*Citation.* Roland Hildebrand (2007). *Positive partial transpose from spectra*. DOI: [10.1103/PhysRevA.76.052325](https://doi.org/10.1103/PhysRevA.76.052325). URL: <https://arxiv.org/abs/quant-ph/0502170>.

*Commentary.*

The upper triangle, including the diagonal, contains the smallest eigenvalues in the reversed plus order. The lower triangle contains the negatives of the largest eigenvalues in the minus order, with the pair transposed to lie in S₋. All entries are real numbers viewed in the complex field. This is Hildebrand's array Λ in equation (2).

**Definition 1.9 (The Hermitian matrix Λ + Λᴴ).**

$$\forall d \in \mathit{Nat},\; \forall lam \in \operatorname{\mathit{Fin}}\left(d \cdot d\right) \to \mathit{Real},\; \forall sigmaP \in \operatorname{\mathit{PlusOrdering}}\left(d\right),\; \forall sigmaM \in \operatorname{\mathit{MinusOrdering}}\left(d\right),\; (\operatorname{\mathit{hildebrandMatrix}}\left(d, \mathit{lam}, \mathit{sigmaP}, \mathit{sigmaM}\right):\operatorname{\mathit{Matrix}}\left(\operatorname{\mathit{Fin}}\left(d\right), \operatorname{\mathit{Fin}}\left(d\right), \mathit{Complex}\right)) = \operatorname{\mathit{hildebrandArray}}\left(d, \mathit{lam}, \mathit{sigmaP}, \mathit{sigmaM}\right) + \operatorname{\mathit{Matrix}}.\operatorname{\mathit{conjTranspose}}\left(\operatorname{\mathit{hildebrandArray}}\left(d, \mathit{lam}, \mathit{sigmaP}, \mathit{sigmaM}\right)\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/HildebrandNegativeIndexRefutation.hildebrandMatrix` (`✓ std3`).

*Citation.* Roland Hildebrand (2007). *Positive partial transpose from spectra*. DOI: [10.1103/PhysRevA.76.052325](https://doi.org/10.1103/PhysRevA.76.052325). URL: <https://arxiv.org/abs/quant-ph/0502170>.

*Commentary.*

Adding the conjugate transpose gives the matrix of the spectral inequality. Because Λ has real entries, Λᴴ equals Λᵀ, so this is the real symmetric matrix Λ + Λᵀ from Hildebrand's criterion.

**Theorem 1.10 (Hermitian symmetry).**

$$\forall d \in \mathit{Nat},\; \forall lam \in \operatorname{\mathit{Fin}}\left(d \cdot d\right) \to \mathit{Real},\; \forall sigmaP \in \operatorname{\mathit{PlusOrdering}}\left(d\right),\; \forall sigmaM \in \operatorname{\mathit{MinusOrdering}}\left(d\right),\; \operatorname{\mathit{Matrix}}.\operatorname{\mathit{IsHermitian}}\left(\operatorname{\mathit{hildebrandMatrix}}\left(d, \mathit{lam}, \mathit{sigmaP}, \mathit{sigmaM}\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/HildebrandNegativeIndexRefutation.hildebrandMatrix_isHermitian` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Roland Hildebrand (2007). *Positive partial transpose from spectra*. DOI: [10.1103/PhysRevA.76.052325](https://doi.org/10.1103/PhysRevA.76.052325). URL: <https://arxiv.org/abs/quant-ph/0502170>.

*Commentary.*

The conjugate transpose of A + Aᴴ is A + Aᴴ. Thus the spectral matrix is Hermitian for every real list and every pair of orderings. Its eigenvalues are real, so its negative index is defined.

**Definition 1.11 (An ordered normalized spectrum).**

$$\forall d \in \mathit{Nat},\; \forall lam \in \operatorname{\mathit{Fin}}\left(d \cdot d\right) \to \mathit{Real},\; (\operatorname{\mathit{OrderedSpectrum}}\left(d, \mathit{lam}\right)) \Leftrightarrow ((\operatorname{\mathit{Antitone}}\left(\mathit{lam}\right)) \land ((\forall i \in \operatorname{\mathit{Fin}}\left(d \cdot d\right),\; 0 \le \mathit{lam}\left(i\right)) \land (\sum_{i:\operatorname{\mathit{Fin}}\left(d \cdot d\right)}(\mathit{lam}\left(i\right)) = 1)))$$

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/HildebrandNegativeIndexRefutation.OrderedSpectrum` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Matthew Chen; Natalie Klco (2026). *Susceptibility of qudit-qudit entanglement to quantum noise: insights from the negativity rank*. URL: <https://arxiv.org/abs/2610.10820v1>.

*Commentary.*

The d² real entries decrease weakly, are nonnegative, and sum to one. These are precisely the conditions on an ordered list of eigenvalues of a density matrix.

**Definition 1.12 (The proposed persistence of negative index at most one).**

$$(\mathit{claim}) \Leftrightarrow (\forall d \in \mathit{Nat},\; (3 < d) \Rightarrow (\forall lam \in \operatorname{\mathit{Fin}}\left(d \cdot d\right) \to \mathit{Real},\; (\operatorname{\mathit{OrderedSpectrum}}\left(d, \mathit{lam}\right)) \Rightarrow (\forall sigmaP \in \operatorname{\mathit{PlusOrdering}}\left(d\right),\; \forall sigmaM \in \operatorname{\mathit{MinusOrdering}}\left(d\right),\; (\operatorname{\mathit{Admissible}}\left(\mathit{sigmaP}, \mathit{sigmaM}\right)) \Rightarrow (\operatorname{\mathit{RHLinalg}}.\operatorname{\mathit{negIndex}}\left(\operatorname{\mathit{hildebrandMatrix}_{\mathit{isHermitian}}}\left(d, \mathit{lam}, \mathit{sigmaP}, \mathit{sigmaM}\right)\right) \le 1))))$$

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/HildebrandNegativeIndexRefutation.claim` (`✓ std3`).

*Citation.* Matthew Chen; Natalie Klco (2026). *Susceptibility of qudit-qudit entanglement to quantum noise: insights from the negativity rank*. URL: <https://arxiv.org/abs/2610.10820v1>.

*Commentary.*

Theorem II.1 of Chen and Klco identifies the two qutrit matrices in equation (5), and Theorem II.2 bounds each negative index by one for every ordered qutrit spectrum. Section V asks whether this bound persists for the corresponding inequalities when d > 3. The statement here expresses that proposed extension for every dimension d > 3, every ordered normalized spectrum, and every pair in Hildebrand's Σ±. The count includes multiplicity. A real orthogonal diagonalization is also a complex unitary diagonalization of this same real matrix, so using complex entries preserves the eigenvalue list.

**Theorem 1.13 (A four-dimensional counterexample).**

$$\neg (\mathit{claim})$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/HildebrandNegativeIndexRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/chen-klco-2026-hildebrand-negative-index-persistence` (refuted) by `D5/S3/Quantum/Entanglement/AbsolutePPT/HildebrandNegativeIndexRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"chen-klco-2026-hildebrand-negative-index-persistence","declaration_gid":"D5/S3/Quantum/Entanglement/AbsolutePPT/HildebrandNegativeIndexRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Matthew Chen; Natalie Klco (2026). *Susceptibility of qudit-qudit entanglement to quantum noise: insights from the negativity rank*. URL: <https://arxiv.org/abs/2610.10820v1>.

*Commentary.*

Take d = 4 and λ = (13,13,13,13,1,1,1,1,1,1,1,1,1,1,1,1)/64. The entries are nonnegative and decreasing, and their sum is (4·13 + 12)/64 = 1. For x = (8,5,3,1), the upper-triangle pairs in increasing plus rank are (0,0), (0,1), (1,1), (0,2), (1,2), (2,2), (0,3), (1,3), (2,3), (3,3). Their products are 64,40,25,24,15,9,8,5,3,1. The strict upper-triangle pairs in increasing minus rank are (0,1), (0,2), (1,2), (0,3), (1,3), (2,3). Both rank lists start at zero. The vector is strictly decreasing and positive, so these compatible orderings belong to Σ±.

For these data, write L for the Hildebrand matrix. Then L = M/32, where M = [[1,−6,−6,−6], [−6,1,−6,0], [−6,−6,1,0], [−6,0,0,1]]. Let B = [[1,0], [0,1], [0,1], [1,−2]]. Direct multiplication gives BᴴLB = −(1/16)[[5,1], [1,3]]. The matrix (1/16)[[5,1], [1,3]] is positive definite: it equals diag(1/4,1/8) + VᴴV, where V = [[1/4,1/4]]. Its negative therefore has two strictly negative eigenvalues. A compression BᴴLB cannot have more negative eigenvalues than L, so L has at least two. This contradicts the asserted bound of one.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/HildebrandNegativeIndexRefutation.Admissible`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/HildebrandNegativeIndexRefutation.Compatible`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/HildebrandNegativeIndexRefutation.MinusOrdering`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/HildebrandNegativeIndexRefutation.OrderedSpectrum`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/HildebrandNegativeIndexRefutation.PlusOrdering`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/HildebrandNegativeIndexRefutation.claim`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/HildebrandNegativeIndexRefutation.hildebrandArray`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/HildebrandNegativeIndexRefutation.hildebrandMatrix`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/HildebrandNegativeIndexRefutation.hildebrandMatrix_isHermitian`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/HildebrandNegativeIndexRefutation.minusIndex`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/HildebrandNegativeIndexRefutation.minusToPlus`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/HildebrandNegativeIndexRefutation.plusIndex`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/HildebrandNegativeIndexRefutation.result`
- Dependency: [D5/S3/Analytic/ReflectedSpectrum/ConfluentNegativeJetBlock](../../../Analytic/ReflectedSpectrum/ConfluentNegativeJetBlock.md)
- Dependency: [D5/S3/Arith/Lattices/Klartag/Walk/Increments](../../../Arith/Lattices/Klartag/Walk/Increments.md)
- Dependency: [D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIISLnRootKernels](../../../FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIISLnRootKernels.md)
- Dependency: [D5/S3/Weil/ZetaLinear/FullRankInertiaPullback](../../../Weil/ZetaLinear/FullRankInertiaPullback.md)
