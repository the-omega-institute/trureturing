# Four MUBs refute the dimension-eight necessity bound

## Abstract

Four mutually unbiased bases in dimension eight give a negative expectation on a positive-partial-transpose density matrix for the witness of Bae, Bera, Chruściński, Hiesmayr and McNulty.

**Definition 1.1 (Mutually unbiased bases).**

$$\forall d:\mathbb{N}, \forall m:\mathbb{N}, \forall U:\operatorname{Fin}\left(m\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right), \operatorname{IsMUBFamily}\left(U\right) \Leftrightarrow ((\forall alpha:\operatorname{Fin}\left(m\right), U\left(alpha\right) \in \operatorname{Matrix.unitaryGroup}\left(\operatorname{Fin}\left(d\right), \mathbb{C}\right)) \land ((\forall hm:0 < m, U\left(\operatorname{Fin.mk}\left(0, hm\right)\right) = 1) \land (\forall alpha:\operatorname{Fin}\left(m\right), \forall beta:\operatorname{Fin}\left(m\right), (alpha \neq beta) \Rightarrow (\forall i:\operatorname{Fin}\left(d\right), \forall j:\operatorname{Fin}\left(d\right), \operatorname{norm}\left(\left(\operatorname{Matrix.conjTranspose}\left(U\left(alpha\right)\right) \cdot U\left(beta\right)\right)\left(i, j\right)\right)^{2} = \frac{1}{(\operatorname{val}\left(d\right):\mathbb{R})}))))$$

*Formalization.* `D5/S3/Quantum/Entanglement/FourMUBBoundEntanglementRefutation.IsMUBFamily` (`✓ std3`).

*Citation.* J. Bae; A. Bera; D. Chruściński; B. C. Hiesmayr; D. McNulty (2022). *How many mutually unbiased bases are needed to detect bound entangled states?*. DOI: [10.1088/1751-8121/acaa16](https://doi.org/10.1088/1751-8121/acaa16). URL: <https://arxiv.org/abs/2108.01109>.

*Commentary.*

Section I, p. 2: 'Generalising to larger collections of measurements, we say a set of bases is mutually unbiased if all bases are pairwise unbiased.' Columns are basis vectors. Each basis matrix is unitary, basis zero is the identity whenever the family is nonempty, and the squared norm of every overlap between distinct bases is 1/d. The implicit natural-number parameters d and m are shown explicitly.

**Definition 1.2 (The partially transposed MUB witness).**

$$\forall d:\mathbb{N}, \forall m:\mathbb{N}, \forall U:\operatorname{Fin}\left(m\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right), \forall s:\operatorname{Fin}\left(d\right), \operatorname{witnessGamma}\left(U, s\right) = \frac{(\operatorname{val}\left(d\right):\mathbb{C}) + (\operatorname{val}\left(m\right):\mathbb{C}) - 1}{(\operatorname{val}\left(d\right):\mathbb{C})} \cdot 1 - \sum_{l:\operatorname{Fin}\left(d\right)} (\operatorname{Matrix.single}\left((l, l + s), (l, l + s), (1:\mathbb{C})\right)) - \sum_{alpha \in \operatorname{Finset.filter}\left((\operatorname{fun} alpha:\operatorname{Fin}\left(m\right) \mapsto \operatorname{val}\left(alpha\right) \neq 0), (\operatorname{Finset.univ}:\operatorname{Finset}\left(\operatorname{Fin}\left(m\right)\right))\right)} \sum_{i:\operatorname{Fin}\left(d\right)} (\operatorname{Matrix.kronecker}\left(\operatorname{Matrix.vecMulVec}\left((\operatorname{fun} x:\operatorname{Fin}\left(d\right) \mapsto U\left(alpha, x, i\right)), \operatorname{star}\left((\operatorname{fun} x:\operatorname{Fin}\left(d\right) \mapsto U\left(alpha, x, i\right))\right)\right), \operatorname{Matrix.map}\left(\operatorname{Matrix.vecMulVec}\left((\operatorname{fun} x:\operatorname{Fin}\left(d\right) \mapsto U\left(alpha, x, i\right)), \operatorname{star}\left((\operatorname{fun} x:\operatorname{Fin}\left(d\right) \mapsto U\left(alpha, x, i\right))\right)\right), (\operatorname{star}:\mathbb{C} \to \mathbb{C})\right)\right))$$

*Formalization.* `D5/S3/Quantum/Entanglement/FourMUBBoundEntanglementRefutation.witnessGamma` (`✓ std3`).

*Citation.* J. Bae; A. Bera; D. Chruściński; B. C. Hiesmayr; D. McNulty (2022). *How many mutually unbiased bases are needed to detect bound entangled states?*. DOI: [10.1088/1751-8121/acaa16](https://doi.org/10.1088/1751-8121/acaa16). URL: <https://arxiv.org/abs/2108.01109>.

*Commentary.*

Equation (4), p. 3: W(M_m, s) = ((d+m−1)/d) 𝟙 ⊗ 𝟙 − B(M_m, s). The formula displays its partial transpose: the computational term pairs l with l+s modulo d, and each nonzero basis index contributes equal-column tensor projectors with conjugation on the second factor. Matrix.vecMulVec forms each column projector. Fin addition is modulo d. The coefficient is complex scalar multiplication; val marks the natural-to-complex casts before subtraction and division.

**Definition 1.3 (Detection of a PPT density matrix).**

$$\forall d:\mathbb{N}, \forall m:\mathbb{N}, \forall U:\operatorname{Fin}\left(m\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right), \forall s:\operatorname{Fin}\left(d\right), \operatorname{DetectsBoundEntanglement}\left(U, s\right) \Leftrightarrow (\exists rho:\operatorname{Matrix}\left(\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right), \mathbb{C}\right), (\operatorname{StructuredNegativityCoincidenceRefutation.IsDensity}\left(rho\right)) \land ((\operatorname{Matrix.PosSemidef}\left(\operatorname{StructuredNegativityCoincidenceRefutation.partialTransposeB}\left(rho\right)\right)) \land (\operatorname{Complex.re}\left(\operatorname{Matrix.trace}\left(\operatorname{witnessGamma}\left(U, s\right) \cdot rho\right)\right) < 0)))$$

*Formalization.* `D5/S3/Quantum/Entanglement/FourMUBBoundEntanglementRefutation.DetectsBoundEntanglement` (`✓ std3`).

*Citation.* J. Bae; A. Bera; D. Chruściński; B. C. Hiesmayr; D. McNulty (2022). *How many mutually unbiased bases are needed to detect bound entangled states?*. DOI: [10.1088/1751-8121/acaa16](https://doi.org/10.1088/1751-8121/acaa16). URL: <https://arxiv.org/abs/2108.01109>.

*Commentary.*

A detected state is a density matrix whose partial transpose on the second subsystem is positive semidefinite and whose real witness expectation is strictly negative. IsDensity and partialTransposeB are the existing pair-indexed matrix operations in StructuredNegativityCoincidenceRefutation. The source's nonnegativity on separable states supplies the physical interpretation of a negative expectation.

**Definition 1.4 (The necessity half of Conjecture 1).**

$$claim \Leftrightarrow (\forall r:\mathbb{N}, (2 \le r) \Rightarrow (\forall m:\mathbb{N}, (m < 2^{(r - 1)} + 1) \Rightarrow (\forall U:\operatorname{Fin}\left(m\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(2^{r}\right), \operatorname{Fin}\left(2^{r}\right), \mathbb{C}\right), (\operatorname{IsMUBFamily}\left(U\right)) \Rightarrow (\forall s:\operatorname{Fin}\left(2^{r}\right), \neg \operatorname{DetectsBoundEntanglement}\left(U, s\right)))))$$

*Formalization.* `D5/S3/Quantum/Entanglement/FourMUBBoundEntanglementRefutation.claim` (`✓ std3`).

*Citation.* J. Bae; A. Bera; D. Chruściński; B. C. Hiesmayr; D. McNulty (2022). *How many mutually unbiased bases are needed to detect bound entangled states?*. DOI: [10.1088/1751-8121/acaa16](https://doi.org/10.1088/1751-8121/acaa16). URL: <https://arxiv.org/abs/2108.01109>.

*Commentary.*

Section VIII, p. 8: 'Conjecture 1. If d = 2^r and r > 1, the minimal number of MUBs required for bound entanglement detection equals m = d/2 + 1 = 2^{r−1} + 1.' The preceding sentence reads: 'When d = 2^r, we predict that d/2 + 1 MUBs are both necessary and sufficient for the witness W^Γ(M_m, s) to be non-decomposable.' The formula states the necessity half for every natural r at least two, every family size below 2^(r−1)+1, every MUB family and every modular shift. Subtraction r−1 is natural subtraction. Refuting this half refutes the stated equality for the minimum.

**Lemma 1.5 (Real normalization identity).**

$$(\frac{1}{\operatorname{Real.sqrt}\left(8\right)}:\mathbb{R})^{2} = (\frac{1}{8}:\mathbb{R})$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/FourMUBBoundEntanglementRefutation.scale_sq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* J. Bae; A. Bera; D. Chruściński; B. C. Hiesmayr; D. McNulty (2022). *How many mutually unbiased bases are needed to detect bound entangled states?*. DOI: [10.1088/1751-8121/acaa16](https://doi.org/10.1088/1751-8121/acaa16). URL: <https://arxiv.org/abs/2108.01109>.

*Commentary.*

The square of the reciprocal of the real square root of eight equals one eighth.

**Lemma 1.6 (Complex normalization identity).**

$$((\frac{1}{\operatorname{Real.sqrt}\left(8\right)}:\mathbb{R}):\mathbb{C})^{2} = (\frac{1}{8}:\mathbb{C})$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/FourMUBBoundEntanglementRefutation.scale_complex_sq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* J. Bae; A. Bera; D. Chruściński; B. C. Hiesmayr; D. McNulty (2022). *How many mutually unbiased bases are needed to detect bound entangled states?*. DOI: [10.1088/1751-8121/acaa16](https://doi.org/10.1088/1751-8121/acaa16). URL: <https://arxiv.org/abs/2108.01109>.

*Commentary.*

The square of the complex coercion of the reciprocal of the real square root of eight equals the complex number one eighth.

**Theorem 1.7 (Refutation in dimension eight).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/FourMUBBoundEntanglementRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/bae-bera-chruscinski-hiesmayr-mcnulty-2022-four-mub-bound-entanglement` (refuted) by `D5/S3/Quantum/Entanglement/FourMUBBoundEntanglementRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"bae-bera-chruscinski-hiesmayr-mcnulty-2022-four-mub-bound-entanglement","declaration_gid":"D5/S3/Quantum/Entanglement/FourMUBBoundEntanglementRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* J. Bae; A. Bera; D. Chruściński; B. C. Hiesmayr; D. McNulty (2022). *How many mutually unbiased bases are needed to detect bound entangled states?*. DOI: [10.1088/1751-8121/acaa16](https://doi.org/10.1088/1751-8121/acaa16). URL: <https://arxiv.org/abs/2108.01109>.

*Commentary.*

Take r=3, m=4 and s=1. The bases are I, H/√8, diag(a)H/√8 and diag(b)H/√8, where H[x,k]=(−1)^(x·k) for the three binary coordinates, a=(1,1,i,i,i,−i,−1,1), and b=(1,1,1,−1,i,i,−i,i). Their overlap calculations use Walsh multiplication and finite character sums. The rational state is M/10134, with eight XOR sectors, each of the form [[A,B],[B,A]]. Thirty-two separate LDL identities with 128 positive pivots prove that the state and its partial transpose are positive semidefinite. Its trace is one and its exact witness expectation is −14/563. Thus four bases detect a PPT density matrix although the conjecture requires at least five. The proof establishes positive semidefiniteness, without a public strict-positivity or optimal-minimum statement.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/FourMUBBoundEntanglementRefutation.DetectsBoundEntanglement`
- Truth anchor: `D5/S3/Quantum/Entanglement/FourMUBBoundEntanglementRefutation.IsMUBFamily`
- Truth anchor: `D5/S3/Quantum/Entanglement/FourMUBBoundEntanglementRefutation.claim`
- Truth anchor: `D5/S3/Quantum/Entanglement/FourMUBBoundEntanglementRefutation.result`
- Truth anchor: `D5/S3/Quantum/Entanglement/FourMUBBoundEntanglementRefutation.scale_complex_sq`
- Truth anchor: `D5/S3/Quantum/Entanglement/FourMUBBoundEntanglementRefutation.scale_sq`
- Truth anchor: `D5/S3/Quantum/Entanglement/FourMUBBoundEntanglementRefutation.witnessGamma`
- Dependency: [D5/S3/Quantum/Divergence/ConditionalHockeyStickOrthogonalReduction](../Divergence/ConditionalHockeyStickOrthogonalReduction.md)
- Dependency: [D5/S3/Quantum/Entanglement/StructuredNegativityCoincidenceRefutation](StructuredNegativityCoincidenceRefutation.md)
