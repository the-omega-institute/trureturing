# Generalized Choi maps and absolute PPT

## Abstract

Generalized Choi maps preserve positivity on absolutely PPT qutrit density matrices.

**Definition 1.1 (The generalized Choi map).**

$$\forall (b:\mathbb{R}), \forall (c:\mathbb{R}), \forall (X:Matrix\left(Fin\left(3\right), Fin\left(3\right), \mathbb{C}\right)), choiGen\left(b, c, X\right)=SMul.smul\left(\frac{1}{2}, \begin{bmatrix}Complex.ofReal\left(((2-b)-c)\right)\cdot X\left(0, 0\right)+Complex.ofReal\left(b\right)\cdot X\left(1, 1\right)+Complex.ofReal\left(c\right)\cdot X\left(2, 2\right)&(-X\left(0, 1\right))&(-X\left(0, 2\right))\\(-X\left(1, 0\right))&Complex.ofReal\left(c\right)\cdot X\left(0, 0\right)+Complex.ofReal\left(((2-b)-c)\right)\cdot X\left(1, 1\right)+Complex.ofReal\left(b\right)\cdot X\left(2, 2\right)&(-X\left(1, 2\right))\\(-X\left(2, 0\right))&(-X\left(2, 1\right))&Complex.ofReal\left(b\right)\cdot X\left(0, 0\right)+Complex.ofReal\left(c\right)\cdot X\left(1, 1\right)+Complex.ofReal\left(((2-b)-c)\right)\cdot X\left(2, 2\right)\end{bmatrix}\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/GeneralizedChoiNonDetection.choiGen` (`✓ std3`).

*Citation.* Srinivasan Arunachalam, Nathaniel Johnston and Vincent Russo (2015). *Is absolute separability determined by the partial transpose?*. URL: <https://arxiv.org/abs/1405.5853v3>.

*Commentary.*

Arunachalam–Johnston–Russo, Section 5.3, page 14. The coefficient a is 2-b-c. Indices are zero-based; the displayed entry at (0,0) is the source entry at (1,1). The scalar one-half is real and acts on the complex matrix.

**Definition 1.2 (Action on the second tensor factor).**

$$\forall (Phi:Matrix\left(Fin\left(3\right), Fin\left(3\right), \mathbb{C}\right)\to Matrix\left(Fin\left(3\right), Fin\left(3\right), \mathbb{C}\right)), \forall (rho:Matrix\left((Fin\left(3\right)\times Fin\left(3\right)), (Fin\left(3\right)\times Fin\left(3\right)), \mathbb{C}\right)), \forall (i:Fin\left(3\right)), \forall (k:Fin\left(3\right)), \forall (j:Fin\left(3\right)), \forall (l:Fin\left(3\right)), idTensor\left(Phi, rho\right)\left((i,k), (j,l)\right)=Phi\left((fun s t \mapsto rho\left((i,s), (j,t)\right))\right)\left(k, l\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/GeneralizedChoiNonDetection.idTensor` (`✓ std3`).

*Citation.* Srinivasan Arunachalam, Nathaniel Johnston and Vincent Russo (2015). *Is absolute separability determined by the partial transpose?*. URL: <https://arxiv.org/abs/1405.5853v3>.

*Commentary.*

The map acts on every three-by-three block. The second tensor factor carries Phi, matching the second-factor partial transpose in APPT.

**Definition 1.3 (Non-detection for the full parameter region).**

$$claim\iff \forall (b:\mathbb{R}), \forall (c:\mathbb{R}), (0\leq b)\Rightarrow (0\leq c)\Rightarrow ((b,c)\neq (0,0))\Rightarrow ((b+c\leq 1)\lor (((b+c-1))^{2}\leq b\cdot c))\Rightarrow \forall (rho:Matrix\left((Fin\left(3\right)\times Fin\left(3\right)), (Fin\left(3\right)\times Fin\left(3\right)), \mathbb{C}\right)), (Matrix.PosSemidef\left(rho\right))\Rightarrow (Matrix.trace\left(rho\right)=1)\Rightarrow (APPT\left(rho\right))\Rightarrow Matrix.PosSemidef\left(idTensor\left(choiGen\left(b, c\right), rho\right)\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/GeneralizedChoiNonDetection.claim` (`✓ std3`).

*Citation.* Srinivasan Arunachalam, Nathaniel Johnston and Vincent Russo (2015). *Is absolute separability determined by the partial transpose?*. URL: <https://arxiv.org/abs/1405.5853v3>.

*Commentary.*

Arunachalam–Johnston–Russo, Section 7, page 21, asks whether every generalized Choi map in the stated region is incapable of detecting absolutely PPT entanglement. APPT is the literal predicate of QutritPerturbationAttainment; density positivity and trace normalization are separate hypotheses.

**Theorem 1.4 (Homogeneous quadratic estimate).**

$$\forall (b:\mathbb{R}), \forall (c:\mathbb{R}), ((((2-b)-c))^{2}+(b)^{2}+(c)^{2}\leq 2)\Rightarrow \forall (v:(Fin\left(3\right)\times Fin\left(3\right))\to \mathbb{C}), Complex.re\left(Matrix.trace\left(idTensor\left(choiGen\left(c, b\right), Matrix.vecMulVec\left(v, star\left(v\right)\right)\right)\cdot idTensor\left(choiGen\left(c, b\right), Matrix.vecMulVec\left(v, star\left(v\right)\right)\right)\right)\right)\leq \frac{(\sum_{i:(Fin\left(3\right)\times Fin\left(3\right))} Complex.normSq\left(v\left(i\right)\right))^{2}}{2}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/GeneralizedChoiNonDetection.witness_purity_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a vector of arbitrary length, the adjoint image of its rank-one matrix has real trace-square at most half the squared total component mass whenever the parameter square-sum is at most two. A Gram-matrix purity estimate and the sum of three squared column masses give the bound.

**Theorem 1.5 (Non-detection on absolutely PPT states).**

$$claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/GeneralizedChoiNonDetection.result` (`✓ std3`). ∎

*Resolves.* `Problems/arunachalam-johnston-russo-2015-generalized-choi-absolutely-ppt` (proved) by `D5/S3/Quantum/Entanglement/AbsolutePPT/GeneralizedChoiNonDetection.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"arunachalam-johnston-russo-2015-generalized-choi-absolutely-ppt","declaration_gid":"D5/S3/Quantum/Entanglement/AbsolutePPT/GeneralizedChoiNonDetection.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Commentary.*

The adjoint quadratic estimate combines with the qutrit APPT purity bound 17/121 and centered Frobenius Cauchy–Schwarz. In the triangle b+c≤1 the map is a positive combination of the two boundary maps and a diagonal conjugation map.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/GeneralizedChoiNonDetection.choiGen`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/GeneralizedChoiNonDetection.claim`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/GeneralizedChoiNonDetection.idTensor`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/GeneralizedChoiNonDetection.result`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/GeneralizedChoiNonDetection.witness_purity_bound`
- Dependency: [D5/S3/Quantum/Entanglement/AbsolutePPT/QutritN3PurityBound](QutritN3PurityBound.md)
- Dependency: [D5/S3/Quantum/Matrix/CartesianVariance](../../Matrix/CartesianVariance.md)
