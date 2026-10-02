# Oblique discord: mutual information can increase

## Abstract

A normalized oblique operation can increase two-qubit mutual information. The state (8|00> + |11>)/sqrt(65) and the normalized oblique basis (2, +/-1)/sqrt(5) refute Xu's Conjecture, Eq. (22) of arXiv:1506.00404v1.

**Definition 1.1 (Normalized basis and biorthogonal dual).**

$$\forall n: \mathbb{N}, \operatorname{ObliqueBasis}\left(n\right) = \{ v:\operatorname{Module.Basis}\left(\operatorname{Fin}\left(n\right), \mathbb{C}, \operatorname{Fin}\left(n\right)\to\mathbb{C}\right); w:\operatorname{Module.Basis}\left(\operatorname{Fin}\left(n\right), \mathbb{C}, \operatorname{Fin}\left(n\right)\to\mathbb{C}\right); normalized:(\forall i: \operatorname{Fin}\left(n\right), \operatorname{dotProduct}\left(\operatorname{star}\left(v\left(i\right)\right), v\left(i\right)\right) = 1); dual:(\forall i: \operatorname{Fin}\left(n\right), \forall j: \operatorname{Fin}\left(n\right), \operatorname{dotProduct}\left(\operatorname{star}\left(v\left(i\right)\right), w\left(j\right)\right) = \operatorname{KroneckerDelta}\left(i, j\right)) \}$$

*Formalization.* `D5/S3/Quantum/Information/ObliqueDiscordMutualInformationRefutation.ObliqueBasis` (`✓ std3`).

*Citation.* Jianwei Xu (2015). *Oblique discord*. DOI: [10.1142/S0217979216502568](https://doi.org/10.1142/S0217979216502568). URL: <https://arxiv.org/abs/1506.00404v1>.

*Commentary.*

Xu, p. 2 immediately before Eq. (13): "Suppose $\{|i\rangle \}_{i = 1}^{n_{A}}$ is a normalized basis of $H^{A}$ which not necessarily orthogonal to each other. There exists an unique basis $\{|\widetilde{i}\rangle \}_{i = 1}^{n}$ of $H^{A}$ such that $\langle i|\widetilde{j}\rangle = \delta_{ij}$, note that $\{|\widetilde{i}\rangle \}_{i = 1}^{n}$ not necessarily orthogonal and not necessarily normalized. $\{|\widetilde{i}\rangle \}_{i = 1}^{n_{A}}$ is called the dual basis of $\{|i\rangle \}_{i = 1}^{n_{A}}$." The structure has two actual Module.Basis objects v and w, followed by the normalized and dual proof fields displayed below. Fin n indexes the source's n vectors from zero. The inner product conjugates its first argument. KroneckerDelta(i,j) is 1 if i = j and 0 otherwise.

**Definition 1.2 (Oblique Kraus matrices).**

$$\forall n: \mathbb{N}, \forall b: \operatorname{ObliqueBasis}\left(n\right), \forall i: \operatorname{Fin}\left(n\right), \operatorname{kraus}\left(b, i\right) = \operatorname{vecMulVec}\left(\operatorname{v}\left(b\right)\left(i\right), \operatorname{star}\left(\operatorname{w}\left(b\right)\left(i\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Information/ObliqueDiscordMutualInformationRefutation.kraus` (`✓ std3`).

*Citation.* Jianwei Xu (2015). *Oblique discord*. DOI: [10.1142/S0217979216502568](https://doi.org/10.1142/S0217979216502568). URL: <https://arxiv.org/abs/1506.00404v1>.

*Commentary.*

The i-th matrix is |v_i><w_i|. vecMulVec forms the outer product and star conjugates each vector entry. Each matrix acts on the A factor.

**Definition 1.3 (Unnormalized bipartite operation).**

$$\forall nA: \mathbb{N}, \forall nB: \mathbb{N}, \forall b: \operatorname{ObliqueBasis}\left(nA\right), \forall \rho: \operatorname{Matrix}\left((\operatorname{Fin}\left(nA\right)\times \operatorname{Fin}\left(nB\right)), (\operatorname{Fin}\left(nA\right)\times \operatorname{Fin}\left(nB\right)), \mathbb{C}\right), \operatorname{rawOblique}\left(b, \rho\right) = \sum_{i\in \operatorname{Fin}\left(nA\right)} \operatorname{Matrix.kronecker}\left(\operatorname{kraus}\left(b, i\right), (1:\operatorname{Matrix}\left(\operatorname{Fin}\left(nB\right), \operatorname{Fin}\left(nB\right), \mathbb{C}\right))\right) \cdot \rho \cdot \operatorname{conjTranspose}\left(\operatorname{Matrix.kronecker}\left(\operatorname{kraus}\left(b, i\right), (1:\operatorname{Matrix}\left(\operatorname{Fin}\left(nB\right), \operatorname{Fin}\left(nB\right), \mathbb{C}\right))\right)\right)$$

*Formalization.* `D5/S3/Quantum/Information/ObliqueDiscordMutualInformationRefutation.rawOblique` (`✓ std3`).

*Citation.* Jianwei Xu (2015). *Oblique discord*. DOI: [10.1142/S0217979216502568](https://doi.org/10.1142/S0217979216502568). URL: <https://arxiv.org/abs/1506.00404v1>.

*Commentary.*

Tensor each oblique Kraus matrix with the identity matrix on B, then sum K rho K^H. Matrix.kronecker is the matrix Kronecker product; the typed 1 is the identity on Fin nB, and conjTranspose denotes conjugate transpose. The input of rawOblique is a matrix rather than a density-state subtype.

**Definition 1.4 (Source denominator).**

$$\forall nA: \mathbb{N}, \forall nB: \mathbb{N}, \forall b: \operatorname{ObliqueBasis}\left(nA\right), \forall \rho: \operatorname{Matrix}\left((\operatorname{Fin}\left(nA\right)\times \operatorname{Fin}\left(nB\right)), (\operatorname{Fin}\left(nA\right)\times \operatorname{Fin}\left(nB\right)), \mathbb{C}\right), \operatorname{normalizer}\left(b, \rho\right) = \operatorname{Re}\left(\operatorname{partialTraceRight}\left(\sum_{i\in \operatorname{Fin}\left(nA\right)} \operatorname{Matrix.kronecker}\left((\operatorname{Matrix.replicateRow}\left(Unit, \operatorname{star}\left(\operatorname{w}\left(b\right)\left(i\right)\right)\right)), (1:\operatorname{Matrix}\left(\operatorname{Fin}\left(nB\right), \operatorname{Fin}\left(nB\right), \mathbb{C}\right))\right) \cdot \rho \cdot \operatorname{conjTranspose}\left(\operatorname{Matrix.kronecker}\left((\operatorname{Matrix.replicateRow}\left(Unit, \operatorname{star}\left(\operatorname{w}\left(b\right)\left(i\right)\right)\right)), (1:\operatorname{Matrix}\left(\operatorname{Fin}\left(nB\right), \operatorname{Fin}\left(nB\right), \mathbb{C}\right))\right)\right)\right)\left(\operatorname{Unit.unit}\left(\right)\right)\left(\operatorname{Unit.unit}\left(\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Information/ObliqueDiscordMutualInformationRefutation.normalizer` (`✓ std3`).

*Citation.* Jianwei Xu (2015). *Oblique discord*. DOI: [10.1142/S0217979216502568](https://doi.org/10.1142/S0217979216502568). URL: <https://arxiv.org/abs/1506.00404v1>.

*Commentary.*

The rectangular matrix L_i is the bra w_i tensor the identity on B, so L_i rho L_i^H is the B-valued sandwich <w_i|rho|w_i>. partialTraceRight takes the trace over B and leaves a one-dimensional Unit factor; evaluating at ((),()) extracts the scalar. normalizer is its real part. The source denominator is therefore the trace over B of the sum of these sandwiches.

**Definition 1.5 (State-dependent source normalization).**

$$\forall nA: \mathbb{N}, \forall nB: \mathbb{N}, \forall b: \operatorname{ObliqueBasis}\left(nA\right), \forall \rho: \operatorname{DensityState}\left((\operatorname{Fin}\left(nA\right)\times \operatorname{Fin}\left(nB\right))\right), \forall ht: 0 < \operatorname{normalizer}\left(b, \operatorname{CStarMatrix.ofMatrix.symm}\left(\operatorname{val}\left(\rho\right)\right)\right), \operatorname{val}\left(\operatorname{phi}\left(b, \rho, ht\right)\right) = \operatorname{CStarMatrix.ofMatrix}\left(\operatorname{SMul.smul}\left(\operatorname{inv}\left(\operatorname{normalizer}\left(b, \operatorname{CStarMatrix.ofMatrix.symm}\left(\operatorname{val}\left(\rho\right)\right)\right)\right), \operatorname{rawOblique}\left(b, \operatorname{CStarMatrix.ofMatrix.symm}\left(\operatorname{val}\left(\rho\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Information/ObliqueDiscordMutualInformationRefutation.phi` (`✓ std3`).

*Citation.* Jianwei Xu (2015). *Oblique discord*. DOI: [10.1142/S0217979216502568](https://doi.org/10.1142/S0217979216502568). URL: <https://arxiv.org/abs/1506.00404v1>.

*Commentary.*

Xu, p. 2, Eq. (13): "We define the quantum operation Φ<sub><i>A</i></sub> = $\{|i\rangle \langle \widetilde{i}|\}_{i = 1}^{n_{A}}$ which operates the bipartite state $\rho^{AB}$ as Φ<sub><i>A</i></sub><i>ρ</i><sup><i>AB</i></sup> = $\frac{\sum_{i = 1}^{n_{A}} |i\rangle \langle \widetilde{i}|\rho^{AB}|\widetilde{i}\rangle \langle i|}{tr[\sum_{i = 1}^{n_{A}} \langle \widetilde{i}|\rho^{AB}|\widetilde{i}\rangle ]}$." phi divides by normalizer, the partial trace over B of the sum of dual-vector sandwiches printed in Eq. (13). Unit norm of each v_i implies that this scalar equals the real trace of the numerator; this equality is proved inside the definition. The displayed equality describes its underlying value; its positivity and trace-one proofs package it as a DensityState. CStarMatrix.ofMatrix embeds the matrix and SMul.smul applies its real scalar. The binder ht is the proof of a strictly positive normalizing trace.

**Definition 1.6 (Xu's conjectured monotonicity).**

$$claim \Leftrightarrow (\forall nA: \mathbb{N}, \forall nB: \mathbb{N}, \forall b: \operatorname{ObliqueBasis}\left(nA\right), \forall \rho: \operatorname{DensityState}\left((\operatorname{Fin}\left(nA\right)\times \operatorname{Fin}\left(nB\right))\right), \forall ht: 0 < \operatorname{normalizer}\left(b, \operatorname{CStarMatrix.ofMatrix.symm}\left(\operatorname{val}\left(\rho\right)\right)\right), \operatorname{quantumMutualInformation}\left(\operatorname{phi}\left(b, \rho, ht\right)\right) \le \operatorname{quantumMutualInformation}\left(\rho\right))$$

*Formalization.* `D5/S3/Quantum/Information/ObliqueDiscordMutualInformationRefutation.claim` (`✓ std3`).

*Citation.* Jianwei Xu (2015). *Oblique discord*. DOI: [10.1142/S0217979216502568](https://doi.org/10.1142/S0217979216502568). URL: <https://arxiv.org/abs/1506.00404v1>.

*Commentary.*

Xu, p. 3, Eq. (22): "Conjecture: $I\left(\rho^{AB}\right)$ ≥ <i>I</i>(Φ<sub><i>A</i></sub><i>ρ</i><sup><i>AB</i></sup>) for any Φ<sub><i>A</i></sub> and any $\rho^{AB}$, where $I\left(\rho^{AB}\right)$ is the mutual information, Φ<sub><i>A</i></sub> is defined in Eq.(13)." Its operation on p. 2, Eq. (13), is: "We define the quantum operation Φ<sub><i>A</i></sub> = $\{|i\rangle \langle \widetilde{i}|\}_{i = 1}^{n_{A}}$ which operates the bipartite state $\rho^{AB}$ as Φ<sub><i>A</i></sub><i>ρ</i><sup><i>AB</i></sup> = $\frac{\sum_{i = 1}^{n_{A}} |i\rangle \langle \widetilde{i}|\rho^{AB}|\widetilde{i}\rangle \langle i|}{tr[\sum_{i = 1}^{n_{A}} \langle \widetilde{i}|\rho^{AB}|\widetilde{i}\rangle ]}$." The quantifiers range over all finite dimensions, all normalized oblique bases with their duals, and all bipartite density states for which the operation is defined. DensityState is the positive trace-one CStarMatrix subtype; no entropy value or spectrum is assumed. quantumMutualInformation is the existing sum of the actual marginal vonNeumannEntropy values minus the joint vonNeumannEntropy. The claim uses natural logarithms, which preserve the conjecture's comparison in base two.

**Theorem 1.7 (Two qubits refute monotonicity).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/ObliqueDiscordMutualInformationRefutation.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jianwei Xu (2015). *Oblique discord*. DOI: [10.1142/S0217979216502568](https://doi.org/10.1142/S0217979216502568). URL: <https://arxiv.org/abs/1506.00404v1>.

*Commentary.*

Take v_+ = (2,1)/sqrt(5), v_- = (2,-1)/sqrt(5) and w_+ = (sqrt(5)/4,sqrt(5)/2), w_- = (sqrt(5)/4,-sqrt(5)/2). The input rho is the rank-one projector onto (8|00> + |11>)/sqrt(65). The source normalizer and unnormalized trace are 17/26 and the output tau is (1/85)[[64,0,0,8],[0,4,8,0],[0,8,16,0],[8,0,0,1]]. Rational similarity certificates identify the spectra: rho has eigenvalues 1,0,0,0 and tau has 13/17,4/17,0,0. The marginals of rho are diag(64/65,1/65); those of tau are diag(4/5,1/5) and diag(16/17,1/17). For h(p) = -p log(p) -(1-p) log(1-p), the information gain is h(1/5)+h(1/17)-h(4/17)-2h(1/65) = (7648/1105) log(2) -log(5) -(21/17) log(13) > 0. The elementary comparisons 5^3 < 2^7 and 13^17 < 2^63 certify strict positivity by logarithmic monotonicity.

## References

- Truth anchor: `D5/S3/Quantum/Information/ObliqueDiscordMutualInformationRefutation.ObliqueBasis`
- Truth anchor: `D5/S3/Quantum/Information/ObliqueDiscordMutualInformationRefutation.claim`
- Truth anchor: `D5/S3/Quantum/Information/ObliqueDiscordMutualInformationRefutation.kraus`
- Truth anchor: `D5/S3/Quantum/Information/ObliqueDiscordMutualInformationRefutation.normalizer`
- Truth anchor: `D5/S3/Quantum/Information/ObliqueDiscordMutualInformationRefutation.phi`
- Truth anchor: `D5/S3/Quantum/Information/ObliqueDiscordMutualInformationRefutation.rawOblique`
- Truth anchor: `D5/S3/Quantum/Information/ObliqueDiscordMutualInformationRefutation.result`
- Dependency: [D5/S3/Quantum/Information/InputInformationBalance](InputInformationBalance.md)
