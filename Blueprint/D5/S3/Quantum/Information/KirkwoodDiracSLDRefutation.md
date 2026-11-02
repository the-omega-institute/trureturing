# A mixed-state KD-real SLD counterexample

## Abstract

A faithful nine-dimensional mixed state has a KD-real symmetric logarithmic derivative with nonzero quantum Fisher information, refuting the mixed-state exclusion conjecture.

**Definition 1.1 (The left Kirkwood–Dirac distribution).**

$$\forall d \in \mathbb{N},\; \forall a \in \operatorname{Matrix.unitaryGroup}\left(\operatorname{Fin}\left(d\right), \mathbb{C}\right),\; \forall b \in \operatorname{Matrix.unitaryGroup}\left(\operatorname{Fin}\left(d\right), \mathbb{C}\right),\; \forall C \in \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right),\; \forall x \in \operatorname{Fin}\left(d\right),\; \forall k \in \operatorname{Fin}\left(d\right),\; \operatorname{qLeft}\left(a, b, C\right)\left(x, k\right) = \operatorname{star}\left(\left(\operatorname{conjTranspose}\left(\operatorname{val}\left(a\right)\right) \cdot \operatorname{val}\left(b\right)\right)\left(x, k\right)\right) \cdot \left(\operatorname{conjTranspose}\left(\operatorname{val}\left(a\right)\right) \cdot C \cdot \operatorname{val}\left(b\right)\right)\left(x, k\right)$$

*Formalization.* `D5/S3/Quantum/Information/KirkwoodDiracSLDRefutation.qLeft` (`✓ std3`).

*Citation.* Matéo Spriet, Christopher Langrenez, Raymond Brummelhuis, Stephan De Bièvre (2026). *What Is Special About the Kirkwood–Dirac Distributions? Only They Produce Natural Conditional Expectations*. DOI: [10.48550/arXiv.2511.01996](https://doi.org/10.48550/arXiv.2511.01996). URL: <https://arxiv.org/abs/2511.01996v2>.

*Commentary.*

The left KD distribution is the conjugate overlap multiplied by the matrix coefficient between the two orthonormal eigenbases.

**Definition 1.2 (The left KD symbol).**

$$\forall d \in \mathbb{N},\; \forall a \in \operatorname{Matrix.unitaryGroup}\left(\operatorname{Fin}\left(d\right), \mathbb{C}\right),\; \forall b \in \operatorname{Matrix.unitaryGroup}\left(\operatorname{Fin}\left(d\right), \mathbb{C}\right),\; \forall C \in \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right),\; \forall x \in \operatorname{Fin}\left(d\right),\; \forall k \in \operatorname{Fin}\left(d\right),\; \operatorname{symbolLeft}\left(a, b, C\right)\left(x, k\right) = \operatorname{Inv.inv}\left(\left(\operatorname{conjTranspose}\left(\operatorname{val}\left(a\right)\right) \cdot \operatorname{val}\left(b\right)\right)\left(x, k\right)\right) \cdot \left(\operatorname{conjTranspose}\left(\operatorname{val}\left(a\right)\right) \cdot C \cdot \operatorname{val}\left(b\right)\right)\left(x, k\right)$$

*Formalization.* `D5/S3/Quantum/Information/KirkwoodDiracSLDRefutation.symbolLeft` (`✓ std3`).

*Citation.* Matéo Spriet, Christopher Langrenez, Raymond Brummelhuis, Stephan De Bièvre (2026). *What Is Special About the Kirkwood–Dirac Distributions? Only They Produce Natural Conditional Expectations*. DOI: [10.48550/arXiv.2511.01996](https://doi.org/10.48550/arXiv.2511.01996). URL: <https://arxiv.org/abs/2511.01996v2>.

*Commentary.*

The left symbol is the inverse overlap multiplied by the same matrix coefficient.

**Definition 1.3 (KD-real Hermitian matrices).**

$$\forall d \in \mathbb{N},\; \forall a \in \operatorname{Matrix.unitaryGroup}\left(\operatorname{Fin}\left(d\right), \mathbb{C}\right),\; \forall b \in \operatorname{Matrix.unitaryGroup}\left(\operatorname{Fin}\left(d\right), \mathbb{C}\right),\; \forall C \in \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right),\; \operatorname{IsKDReal}\left(a, b, C\right) = \left((\operatorname{IsHermitian}\left(C\right)) \land (\forall x \in \operatorname{Fin}\left(d\right),\; \forall k \in \operatorname{Fin}\left(d\right),\; \operatorname{Complex.im}\left(\operatorname{Inv.inv}\left(\left(\operatorname{conjTranspose}\left(\operatorname{val}\left(a\right)\right) \cdot \operatorname{val}\left(b\right)\right)\left(x, k\right)\right) \cdot \left(\operatorname{conjTranspose}\left(\operatorname{val}\left(a\right)\right) \cdot C \cdot \operatorname{val}\left(b\right)\right)\left(x, k\right)\right) = 0)\right)$$

*Formalization.* `D5/S3/Quantum/Information/KirkwoodDiracSLDRefutation.IsKDReal` (`✓ std3`).

*Citation.* Matéo Spriet, Christopher Langrenez, Raymond Brummelhuis, Stephan De Bièvre (2026). *What Is Special About the Kirkwood–Dirac Distributions? Only They Produce Natural Conditional Expectations*. DOI: [10.48550/arXiv.2511.01996](https://doi.org/10.48550/arXiv.2511.01996). URL: <https://arxiv.org/abs/2511.01996v2>.

*Commentary.*

A matrix is left KD-real when it is Hermitian and the imaginary part of its left KD symbol vanishes at every pair of basis labels.

**Definition 1.4 (The mixed-state conjecture).**

$$claim \Leftrightarrow (\forall d \in \mathbb{N},\; (0 < d) \Rightarrow (\forall a \in \operatorname{Matrix.unitaryGroup}\left(\operatorname{Fin}\left(d\right), \mathbb{C}\right),\; \forall b \in \operatorname{Matrix.unitaryGroup}\left(\operatorname{Fin}\left(d\right), \mathbb{C}\right),\; (\forall x \in \operatorname{Fin}\left(d\right),\; \forall k \in \operatorname{Fin}\left(d\right),\; \left(\operatorname{conjTranspose}\left(\operatorname{val}\left(a\right)\right) \cdot \operatorname{val}\left(b\right)\right)\left(x, k\right) \ne 0) \Rightarrow (\forall rho \in \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right),\; \forall X \in \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right),\; (\operatorname{D5.S3.Quantum.Information.SLDSpectralEnergy.IsDensity}\left(rho\right)) \Rightarrow ((\operatorname{IsKDReal}\left(a, b, rho\right)) \Rightarrow ((\operatorname{IsKDReal}\left(a, b, X\right)) \Rightarrow ((\exists L \in \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right),\; \operatorname{IsSLD}\left(rho, X, L\right)) \land (\forall L \in \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right),\; (\operatorname{D5.S3.Quantum.Information.FisherDiscord.Defs.IsSLD}\left(rho, X, L\right)) \Rightarrow ((4 \cdot \operatorname{D5.S3.Quantum.Information.FisherDiscord.Defs.fisherSLD}\left(rho, L\right) \ne 0) \Rightarrow (\neg (\operatorname{IsKDReal}\left(a, b, L\right)))))))))))$$

*Formalization.* `D5/S3/Quantum/Information/KirkwoodDiracSLDRefutation.claim` (`✓ std3`).

*Citation.* Matéo Spriet, Christopher Langrenez, Raymond Brummelhuis, Stephan De Bièvre (2026). *What Is Special About the Kirkwood–Dirac Distributions? Only They Produce Natural Conditional Expectations*. DOI: [10.48550/arXiv.2511.01996](https://doi.org/10.48550/arXiv.2511.01996). URL: <https://arxiv.org/abs/2511.01996v2>.

*Commentary.*

Section 6.3, immediately after equation (6.23), states verbatim: "In view of what precedes, it is tempting to conjecture that, if \hat \rho and \hat X are both KD real, the optimal observable \hat L must not be KD-real itself, provided \rm I_{QF} does not vanish." The encoding quantifies over every positive finite dimension, two unitary bases with nonzero overlaps, every density matrix and Hermitian observable in the KD-real sector, and every Hermitian SLD solution. The source QFI is 4 times fisherSLD.

**Theorem 1.5 (The conjecture is false).**

$$\neg (\forall d \in \mathbb{N},\; (0 < d) \Rightarrow (\forall a \in \operatorname{Matrix.unitaryGroup}\left(\operatorname{Fin}\left(d\right), \mathbb{C}\right),\; \forall b \in \operatorname{Matrix.unitaryGroup}\left(\operatorname{Fin}\left(d\right), \mathbb{C}\right),\; (\forall x \in \operatorname{Fin}\left(d\right),\; \forall k \in \operatorname{Fin}\left(d\right),\; \left(\operatorname{conjTranspose}\left(\operatorname{val}\left(a\right)\right) \cdot \operatorname{val}\left(b\right)\right)\left(x, k\right) \ne 0) \Rightarrow (\forall rho \in \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right),\; \forall X \in \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right),\; (\operatorname{D5.S3.Quantum.Information.SLDSpectralEnergy.IsDensity}\left(rho\right)) \Rightarrow ((\operatorname{IsKDReal}\left(a, b, rho\right)) \Rightarrow ((\operatorname{IsKDReal}\left(a, b, X\right)) \Rightarrow ((\exists L \in \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right),\; \operatorname{IsSLD}\left(rho, X, L\right)) \land (\forall L \in \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right),\; (\operatorname{D5.S3.Quantum.Information.FisherDiscord.Defs.IsSLD}\left(rho, X, L\right)) \Rightarrow ((4 \cdot \operatorname{D5.S3.Quantum.Information.FisherDiscord.Defs.fisherSLD}\left(rho, L\right) \ne 0) \Rightarrow (\neg (\operatorname{IsKDReal}\left(a, b, L\right)))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/KirkwoodDiracSLDRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/slbd2026` (refuted) by `D5/S3/Quantum/Information/KirkwoodDiracSLDRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"slbd2026","declaration_gid":"D5/S3/Quantum/Information/KirkwoodDiracSLDRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Matéo Spriet, Christopher Langrenez, Raymond Brummelhuis, Stephan De Bièvre (2026). *What Is Special About the Kirkwood–Dirac Distributions? Only They Produce Natural Conditional Expectations*. DOI: [10.48550/arXiv.2511.01996](https://doi.org/10.48550/arXiv.2511.01996). URL: <https://arxiv.org/abs/2511.01996v2>.

*Commentary.*

The explicit p = 3, dimension-nine witness uses the identity basis and an explicit Fourier basis, a faithful density matrix rho, the Hermitian observable X and the Hermitian matrix L. The coefficient calculations make rho, X and L KD-real; L solves the SLD equation; and the source-normalized QFI is 1/6, so the universal conclusion that every nonzero-QFI SLD is not KD-real fails.

## References

- Truth anchor: `D5/S3/Quantum/Information/KirkwoodDiracSLDRefutation.IsKDReal`
- Truth anchor: `D5/S3/Quantum/Information/KirkwoodDiracSLDRefutation.claim`
- Truth anchor: `D5/S3/Quantum/Information/KirkwoodDiracSLDRefutation.qLeft`
- Truth anchor: `D5/S3/Quantum/Information/KirkwoodDiracSLDRefutation.result`
- Truth anchor: `D5/S3/Quantum/Information/KirkwoodDiracSLDRefutation.symbolLeft`
- Dependency: [D5/S3/Quantum/Information/FisherDiscord/Defs](FisherDiscord/Defs.md)
- Dependency: [D5/S3/Quantum/Information/SLDSpectralEnergy](SLDSpectralEnergy.md)
