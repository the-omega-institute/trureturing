# LikelihoodSpectrum

## Abstract

Positive matrix maps and the two-triangle obstruction to Rényi sufficiency.

**Theorem 1.1 (matrixPower eq).**

$$\forall (n: \mathbb{N}), \forall (A: \operatorname{Matrix} (\operatorname{Fin} n) (\operatorname{Fin} n) \mathbb{C}), \forall (hA: A.\operatorname{IsHermitian}), \forall (t: \mathbb{R}), \operatorname{matrixPower} A t = \operatorname{mpow} hA t$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumChannels/RenyiSufficiency/LikelihoodSpectrum.matrixPower_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On Hermitian matrices the total power extension is the Hermitian functional calculus.

**Theorem 1.2 (rho hermitian).**

$$\forall (minus: \operatorname{Bool}), \forall (e: \mathbb{R}), (\operatorname{rho} minus e).\operatorname{IsHermitian}$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumChannels/RenyiSufficiency/LikelihoodSpectrum.rho_hermitian` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each real edge is symmetric and each imaginary edge has its complex conjugate in the transposed entry.

**Definition 1.3 (mpow).**

$$\forall (n: \mathbb{N}), \forall (A: \operatorname{Matrix} (\operatorname{Fin} n) (\operatorname{Fin} n) \mathbb{C}), \forall (hA: A.\operatorname{IsHermitian}), \forall (t: \mathbb{R}), \operatorname{mpow} hA t = (hA.\operatorname{cfc} (\lambda (x : \mathbb{R}) \mapsto x^{t}))$$

*Formalization.* `D5/S3/QuantumChannels/RenyiSufficiency/LikelihoodSpectrum.mpow` (`✓ std3`).

*Citation.* N. Galke, L. van Luijk, H. Wilming (2023). *Sufficiency of Rényi divergences*. DOI: [10.48550/arXiv.2304.12989](https://doi.org/10.48550/arXiv.2304.12989). URL: <https://arxiv.org/abs/2304.12989v6>.

*Commentary.*

The real power uses Matrix.IsHermitian.cfc with Real.rpow, under the Hermitian proof hA.

**Definition 1.4 (matrixPower).**

$$\forall (n: \mathbb{N}), \forall (A: \operatorname{Matrix} (\operatorname{Fin} n) (\operatorname{Fin} n) \mathbb{C}), \forall (t: \mathbb{R}), \operatorname{matrixPower} A t = (\operatorname{if} hA : A.\operatorname{IsHermitian} \operatorname{then} \operatorname{mpow} hA t \operatorname{else} 0)$$

*Formalization.* `D5/S3/QuantumChannels/RenyiSufficiency/LikelihoodSpectrum.matrixPower` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The total extension evaluates the Hermitian functional calculus and returns zero when the matrix is not Hermitian.

**Definition 1.5 (matrixLog).**

$$\forall (n: \mathbb{N}), \forall (A: \operatorname{Matrix} (\operatorname{Fin} n) (\operatorname{Fin} n) \mathbb{C}), \operatorname{matrixLog} A = (\operatorname{if} hA : A.\operatorname{IsHermitian} \operatorname{then} hA.\operatorname{cfc} \operatorname{Real}.\operatorname{log} \operatorname{else} 0)$$

*Formalization.* `D5/S3/QuantumChannels/RenyiSufficiency/LikelihoodSpectrum.matrixLog` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The total logarithm extension evaluates Matrix.IsHermitian.cfc with Real.log and returns zero outside Hermitian matrices.

**Definition 1.6 (Dmin).**

$$\forall (n: \mathbb{N}), \forall (rho: \operatorname{Matrix} (\operatorname{Fin} n) (\operatorname{Fin} n) \mathbb{C}), \forall (sigma: \operatorname{Matrix} (\operatorname{Fin} n) (\operatorname{Fin} n) \mathbb{C}), \forall (alpha: \mathbb{R}), \operatorname{Dmin} rho sigma alpha = (\operatorname{if} alpha = 1 \operatorname{then} (rho \times (\operatorname{matrixLog} rho - \operatorname{matrixLog} sigma)) .\operatorname{trace} .\operatorname{re} \operatorname{else} (alpha - 1)^{-1} \times \operatorname{Real}.\operatorname{log} (\operatorname{matrixPower} (\operatorname{matrixPower} sigma ((1 - alpha) / (2 \times alpha)) \times rho \times \operatorname{matrixPower} sigma ((1 - alpha) / (2 \times alpha))) alpha .\operatorname{trace} .\operatorname{re}))$$

*Formalization.* `D5/S3/QuantumChannels/RenyiSufficiency/LikelihoodSpectrum.Dmin` (`✓ std3`).

*Citation.* N. Galke, L. van Luijk, H. Wilming (2023). *Sufficiency of Rényi divergences*. DOI: [10.48550/arXiv.2304.12989](https://doi.org/10.48550/arXiv.2304.12989). URL: <https://arxiv.org/abs/2304.12989v6>.

*Commentary.*

Appendix E, p. 35, Eq. (105): “The minimal quantum Rényi divergence (or sandwiched Rényi divergence) is given by” the displayed sandwiched trace power. “The limit α → 1 is the quantum relative entropy.” The α = 1 branch is the Umegaki relative entropy tr ρ (log ρ − log σ). The factors (1−alpha)/(2 alpha) are divisions in Real.

**Definition 1.7 (DminFinite).**

$$\forall (n: \mathbb{N}), \forall (rho: \operatorname{Matrix} (\operatorname{Fin} n) (\operatorname{Fin} n) \mathbb{C}), \forall (sigma: \operatorname{Matrix} (\operatorname{Fin} n) (\operatorname{Fin} n) \mathbb{C}), \forall (alpha: \mathbb{R}), \operatorname{DminFinite} rho sigma alpha = ((1 \leq alpha \to \operatorname{LinearMap}.\operatorname{range} rho.\operatorname{toLin}' \leq \operatorname{LinearMap}.\operatorname{range} sigma.\operatorname{toLin}') \land (alpha < 1 \to rho \times sigma \neq 0))$$

*Formalization.* `D5/S3/QuantumChannels/RenyiSufficiency/LikelihoodSpectrum.DminFinite` (`✓ std3`).

*Citation.* N. Galke, L. van Luijk, H. Wilming (2023). *Sufficiency of Rényi divergences*. DOI: [10.48550/arXiv.2304.12989](https://doi.org/10.48550/arXiv.2304.12989). URL: <https://arxiv.org/abs/2304.12989v6>.

*Commentary.*

Finiteness is support inclusion at alpha at least one, and nonorthogonality below one. Support is LinearMap.range of Matrix.toLin'.

**Definition 1.8 (IsPTP).**

$$\forall (n: \mathbb{N}), \forall (m: \mathbb{N}), \forall (T: \operatorname{Matrix} (\operatorname{Fin} n) (\operatorname{Fin} n) \mathbb{C} \to_{l}[\mathbb{C}] \operatorname{Matrix} (\operatorname{Fin} m) (\operatorname{Fin} m) \mathbb{C}), \operatorname{IsPTP} T = ((\operatorname{IsPositive} T) \land (\forall (X : \operatorname{Matrix} (\operatorname{Fin} n) (\operatorname{Fin} n) \mathbb{C}) , (T X) .\operatorname{trace} = X.\operatorname{trace}))$$

*Formalization.* `D5/S3/QuantumChannels/RenyiSufficiency/LikelihoodSpectrum.IsPTP` (`✓ std3`).

*Citation.* N. Galke, L. van Luijk, H. Wilming (2023). *Sufficiency of Rényi divergences*. DOI: [10.48550/arXiv.2304.12989](https://doi.org/10.48550/arXiv.2304.12989). URL: <https://arxiv.org/abs/2304.12989v6>.

*Commentary.*

A positive trace-preserving map is a complex-linear map that sends each positive semidefinite input to a positive semidefinite output and preserves the trace. IsPositive is the existing MatrixMap predicate.

**Definition 1.9 (Interconvertible).**

$$\forall (n: \mathbb{N}), \forall (m: \mathbb{N}), \forall (rho1: \operatorname{Matrix} (\operatorname{Fin} n) (\operatorname{Fin} n) \mathbb{C}), \forall (sigma1: \operatorname{Matrix} (\operatorname{Fin} n) (\operatorname{Fin} n) \mathbb{C}), \forall (rho2: \operatorname{Matrix} (\operatorname{Fin} m) (\operatorname{Fin} m) \mathbb{C}), \forall (sigma2: \operatorname{Matrix} (\operatorname{Fin} m) (\operatorname{Fin} m) \mathbb{C}), \operatorname{Interconvertible} rho1 sigma1 rho2 sigma2 = (\exists (T : \operatorname{Matrix} (\operatorname{Fin} n) (\operatorname{Fin} n) \mathbb{C} \to_{l}[\mathbb{C}] \operatorname{Matrix} (\operatorname{Fin} m) (\operatorname{Fin} m) \mathbb{C}) (R : \operatorname{Matrix} (\operatorname{Fin} m) (\operatorname{Fin} m) \mathbb{C} \to_{l}[\mathbb{C}] \operatorname{Matrix} (\operatorname{Fin} n) (\operatorname{Fin} n) \mathbb{C}) , (\operatorname{IsPTP} T) \land (\operatorname{IsPTP} R) \land (T rho1 = rho2) \land (T sigma1 = sigma2) \land (R rho2 = rho1) \land (R sigma2 = sigma1))$$

*Formalization.* `D5/S3/QuantumChannels/RenyiSufficiency/LikelihoodSpectrum.Interconvertible` (`✓ std3`).

*Citation.* N. Galke, L. van Luijk, H. Wilming (2023). *Sufficiency of Rényi divergences*. DOI: [10.48550/arXiv.2304.12989](https://doi.org/10.48550/arXiv.2304.12989). URL: <https://arxiv.org/abs/2304.12989v6>.

*Commentary.*

Section 3.3, p. 16, Eq. (40): “In the following, we therefore write” (ρ₁, σ₁) ↔ᴾ (ρ₂, σ₂) “if the two dichotomies can be interconverted using positive trace-preserving maps T, R.” The encoding requires T(rho1)=rho2, T(sigma1)=sigma2, R(rho2)=rho1 and R(sigma2)=sigma1.

**Definition 1.10 (rho).**

$$\forall (minus: \operatorname{Bool}), \forall (e: \mathbb{C}), \operatorname{rho} minus e = (!! [1 / 5 , e / 5 , - \operatorname{Complex}.\operatorname{I} \times e / 5 , e / 5 , (\operatorname{if} minus \operatorname{then} \operatorname{Complex}.\operatorname{I} \operatorname{else} - \operatorname{Complex}.\operatorname{I}) \times e / 5 ; e / 5 , 1 / 5 , e / 5 , 0 , 0 ; \operatorname{Complex}.\operatorname{I} \times e / 5 , e / 5 , 1 / 5 , 0 , 0 ; e / 5 , 0 , 0 , 1 / 5 , e / 5 ; (\operatorname{if} minus \operatorname{then} - \operatorname{Complex}.\operatorname{I} \operatorname{else} \operatorname{Complex}.\operatorname{I}) \times e / 5 , 0 , 0 , e / 5 , 1 / 5])$$

*Formalization.* `D5/S3/QuantumChannels/RenyiSufficiency/LikelihoodSpectrum.rho` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The two Hermitian bouquet matrices have four real edges and two imaginary edges. The Boolean minus changes the orientation of the second triangle. The displayed rows have index type Fin 5 and entries in Complex.

**Definition 1.11 (weightedRho).**

$$\forall (minus: \operatorname{Bool}), \forall (e: \mathbb{C}), \forall (d: \operatorname{Fin} 5 \to \mathbb{C}), \operatorname{weightedRho} minus e d = (\operatorname{diagonal} d \times \operatorname{rho} minus e \times \operatorname{diagonal} d)$$

*Formalization.* `D5/S3/QuantumChannels/RenyiSufficiency/LikelihoodSpectrum.weightedRho` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The complete parameter telescope and conclusion are displayed. Matrix products, transpose and conjTranspose have their Mathlib meanings; arrows indexed by Complex denote LinearMap.

**Definition 1.12 (sigma).**

$$\operatorname{sigma} = (\operatorname{diagonal} (\lambda (i : \operatorname{Fin} 5) \mapsto ((((i.\operatorname{val} + 1 : \mathbb{N}) : \mathbb{R}) / 15 : \mathbb{R}) : \mathbb{C})))$$

*Formalization.* `D5/S3/QuantumChannels/RenyiSufficiency/LikelihoodSpectrum.sigma` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The reference density matrix is diagonal with entries (i.val+1)/15. The additions in i.val+1 are in Nat; the quotient is taken after coercion to Real and then Complex.

**Theorem 1.13 (sigma posDef).**

$$\operatorname{sigma}.\operatorname{PosDef}$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumChannels/RenyiSufficiency/LikelihoodSpectrum.sigma_posDef` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The complete parameter telescope and conclusion are displayed. Matrix products, transpose and conjTranspose have their Mathlib meanings; arrows indexed by Complex denote LinearMap.

**Theorem 1.14 (matrixPower diagonal).**

$$\forall (n: \mathbb{N}), \forall (d: \operatorname{Fin} n \to \mathbb{R}), \forall (t: \mathbb{R}), \operatorname{matrixPower} (\operatorname{diagonal} (\lambda i \mapsto (d i : \mathbb{C}))) t = \operatorname{diagonal} (\lambda i \mapsto (((d i)^{t} : \mathbb{R}) : \mathbb{C}))$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumChannels/RenyiSufficiency/LikelihoodSpectrum.matrixPower_diagonal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The complete parameter telescope and conclusion are displayed. Matrix products, transpose and conjTranspose have their Mathlib meanings; arrows indexed by Complex denote LinearMap.

**Theorem 1.15 (weightedRho hermitian).**

$$\forall (minus: \operatorname{Bool}), \forall (e: \mathbb{R}), \forall (d: \operatorname{Fin} 5 \to \mathbb{R}), (\operatorname{weightedRho} minus (e : \mathbb{C}) (\lambda i \mapsto (d i : \mathbb{C}))) .\operatorname{IsHermitian}$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumChannels/RenyiSufficiency/LikelihoodSpectrum.weightedRho_hermitian` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The complete parameter telescope and conclusion are displayed. Matrix products, transpose and conjTranspose have their Mathlib meanings; arrows indexed by Complex denote LinearMap.

**Definition 1.16 (likelihoodPolynomial).**

$$\operatorname{likelihoodPolynomial} = (\operatorname{Polynomial}.\operatorname{C} (1 / 1 : \mathbb{C}) \times \operatorname{Polynomial}.X^{5} + \operatorname{Polynomial}.\operatorname{C} (- 137 / 20 : \mathbb{C}) \times \operatorname{Polynomial}.X^{4} + \operatorname{Polynomial}.\operatorname{C} (33749973 / 2000000 : \mathbb{C}) \times \operatorname{Polynomial}.X^{3} + \operatorname{Polynomial}.\operatorname{C} (- 382499181 / 20000000 : \mathbb{C}) \times \operatorname{Polynomial}.X^{2} + \operatorname{Polynomial}.\operatorname{C} (80999686800081 / 8000000000000 : \mathbb{C}) \times \operatorname{Polynomial}.X^{1} + \operatorname{Polynomial}.\operatorname{C} (- 16199902800081 / 8000000000000 : \mathbb{C}))$$

*Formalization.* `D5/S3/QuantumChannels/RenyiSufficiency/LikelihoodSpectrum.likelihoodPolynomial` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The complete parameter telescope and conclusion are displayed. Matrix products, transpose and conjTranspose have their Mathlib meanings; arrows indexed by Complex denote LinearMap.

**Theorem 1.17 (likelihoodPolynomial separable).**

$$\operatorname{likelihoodPolynomial}.\operatorname{Separable}$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumChannels/RenyiSufficiency/LikelihoodSpectrum.likelihoodPolynomial_separable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed polynomial has a Bézout identity with its derivative, so it has no repeated root.

**Definition 1.18 (likelihood).**

$$\forall (minus: \operatorname{Bool}), \operatorname{likelihood} minus = (\operatorname{matrixPower} \operatorname{sigma} (- 1 / 2) \times \operatorname{rho} minus (1 / 1000) \times \operatorname{matrixPower} \operatorname{sigma} (- 1 / 2))$$

*Formalization.* `D5/S3/QuantumChannels/RenyiSufficiency/LikelihoodSpectrum.likelihood` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The complete parameter telescope and conclusion are displayed. Matrix products, transpose and conjTranspose have their Mathlib meanings; arrows indexed by Complex denote LinearMap.

**Theorem 1.19 (likelihood hermitian).**

$$\forall (minus: \operatorname{Bool}), (\operatorname{likelihood} minus) .\operatorname{IsHermitian}$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumChannels/RenyiSufficiency/LikelihoodSpectrum.likelihood_hermitian` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The complete parameter telescope and conclusion are displayed. Matrix products, transpose and conjTranspose have their Mathlib meanings; arrows indexed by Complex denote LinearMap.

**Theorem 1.20 (likelihood simple spectrum).**

$$\forall (minus: \operatorname{Bool}), \operatorname{Function}.\operatorname{Injective} ((\operatorname{likelihood}_{\operatorname{hermitian}} minus) .\operatorname{eigenvalues})$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumChannels/RenyiSufficiency/LikelihoodSpectrum.likelihood_simple_spectrum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The eigenvalue projection uses likelihood_hermitian, the actual proof supplied in the Lean statement.

## References

- Truth anchor: `D5/S3/QuantumChannels/RenyiSufficiency/LikelihoodSpectrum.Dmin`
- Truth anchor: `D5/S3/QuantumChannels/RenyiSufficiency/LikelihoodSpectrum.DminFinite`
- Truth anchor: `D5/S3/QuantumChannels/RenyiSufficiency/LikelihoodSpectrum.Interconvertible`
- Truth anchor: `D5/S3/QuantumChannels/RenyiSufficiency/LikelihoodSpectrum.IsPTP`
- Truth anchor: `D5/S3/QuantumChannels/RenyiSufficiency/LikelihoodSpectrum.likelihood`
- Truth anchor: `D5/S3/QuantumChannels/RenyiSufficiency/LikelihoodSpectrum.likelihoodPolynomial`
- Truth anchor: `D5/S3/QuantumChannels/RenyiSufficiency/LikelihoodSpectrum.likelihoodPolynomial_separable`
- Truth anchor: `D5/S3/QuantumChannels/RenyiSufficiency/LikelihoodSpectrum.likelihood_hermitian`
- Truth anchor: `D5/S3/QuantumChannels/RenyiSufficiency/LikelihoodSpectrum.likelihood_simple_spectrum`
- Truth anchor: `D5/S3/QuantumChannels/RenyiSufficiency/LikelihoodSpectrum.matrixLog`
- Truth anchor: `D5/S3/QuantumChannels/RenyiSufficiency/LikelihoodSpectrum.matrixPower`
- Truth anchor: `D5/S3/QuantumChannels/RenyiSufficiency/LikelihoodSpectrum.matrixPower_diagonal`
- Truth anchor: `D5/S3/QuantumChannels/RenyiSufficiency/LikelihoodSpectrum.matrixPower_eq`
- Truth anchor: `D5/S3/QuantumChannels/RenyiSufficiency/LikelihoodSpectrum.mpow`
- Truth anchor: `D5/S3/QuantumChannels/RenyiSufficiency/LikelihoodSpectrum.rho`
- Truth anchor: `D5/S3/QuantumChannels/RenyiSufficiency/LikelihoodSpectrum.rho_hermitian`
- Truth anchor: `D5/S3/QuantumChannels/RenyiSufficiency/LikelihoodSpectrum.sigma`
- Truth anchor: `D5/S3/QuantumChannels/RenyiSufficiency/LikelihoodSpectrum.sigma_posDef`
- Truth anchor: `D5/S3/QuantumChannels/RenyiSufficiency/LikelihoodSpectrum.weightedRho`
- Truth anchor: `D5/S3/QuantumChannels/RenyiSufficiency/LikelihoodSpectrum.weightedRho_hermitian`
- Dependency: [D5/S3/Quantum/Dynamics/EntropyProductionCoherenceDeletionIdentity](../../Quantum/Dynamics/EntropyProductionCoherenceDeletionIdentity.md)
- Dependency: [D5/S3/QuantumChannels/CoPRelativeQuantumnessRefutation](../CoPRelativeQuantumnessRefutation.md)
