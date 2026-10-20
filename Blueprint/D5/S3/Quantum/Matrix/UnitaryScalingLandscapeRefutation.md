# A nonglobal local minimum of the unitary scaling landscape

## Abstract

A unitary matrix of order three has a nonglobal local scaling minimum.

Let Complex.I be the imaginary unit. A phase point x=(λ,ρ) consists of two real vectors indexed by Fin n. Diagonal unitary scaling gives B with entries Bⱼₖ=exp(((λⱼ+ρₖ : ℝ) : ℂ) Complex.I)Aⱼₖ. Write sum(B) for the sum of all entries, and Ψ_A(x)=landscape A x. The phase space has its usual product topology.

**Definition 1.1 (The sum after diagonal scaling).**

$$\forall (n: \mathbb{N}), \forall (A: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right)), \forall (\lambda: \operatorname{Fin}\left(n\right) \to \mathbb{R}), \forall (\rho: \operatorname{Fin}\left(n\right) \to \mathbb{R}), \operatorname{scalingSum}\left(A, (\lambda, \rho)\right) = \sum_{j: \operatorname{Fin}\left(n\right)}\sum_{k: \operatorname{Fin}\left(n\right)} \exp\left(\operatorname{Complex.ofReal}\left(\lambda\left(j\right) + \rho\left(k\right)\right) \cdot \operatorname{Complex.I}\right) \cdot \operatorname{A}\left(j, k\right)$$

*Formalization.* `D5/S3/Quantum/Matrix/UnitaryScalingLandscapeRefutation.scalingSum` (`✓ std3`).

*Citation.* Alexis De Vos; Stijn De Baerdemacker (2014). *Scaling a unitary matrix*. DOI: [10.1142/S1230161214500139](https://doi.org/10.1142/S1230161214500139). URL: <https://arxiv.org/abs/1401.7883v2>.

*Commentary.*

The double sum is sum(B). It is defined for every complex square matrix A and every pair of real phase vectors, without a unitarity hypothesis. De Vos and De Baerdemacker, Scaling a unitary matrix, Appendix B, define Bⱼₖ=exp(((λⱼ+ρₖ : ℝ) : ℂ) Complex.I)Aⱼₖ and use this sum in their landscape.

**Definition 1.2 (The scaling landscape).**

$$\forall (n: \mathbb{N}), \forall (A: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right)), \forall (x: (\operatorname{Fin}\left(n\right) \to \mathbb{R}) \times (\operatorname{Fin}\left(n\right) \to \mathbb{R})), \operatorname{landscape}\left(A, x\right) = (\operatorname{Nat.cast}\left(n\right): \mathbb{R})^{2} - \left\lVert \operatorname{scalingSum}\left(A, x\right) \right\rVert^{2}$$

*Formalization.* `D5/S3/Quantum/Matrix/UnitaryScalingLandscapeRefutation.landscape` (`✓ std3`).

*Citation.* Alexis De Vos; Stijn De Baerdemacker (2014). *Scaling a unitary matrix*. DOI: [10.1142/S1230161214500139](https://doi.org/10.1142/S1230161214500139). URL: <https://arxiv.org/abs/1401.7883v2>.

*Commentary.*

Appendix B defines Ψ_A(λ,ρ)=(n : ℝ)²−‖sum(B)‖². Here the same expression is defined for every A; the conjecture restricts A to the unitary group. The norm is the complex modulus.

**Definition 1.3 (Every local minimum is global).**

$$claim \Leftrightarrow (\forall (n: \mathbb{N}), \forall (A: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right)), (A \in \operatorname{Matrix.unitaryGroup}\left(\operatorname{Fin}\left(n\right), \mathbb{C}\right)) \Rightarrow (\forall (x: (\operatorname{Fin}\left(n\right) \to \mathbb{R}) \times (\operatorname{Fin}\left(n\right) \to \mathbb{R})), (\operatorname{IsLocalMin}\left(\operatorname{landscape}\left(A\right), x\right)) \Rightarrow (\forall (y: (\operatorname{Fin}\left(n\right) \to \mathbb{R}) \times (\operatorname{Fin}\left(n\right) \to \mathbb{R})), \operatorname{landscape}\left(A, x\right) \le \operatorname{landscape}\left(A, y\right))))$$

*Formalization.* `D5/S3/Quantum/Matrix/UnitaryScalingLandscapeRefutation.claim` (`✓ std3`).

*Citation.* Alexis De Vos; Stijn De Baerdemacker (2014). *Scaling a unitary matrix*. DOI: [10.1142/S1230161214500139](https://doi.org/10.1142/S1230161214500139). URL: <https://arxiv.org/abs/1401.7883v2>.

*Commentary.*

The assertion quantifies over every natural n, including zero, every complex n×n matrix A, and every phase point x. If A is unitary and x is a local minimum of Ψ_A in the sense of IsLocalMin, then Ψ_A(x)≤Ψ_A(y) for every phase point y. This expresses the absence of nonglobal local minima in Appendix B: “We conjecture that all these stationary points are either maxima or saddle points or global minima. In other words: we conjecture that no local minima exist.” Section 2 likewise conjectures that stationary points with 0<Ψ<(n : ℝ)² are saddle points. The separate assertion that global minima have Ψ=0 is not part of claim.

**Theorem 1.4 (A unitary counterexample of order three).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/UnitaryScalingLandscapeRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/de-vos-de-baerdemacker-2014-unitary-scaling-landscape-refutation` (refuted) by `D5/S3/Quantum/Matrix/UnitaryScalingLandscapeRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"de-vos-de-baerdemacker-2014-unitary-scaling-landscape-refutation","declaration_gid":"D5/S3/Quantum/Matrix/UnitaryScalingLandscapeRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Alexis De Vos; Stijn De Baerdemacker (2014). *Scaling a unitary matrix*. DOI: [10.1142/S1230161214500139](https://doi.org/10.1142/S1230161214500139). URL: <https://arxiv.org/abs/1401.7883v2>.

*Commentary.*

Take A=(1/34)[[−2,24,24],[24,1+17 Complex.I,1−17 Complex.I],[24,1−17 Complex.I,1+17 Complex.I]]. Direct multiplication gives A^* A=I, where A^* is the conjugate transpose, so A is unitary. At the zero phase point, sum(A)=49/17 and Ψ_A(0)=9−(49/17)²=200/289. Use one-based indices for the three coordinates. The set U={ (λ,ρ) : |ρ₂−ρ₃|<1/50 } is an open neighbourhood of zero. For zₖ=exp(((ρₖ : ℝ) : ℂ) Complex.I), the triangle inequality and the row-modulus estimate give ‖sum(B)‖≤Σⱼ‖(Az)ⱼ‖≤49/17 on U, hence Ψ_A≥200/289 there. Thus zero is a local minimum. For the comparison, choose ρ=(0,2π/3,π/3) and align the row phases by λⱼ=−arg((Az)ⱼ). The squared row moduli are 433/289, 217/289−√3/34, and 217/289+√3/34. Their moduli are at least 6/5, 4/5, and 8/9, respectively, so the aligned sum satisfies ‖sum(B)‖=Σⱼ‖(Az)ⱼ‖≥26/9>49/17. Consequently this phase point has Ψ_A<200/289, and the local minimum at zero is not global. This counterexample refutes the landscape conjecture of De Vos and De Baerdemacker. It does not refute the existence of a scaling with Ψ_A=0.

## References

- Truth anchor: `D5/S3/Quantum/Matrix/UnitaryScalingLandscapeRefutation.claim`
- Truth anchor: `D5/S3/Quantum/Matrix/UnitaryScalingLandscapeRefutation.landscape`
- Truth anchor: `D5/S3/Quantum/Matrix/UnitaryScalingLandscapeRefutation.result`
- Truth anchor: `D5/S3/Quantum/Matrix/UnitaryScalingLandscapeRefutation.scalingSum`
