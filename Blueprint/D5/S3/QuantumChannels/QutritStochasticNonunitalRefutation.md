# A stochastic qutrit channel that is not unital

## Abstract

A completely positive trace-preserving qutrit map has the identity vector as a Choi eigenvector with eigenvalue one half, but does not preserve the identity matrix.

**Definition 1.1 (Stochastic channels).**

$$\forall (d: \mathbb{N}), \forall (Phi: \operatorname{MatrixMap}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)), \operatorname{IsStochastic}\left(Phi\right) = \left((\operatorname{IsCPTP}\left(Phi\right)) \land (\exists (lam: \mathbb{R}), (0 < lam) \land ((lam \le 1) \land (\operatorname{Matrix.mulVec}\left(((d: \mathbb{C})^{-1}) \cdot (fun (p: \operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right)) \mapsto fun (q: \operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right)) \mapsto Phi\left(\operatorname{Matrix.single}\left(p.2, q.2, 1\right), p.1, q.1\right)), fun (p: \operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right)) \mapsto if p.1 = p.2 then 1 else 0\right) = ((lam: \mathbb{C})) \cdot (fun (p: \operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right)) \mapsto if p.1 = p.2 then 1 else 0))))\right)$$

*Formalization.* `D5/S3/QuantumChannels/QutritStochasticNonunitalRefutation.IsStochastic` (`✓ std3`).

*Citation.* Matthew A. Graydon and Joshua Skanes-Norman and Joel J. Wallman (2022). *Designing Stochastic Channels*. URL: <https://arxiv.org/abs/2201.07156v1>.

*Commentary.*

Section II, page 2: "A stochastic channel is a CPTP map Φ ∈ B(B(Cᵈ)) such that for some 0 < λ ≤ 1" followed by Eq. (11), "J(Φ)col(1_d) = λcol(1_d)." Here MatrixMap is the complex-linear matrix-map type, and IsCPTP is the completely positive trace-preserving predicate. The normalized Choi state is d⁻¹ times MatrixMap.choi_matrix Phi, with the cast of d to C shown explicitly. Its row (j,i) and column (k,l) entry is d⁻¹ Phi(Matrix.single i l 1)(j,k), so the output factor comes first. The identity vector has value one on equal indices and zero otherwise. Matrix.mulVec and scalar multiplication give exactly Eq. (11). The real parameter lam satisfies both strict positivity and the upper bound one. The expression also accepts d=0; the question below is at positive dimension three.

**Definition 1.2 (The qutrit unitality question).**

$$claim = \forall (Phi: \operatorname{MatrixMap}\left(\operatorname{Fin}\left(3\right), \operatorname{Fin}\left(3\right), \mathbb{C}\right)), (\operatorname{IsStochastic}\left(Phi\right)) \Rightarrow (Phi\left(1\right) = 1)$$

*Formalization.* `D5/S3/QuantumChannels/QutritStochasticNonunitalRefutation.claim` (`✓ std3`).

*Citation.* Matthew A. Graydon and Joshua Skanes-Norman and Joel J. Wallman (2022). *Designing Stochastic Channels*. URL: <https://arxiv.org/abs/2201.07156v1>.

*Commentary.*

Section II, page 2: "We leave open the question of whether or not all stochastic channels are unital for d = 3." The universal quantifier ranges over every complex-linear map on 3 by 3 complex matrices. Stochasticity is Eq. (11) with complete positivity and trace preservation. Unitality is the equality Phi 1 = 1, where 1 is the identity matrix.

**Theorem 1.3 (A nonunital stochastic qutrit channel).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumChannels/QutritStochasticNonunitalRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/graydon-skanes-norman-wallman-2022-qutrit-stochastic-unitality` (refuted) by `D5/S3/QuantumChannels/QutritStochasticNonunitalRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"graydon-skanes-norman-wallman-2022-qutrit-stochastic-unitality","declaration_gid":"D5/S3/QuantumChannels/QutritStochasticNonunitalRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Matthew A. Graydon and Joshua Skanes-Norman and Joel J. Wallman (2022). *Designing Stochastic Channels*. URL: <https://arxiv.org/abs/2201.07156v1>.

*Commentary.*

Take Kraus matrices I/√2, diag(1,−1/2,−1/2)/√2, √(3/8) Matrix.single 0 1 1, and √(3/8) Matrix.single 0 2 1, with zero-based indices. Their right Gram sum is the identity, giving trace preservation, and their Kraus sum is completely positive. The resulting channel acts by Phi(X)₀₀ = X₀₀ + (3/8)(X₁₁+X₂₂), by multiplication by 1/4 on entries with exactly one index zero, and by multiplication by 5/8 on the lower-right 2 by 2 block. Its normalized Choi state sends the identity vector to one half of that vector. Yet Phi(I) = diag(7/4,5/8,5/8), whose first diagonal entry differs from one. Thus the qutrit question has a negative answer. Appendix A's unitality theorem for stochastic qubit channels concerns dimension two.

## References

- Truth anchor: `D5/S3/QuantumChannels/QutritStochasticNonunitalRefutation.IsStochastic`
- Truth anchor: `D5/S3/QuantumChannels/QutritStochasticNonunitalRefutation.claim`
- Truth anchor: `D5/S3/QuantumChannels/QutritStochasticNonunitalRefutation.result`
- Dependency: [D5/S3/Quantum/QuantumChannels/ProductUnitaryChoiSpectrum](../Quantum/QuantumChannels/ProductUnitaryChoiSpectrum.md)
- Dependency: [D5/S3/QuantumChannels/CoPRelativeQuantumnessRefutation](CoPRelativeQuantumnessRefutation.md)
- Dependency: [D5/S3/QuantumChannels/PassiveMemoryNonclassicalRefutation](PassiveMemoryNonclassicalRefutation.md)
