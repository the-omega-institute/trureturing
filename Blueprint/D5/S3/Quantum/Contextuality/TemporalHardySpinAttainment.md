# Temporal Hardy attainment for every positive spin

## Abstract

For every positive integer n, spin-n/2 measurements attain temporal Hardy success probability one quarter.

Work on ℂ^(n+1) in the standard basis e_k = |n/2 − k⟩, with ℏ = 1. The matrices Jx(n), Jy(n) and Jz(n) are the spin-n/2 components in this basis. Fin(n+1) indexes the coordinates from zero through n. A matrix asterisk denotes the conjugate transpose, and a real scalar in a complex matrix or vector expression is included into ℂ.

**Definition 1.1 (A scaled outer product).**

$$\forall (n: \mathbb{N}), (\forall (w: (\operatorname{Fin}\left((n + 1)\right) \to \mathbb{C})), (\forall (d: \mathbb{R}), (\operatorname{ray}\left(n, w, d\right) = (d: \mathbb{C})^{-1} \cdot \operatorname{vecMulVec}\left(w, \operatorname{star}\left(w\right)\right))))$$

*Formalization.* `D5/S3/Quantum/Contextuality/TemporalHardySpinAttainment.ray` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The outer product of w with its conjugate is scaled by the inverse of the real normalization parameter, included into ℂ.

**Definition 1.2 (A spin component in a real direction).**

$$\forall (n: \mathbb{N}), (\forall (u: (\operatorname{Fin}\left(3\right) \to \mathbb{R})), (\operatorname{spinComponent}\left(n, u\right) = \operatorname{ofReal}\left(u\left(0\right)\right) \cdot \operatorname{Jx}\left(n\right) + \operatorname{ofReal}\left(u\left(1\right)\right) \cdot \operatorname{Jy}\left(n\right) + \operatorname{ofReal}\left(u\left(2\right)\right) \cdot \operatorname{Jz}\left(n\right)))$$

*Formalization.* `D5/S3/Quantum/Contextuality/TemporalHardySpinAttainment.spinComponent` (`✓ std3`).

*Citation.* Sujit K. Choudhary; Sandeep K. Goyal; Thomas Konrad; Sibasish Ghosh (2013). *Persistence of Hardy's nonlocality in time*. URL: <https://arxiv.org/abs/1302.5296v1>.

*Commentary.*

The spin component u·S is u₀Jx(n) + u₁Jy(n) + u₂Jz(n). This definition allows every real direction u; the unit-length conditions for the four measurement directions appear in claim.

**Definition 1.3 (The projector onto an outcome eigenspace).**

$$\forall (n: \mathbb{N}), (\forall (M: \operatorname{Matrix}\left(\operatorname{Fin}\left((n + 1)\right), \operatorname{Fin}\left((n + 1)\right), \mathbb{C}\right)), (\forall (\pi: \operatorname{Matrix}\left(\operatorname{Fin}\left((n + 1)\right), \operatorname{Fin}\left((n + 1)\right), \mathbb{C}\right)), (\forall (a: \mathbb{R}), ((\operatorname{IsSpectralProjector}\left(M, \pi, a\right)) \Leftrightarrow ((\pi^{2} = \pi) \land ((\pi^{*} = \pi) \land (\forall (v: (\operatorname{Fin}\left((n + 1)\right) \to \mathbb{C})), ((\pi \cdot v = v) \Leftrightarrow (M \cdot v = \operatorname{ofReal}\left(a\right) \cdot v)))))))))$$

*Formalization.* `D5/S3/Quantum/Contextuality/TemporalHardySpinAttainment.IsSpectralProjector` (`✓ std3`).

*Citation.* Sujit K. Choudhary; Sandeep K. Goyal; Thomas Konrad; Sibasish Ghosh (2013). *Persistence of Hardy's nonlocality in time*. URL: <https://arxiv.org/abs/1302.5296v1>.

*Commentary.*

For complex matrices M and Π and a real outcome a, IsSpectralProjector requires Π to be idempotent and self-adjoint, with fixed vectors exactly the a-eigenvectors of M. Thus its range is the whole a-eigenspace, including any degeneracy, as required for a Lüders measurement in Section III.

**Definition 1.4 (The sequential expectation).**

$$\forall (n: \mathbb{N}), (\forall (\psi: (\operatorname{Fin}\left((n + 1)\right) \to \mathbb{C})), (\forall (\pi_{X}: \operatorname{Matrix}\left(\operatorname{Fin}\left((n + 1)\right), \operatorname{Fin}\left((n + 1)\right), \mathbb{C}\right)), (\forall (\pi_{Y}: \operatorname{Matrix}\left(\operatorname{Fin}\left((n + 1)\right), \operatorname{Fin}\left((n + 1)\right), \mathbb{C}\right)), (\operatorname{seqProb}\left(\psi, \pi_{X}, \pi_{Y}\right) = \langle \psi \mid (\pi_{X} \cdot \pi_{Y} \cdot \pi_{X}) \mid \psi \rangle))))$$

*Formalization.* `D5/S3/Quantum/Contextuality/TemporalHardySpinAttainment.seqProb` (`✓ std3`).

*Citation.* Sujit K. Choudhary; Sandeep K. Goyal; Thomas Konrad; Sibasish Ghosh (2013). *Persistence of Hardy's nonlocality in time*. URL: <https://arxiv.org/abs/1302.5296v1>.

*Commentary.*

The expression is defined for every complex vector ψ and every pair of complex matrices Π_X and Π_Y. For a unit state and orthogonal outcome projectors it is the sequential probability in Section III: first measure X and then Y. The complementary outcome uses I − Π.

**Definition 1.5 (Attainability with spin measurements).**

$$(\operatorname{claim}) \Leftrightarrow (\forall (n: \mathbb{N}), ((1 \le n) \Rightarrow (\exists (u_{A1}: (\operatorname{Fin}\left(3\right) \to \mathbb{R})), (\exists (u_{A2}: (\operatorname{Fin}\left(3\right) \to \mathbb{R})), (\exists (u_{B1}: (\operatorname{Fin}\left(3\right) \to \mathbb{R})), (\exists (u_{B2}: (\operatorname{Fin}\left(3\right) \to \mathbb{R})), (\exists (a_{1}: \mathbb{R}), (\exists (a_{2}: \mathbb{R}), (\exists (b_{1}: \mathbb{R}), (\exists (b_{2}: \mathbb{R}), (\exists (\pi_{A1}: \operatorname{Matrix}\left(\operatorname{Fin}\left((n + 1)\right), \operatorname{Fin}\left((n + 1)\right), \mathbb{C}\right)), (\exists (\pi_{A2}: \operatorname{Matrix}\left(\operatorname{Fin}\left((n + 1)\right), \operatorname{Fin}\left((n + 1)\right), \mathbb{C}\right)), (\exists (\pi_{B1}: \operatorname{Matrix}\left(\operatorname{Fin}\left((n + 1)\right), \operatorname{Fin}\left((n + 1)\right), \mathbb{C}\right)), (\exists (\pi_{B2}: \operatorname{Matrix}\left(\operatorname{Fin}\left((n + 1)\right), \operatorname{Fin}\left((n + 1)\right), \mathbb{C}\right)), (\exists (\psi: (\operatorname{Fin}\left((n + 1)\right) \to \mathbb{C})), ((\sum_{(i: \operatorname{Fin}\left(3\right))} (\left(u_{A1}\right)\left(i\right))^{2} = 1) \land ((\sum_{(i: \operatorname{Fin}\left(3\right))} (\left(u_{A2}\right)\left(i\right))^{2} = 1) \land ((\sum_{(i: \operatorname{Fin}\left(3\right))} (\left(u_{B1}\right)\left(i\right))^{2} = 1) \land ((\sum_{(i: \operatorname{Fin}\left(3\right))} (\left(u_{B2}\right)\left(i\right))^{2} = 1) \land ((\operatorname{IsSpectralProjector}\left(\operatorname{spinComponent}\left(n, u_{A1}\right), \pi_{A1}, a_{1}\right)) \land ((\operatorname{IsSpectralProjector}\left(\operatorname{spinComponent}\left(n, u_{A2}\right), \pi_{A2}, a_{2}\right)) \land ((\operatorname{IsSpectralProjector}\left(\operatorname{spinComponent}\left(n, u_{B1}\right), \pi_{B1}, b_{1}\right)) \land ((\operatorname{IsSpectralProjector}\left(\operatorname{spinComponent}\left(n, u_{B2}\right), \pi_{B2}, b_{2}\right)) \land ((\langle \psi, \psi \rangle = 1) \land ((\operatorname{seqProb}\left(\psi, \pi_{A1}, \pi_{B1}\right) = 0) \land ((\operatorname{seqProb}\left(\psi, (1 - \pi_{A1}), \pi_{B2}\right) = 0) \land ((\operatorname{seqProb}\left(\psi, \pi_{A2}, (1 - \pi_{B1})\right) = 0) \land (\operatorname{seqProb}\left(\psi, \pi_{A2}, \pi_{B2}\right) = \frac{1}{4}))))))))))))))))))))))))))))$$

*Formalization.* `D5/S3/Quantum/Contextuality/TemporalHardySpinAttainment.claim` (`✓ std3`).

*Citation.* Sujit K. Choudhary; Sandeep K. Goyal; Thomas Konrad; Sibasish Ghosh (2013). *Persistence of Hardy's nonlocality in time*. URL: <https://arxiv.org/abs/1302.5296v1>.

*Commentary.*

For every n ≥ 1, there are four real unit directions, four real outcomes, their full spectral projectors, and a unit complex state ψ satisfying the three zero conditions and attaining success probability 1/4. These are the temporal Hardy conditions of Sections II and III, with the attainable value conjectured for every spin in the conclusion and Appendix B. The assertion is attainability; the dimension-independent upper bound is established in Section III of the source.

**Theorem 1.6 (A construction attaining one quarter for every positive spin).**

$$\operatorname{claim}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Contextuality/TemporalHardySpinAttainment.result` (`✓ std3`). ∎

*Resolves.* `Problems/choudhary-goyal-konrad-ghosh-2013-temporal-hardy-spin-attainment` (proved) by `D5/S3/Quantum/Contextuality/TemporalHardySpinAttainment.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"choudhary-goyal-konrad-ghosh-2013-temporal-hardy-spin-attainment","declaration_gid":"D5/S3/Quantum/Contextuality/TemporalHardySpinAttainment.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Sujit K. Choudhary; Sandeep K. Goyal; Thomas Konrad; Sibasish Ghosh (2013). *Persistence of Hardy's nonlocality in time*. URL: <https://arxiv.org/abs/1302.5296v1>.

*Commentary.*

Fix n ≥ 1 and put r = √(2^{1/n} − 1), so r > 0 and (1 + r²)^n = 2. Let b_k = √C(n,k) r^k for 0 ≤ k ≤ n, where C(n,k) is the binomial coefficient, and set ψ = b − e₀. The binomial theorem gives ⟨b,b⟩ = 2, while b₀ = 1; hence ⟨ψ,ψ⟩ = 1.

Set a = (1 − r²)/(1 + r²), c = 2r/(1 + r²), and S = a Jz(n) + c Jx(n). Then a² + c² = 1. The spin ladder identities give S b = (n/2)b. The superdiagonal entries of S are strictly positive. Its tridiagonal recurrence forces any eigenvector whose first coordinate vanishes to be zero. Consequently its n/2-eigenspace is exactly span{b}. The diagonal entries of Jz(n) are n/2 − k, so its n/2-eigenspace is exactly span{e₀}. Both eigenspaces are one-dimensional.

Choose A₁ = B₂ = Jz(n), A₂ = B₁ = S, and all four outcomes n/2. Their spectral projectors are P = |e₀⟩⟨e₀| and Q = |b⟩⟨b|/2, respectively. Since Pψ = 0, Qψ = b/2, Pb = e₀ and Qe₀ = b/2, the probabilities ⟨ψ|PQP|ψ⟩, ⟨ψ|(I − P)P(I − P)|ψ⟩ and ⟨ψ|Q(I − Q)Q|ψ⟩ all vanish, whereas ⟨ψ|QPQ|ψ⟩ = 1/4. This realizes the spin-measurement attainability conjecture stated in the conclusion and Appendix B.

## References

- Truth anchor: `D5/S3/Quantum/Contextuality/TemporalHardySpinAttainment.IsSpectralProjector`
- Truth anchor: `D5/S3/Quantum/Contextuality/TemporalHardySpinAttainment.claim`
- Truth anchor: `D5/S3/Quantum/Contextuality/TemporalHardySpinAttainment.ray`
- Truth anchor: `D5/S3/Quantum/Contextuality/TemporalHardySpinAttainment.result`
- Truth anchor: `D5/S3/Quantum/Contextuality/TemporalHardySpinAttainment.seqProb`
- Truth anchor: `D5/S3/Quantum/Contextuality/TemporalHardySpinAttainment.spinComponent`
- Dependency: [D5/S3/Quantum/Dynamics/TridiagonalSweeps/FinitePathDynamics](../Dynamics/TridiagonalSweeps/FinitePathDynamics.md)
- Dependency: [D5/S3/Quantum/Entanglement/PrecessionSpinOneSeparableBound](../Entanglement/PrecessionSpinOneSeparableBound.md)
