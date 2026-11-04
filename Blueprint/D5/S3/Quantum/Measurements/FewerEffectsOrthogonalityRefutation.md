# Orthogonality with fewer effects than dimensions

## Abstract

Four effects on a ten-dimensional complex space disprove the proposed orthogonality minimum.

**Definition 1.1 (The square-root Gram matrix).**

$$\forall \left(n: \mathbb{N}\right), \left(\forall \left(d: \mathbb{N}\right), \left(\forall \left(f: \operatorname{Fin}\left(n\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)\right), \left(\left(\operatorname{D5.S3.Quantum.Measurements.FewerEffectsOrthogonalityRefutation.gram}\left(f\right): \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right)\right) = \lambda \left(i: \operatorname{Fin}\left(n\right)\right) \mapsto \left(\lambda \left(j: \operatorname{Fin}\left(n\right)\right) \mapsto \left(\operatorname{D5.S3.Quantum.GeneralizedFidelity.fidelity}\left(\left(1: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)\right), f\left(i\right), f\left(j\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Measurements/FewerEffectsOrthogonalityRefutation.gram` (`✓ std3`).

*Citation.* Yizhou Liu; John B. DeBrota (2021). *Relating measurement disturbance, information, and orthogonality*. DOI: [10.1103/PhysRevA.104.052216](https://doi.org/10.1103/PhysRevA.104.052216). URL: <https://arxiv.org/abs/2105.02074v2>.

*Commentary.*

For a family f of complex matrices, the (i,j) entry is GeneralizedFidelity.fidelity 1 (f i) (f j). At reference matrix 1, this is the trace of the product of CFC.sqrt (f i) and CFC.sqrt (f j). For positive semidefinite effects these are the positive square roots, giving the source's entry [S] at (i,j) and its Hilbert–Schmidt Gram matrix. The formula accepts arbitrary complex matrices without a positivity hypothesis. It expresses the definition in Section IV, apssamp.tex, lines 403–406.

**Definition 1.2 (Squared distance from the identity).**

$$\forall \left(n: \mathbb{N}\right), \left(\forall \left(d: \mathbb{N}\right), \left(\forall \left(f: \operatorname{Fin}\left(n\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)\right), \left(\left(\operatorname{D5.S3.Quantum.Measurements.FewerEffectsOrthogonalityRefutation.orthogonality}\left(f\right): \mathbb{R}\right) = \operatorname{D5.S3.Quantum.RandomCircuits.CHaarConcatenationNonmonotone.hsNormSq}\left(\left(\operatorname{D5.S3.Quantum.Measurements.FewerEffectsOrthogonalityRefutation.gram}\left(f\right)\right) - \left(\left(1: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Measurements/FewerEffectsOrthogonalityRefutation.orthogonality` (`✓ std3`).

*Citation.* Yizhou Liu; John B. DeBrota (2021). *Relating measurement disturbance, information, and orthogonality*. DOI: [10.1103/PhysRevA.104.052216](https://doi.org/10.1103/PhysRevA.104.052216). URL: <https://arxiv.org/abs/2105.02074v2>.

*Commentary.*

Orthogonality applies CHaarConcatenationNonmonotone.hsNormSq to the Gram matrix minus the n by n identity. This is the sum of the squared complex moduli of its entries, taking values in the real numbers: the source's squared Frobenius distance of S from the identity in Section IV, apssamp.tex, lines 410–420; the definition itself does not assume that f is a POVM.

**Definition 1.3 (Exactly n nonzero effects).**

$$\forall \left(n: \mathbb{N}\right), \left(\forall \left(d: \mathbb{N}\right), \left(\forall \left(f: \operatorname{Fin}\left(n\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)\right), \left(\left(\operatorname{D5.S3.Quantum.Measurements.FewerEffectsOrthogonalityRefutation.IsPOVMWith}\left(n, d, f\right)\right) \Leftrightarrow \left(\left(\forall \left(i: \operatorname{Fin}\left(n\right)\right), \left(\left(\operatorname{Matrix.PosSemidef}\left(f\left(i\right)\right)\right) \land \left(f\left(i\right) \ne \left(0: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)\right)\right)\right)\right) \land \left(\sum_{\left(i: \operatorname{Fin}\left(n\right)\right)} \left(f\left(i\right)\right) = \left(1: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Measurements/FewerEffectsOrthogonalityRefutation.IsPOVMWith` (`✓ std3`).

*Citation.* Yizhou Liu; John B. DeBrota (2021). *Relating measurement disturbance, information, and orthogonality*. DOI: [10.1103/PhysRevA.104.052216](https://doi.org/10.1103/PhysRevA.104.052216). URL: <https://arxiv.org/abs/2105.02074v2>.

*Commentary.*

Every matrix f i must be positive semidefinite and nonzero, and the sum of the effects must be the d by d identity. Distinct indices are not required to have distinct matrices. The POVM conditions occur in apssamp.tex, line 155; the nonvanishing condition is part of the conjecture at lines 795–797.

**Definition 1.4 (Consecutive coordinate blocks).**

$$\forall \left(n: \mathbb{N}\right), \left(\forall \left(d: \mathbb{N}\right), \left(\left(\operatorname{D5.S3.Quantum.Measurements.FewerEffectsOrthogonalityRefutation.construction}\left(n, d\right): \operatorname{Fin}\left(n\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)\right) = \lambda \left(i: \operatorname{Fin}\left(n\right)\right) \mapsto \left(\operatorname{Matrix.diagonal}\left(\lambda \left(k: \operatorname{Fin}\left(d\right)\right) \mapsto \left(\operatorname{ite}\left(\left(\left(\left(\left(\operatorname{Fin.val}\left(i\right): \mathbb{N}\right)\right) \cdot \left(\operatorname{Nat.div}\left(d, n\right)\right) \le \left(\operatorname{Fin.val}\left(k\right): \mathbb{N}\right)\right) \land \left(\left(\operatorname{Fin.val}\left(k\right): \mathbb{N}\right) < \operatorname{ite}\left(\left(\left(\operatorname{Fin.val}\left(i\right): \mathbb{N}\right) < \left(n\right) - \left(\left(1: \mathbb{N}\right)\right)\right), \left(\left(\left(\operatorname{Fin.val}\left(i\right): \mathbb{N}\right)\right) + \left(\left(1: \mathbb{N}\right)\right)\right) \cdot \left(\operatorname{Nat.div}\left(d, n\right)\right), d\right)\right)\right), \left(1: \mathbb{C}\right), \left(0: \mathbb{C}\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Measurements/FewerEffectsOrthogonalityRefutation.construction` (`✓ std3`).

*Citation.* Yizhou Liu; John B. DeBrota (2021). *Relating measurement disturbance, information, and orthogonality*. DOI: [10.1103/PhysRevA.104.052216](https://doi.org/10.1103/PhysRevA.104.052216). URL: <https://arxiv.org/abs/2105.02074v2>.

*Commentary.*

The diagonal entry at coordinate k is one precisely when k lies in the block assigned to i. All coordinate values are natural numbers, obtained explicitly by Fin.val, and Nat.div is natural-number division. Subtraction in n minus one is natural-number subtraction. For 0 < n < d, write d = an + b with a = d / n and 0 ≤ b < n. The first n minus one blocks have a coordinates each; the last has a + b. These disjoint blocks give the diagonal projectors described in Appendix C, apssamp.tex, lines 761–792. The formula defines a family for every natural n and d, including the empty family when n is zero.

**Definition 1.5 (The proposed minimum for fewer effects).**

$$\left(\operatorname{D5.S3.Quantum.Measurements.FewerEffectsOrthogonalityRefutation.claim}\right) \Leftrightarrow \left(\forall \left(n: \mathbb{N}\right), \left(\forall \left(d: \mathbb{N}\right), \left(\left(\left(0: \mathbb{N}\right) < n\right) \Rightarrow \left(\left(n < d\right) \Rightarrow \left(\forall \left(f: \operatorname{Fin}\left(n\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)\right), \left(\left(\operatorname{D5.S3.Quantum.Measurements.FewerEffectsOrthogonalityRefutation.IsPOVMWith}\left(n, d, f\right)\right) \Rightarrow \left(\operatorname{D5.S3.Quantum.Measurements.FewerEffectsOrthogonalityRefutation.orthogonality}\left(\operatorname{D5.S3.Quantum.Measurements.FewerEffectsOrthogonalityRefutation.construction}\left(n, d\right)\right) \le \operatorname{D5.S3.Quantum.Measurements.FewerEffectsOrthogonalityRefutation.orthogonality}\left(f\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Measurements/FewerEffectsOrthogonalityRefutation.claim` (`✓ std3`).

*Citation.* Yizhou Liu; John B. DeBrota (2021). *Relating measurement disturbance, information, and orthogonality*. DOI: [10.1103/PhysRevA.104.052216](https://doi.org/10.1103/PhysRevA.104.052216). URL: <https://arxiv.org/abs/2105.02074v2>.

*Commentary.*

For every pair of natural dimensions with 0 < n < d, the proposed block family is asserted to have orthogonality no greater than any POVM with exactly n nonzero effects. This is the universal statement corresponding to Conjecture 2 in Appendix C, apssamp.tex, lines 795–797, with the consecutive blocks above fixing the coordinate representation of its construction.

**Theorem 1.6 (Four effects in dimension ten refute the minimum).**

$$\neg \left(\operatorname{D5.S3.Quantum.Measurements.FewerEffectsOrthogonalityRefutation.claim}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurements/FewerEffectsOrthogonalityRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/liu-debrota-2021-fewer-effects-orthogonality` (refuted) by `D5/S3/Quantum/Measurements/FewerEffectsOrthogonalityRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"liu-debrota-2021-fewer-effects-orthogonality","declaration_gid":"D5/S3/Quantum/Measurements/FewerEffectsOrthogonalityRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Yizhou Liu; John B. DeBrota (2021). *Relating measurement disturbance, information, and orthogonality*. DOI: [10.1103/PhysRevA.104.052216](https://doi.org/10.1103/PhysRevA.104.052216). URL: <https://arxiv.org/abs/2105.02074v2>.

*Commentary.*

At n = 4 and d = 10, the proposed construction consists of coordinate projectors with ranks 2, 2, 2, 4. Each diagonal entry is zero or one. NMLWMeasuredFidelitySeparation.sqrt_diagonal computes the positive square root by taking the real square root of each nonnegative diagonal entry. Since the square roots of zero and one are zero and one, each matrix is its own positive square root.

Define another family F of diagonal projectors on the consecutive coordinate blocks [0,2), [2,4), [4,7), [7,10). Its ranks are 2, 2, 3, 3. The same diagonal square-root formula makes each of these matrices its own positive square root.

For the proposed construction, multiply the diagonal square roots and sum their diagonal entries to take the trace. Disjoint supports make the off-diagonal Gram entries zero; the diagonal entries are the block ranks. Thus its Gram matrix is diag(2,2,2,4). Applying the same entrywise calculation to F gives diag(2,2,3,3).

The family F has positive semidefinite effects because its diagonal entries are nonnegative. None is zero: a zero effect would have zero square root and zero diagonal Gram entry, contradicting its positive rank. Summing the four matrices entry by entry gives the identity, since the blocks partition all ten coordinates. Hence F satisfies IsPOVMWith 4 10.

Subtracting the four by four identity from the first Gram matrix and summing the squared complex moduli gives 1 + 1 + 1 + 9 = 12. For F the corresponding sum is 1 + 1 + 4 + 4 = 10. If claim held, its instance at n = 4, d = 10 and F would imply 12 ≤ 10, a contradiction. The proposed minimum is therefore false. This comparison does not assert the minimum among all such POVMs.

## References

- Truth anchor: `D5/S3/Quantum/Measurements/FewerEffectsOrthogonalityRefutation.IsPOVMWith`
- Truth anchor: `D5/S3/Quantum/Measurements/FewerEffectsOrthogonalityRefutation.claim`
- Truth anchor: `D5/S3/Quantum/Measurements/FewerEffectsOrthogonalityRefutation.construction`
- Truth anchor: `D5/S3/Quantum/Measurements/FewerEffectsOrthogonalityRefutation.gram`
- Truth anchor: `D5/S3/Quantum/Measurements/FewerEffectsOrthogonalityRefutation.orthogonality`
- Truth anchor: `D5/S3/Quantum/Measurements/FewerEffectsOrthogonalityRefutation.result`
- Dependency: [D5/S3/Quantum/GeneralizedFidelity](../GeneralizedFidelity.md)
- Dependency: [D5/S3/Quantum/Information/NMLWMeasuredFidelitySeparation](../Information/NMLWMeasuredFidelitySeparation.md)
- Dependency: [D5/S3/Quantum/RandomCircuits/CHaarConcatenationNonmonotone](../RandomCircuits/CHaarConcatenationNonmonotone.md)
