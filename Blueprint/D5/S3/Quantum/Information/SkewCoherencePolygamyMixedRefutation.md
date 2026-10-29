# A mixed-state refutation of skew-coherence polygamy

## Abstract

A mixed state on two by three levels violates skew-coherence polygamy.

**Definition 1.1 (Skew-information coherence in a reference basis).**

$$\forall iota \in Type,\; ([\operatorname{Fintype}\left(iota\right)] [\operatorname{DecidableEq}\left(iota\right)] \forall rho \in \operatorname{Matrix}\left(iota, iota, \mathbb{C}\right),\; ((\operatorname{skewCoherence}\left(rho\right): \mathbb{R}) = ((1: \mathbb{R})) - (\sum_{k: iota} ((\operatorname{Complex.re}\left(\operatorname{CFC.sqrt}\left(rho\right)\left(k, k\right)\right))^{(2: \mathbb{N})}))))$$

*Formalization.* `D5/S3/Quantum/Information/SkewCoherencePolygamyMixedRefutation.skewCoherence` (`✓ std3`).

*Citation.* Chang-shui Yu (2017). *Quantum coherence via skew information and its polygamy*. DOI: [10.1103/PhysRevA.95.042337](https://doi.org/10.1103/PhysRevA.95.042337). URL: <https://arxiv.org/abs/1704.04871v1>.

*Commentary.*

For a finite reference index type and a complex matrix ρ, skewCoherence is one minus the sum over basis indices of the squared real diagonal entries of the positive continuous-functional-calculus square root of ρ. This is the diagonal reference-basis expression for the skew-information coherence in Yu's Lemma 1 (coherenceLy.tex, lines 170–178).

**Definition 1.2 (Mixed-state polygamy from total dimension six).**

$$\operatorname{claim}\left(\right) = \left(\forall m \in \mathbb{N},\; (\forall n \in \mathbb{N},\; (((6: \mathbb{N}) \le (m) \cdot (n)) \Rightarrow (\forall rho \in \operatorname{Matrix}\left(\operatorname{Prod}\left(\operatorname{Fin}\left(m\right), \operatorname{Fin}\left(n\right)\right), \operatorname{Prod}\left(\operatorname{Fin}\left(m\right), \operatorname{Fin}\left(n\right)\right), \mathbb{C}\right),\; ((\operatorname{D5.S3.Quantum.Information.SLDSpectralEnergy.IsDensity}\left(rho\right)) \Rightarrow (((1: \mathbb{R})) - (\operatorname{skewCoherence}\left(rho\right)) \le (((1: \mathbb{R})) - (\operatorname{skewCoherence}\left(\operatorname{D5.S3.Quantum.Information.PartialTraceMutualInformation.partialTraceRight}\left(rho\right)\right))) \cdot (((1: \mathbb{R})) - (\operatorname{skewCoherence}\left(\operatorname{D5.S3.Quantum.Information.PartialTraceMutualInformation.partialTraceLeft}\left(rho\right)\right))))))))\right)$$

*Formalization.* `D5/S3/Quantum/Information/SkewCoherencePolygamyMixedRefutation.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Chang-shui Yu (2017). *Quantum coherence via skew information and its polygamy*. DOI: [10.1103/PhysRevA.95.042337](https://doi.org/10.1103/PhysRevA.95.042337). URL: <https://arxiv.org/abs/1704.04871v1>.

*Commentary.*

For every pair of natural subsystem dimensions whose product is at least six, and every complex density matrix on their product index, the complement of skewCoherence of the joint state is at most the product of the two marginal complements. This is the repository's formal reading of the mixed-state conjecture stated in the source's discussion (coherenceLy.tex, lines 994–999) and Appendix D (lines 1370–1397).

**Theorem 1.3 (A two by three counterexample).**

$$\neg (\operatorname{claim}\left(\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/SkewCoherencePolygamyMixedRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/yu-2017-skew-coherence-mixed-state-polygamy` (refuted) by `D5/S3/Quantum/Information/SkewCoherencePolygamyMixedRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"yu-2017-skew-coherence-mixed-state-polygamy","declaration_gid":"D5/S3/Quantum/Information/SkewCoherencePolygamyMixedRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Chang-shui Yu (2017). *Quantum coherence via skew information and its polygamy*. DOI: [10.1103/PhysRevA.95.042337](https://doi.org/10.1103/PhysRevA.95.042337). URL: <https://arxiv.org/abs/1704.04871v1>.

*Commentary.*

Define the two-by-three witness matrix on Fin 2 × Fin 3 by the displayed rational entries: the Fin 3 coordinate 2 carries a two by two block with diagonal 1/4 and off-diagonal 3/17, while the other four coordinates have diagonal 1/8, entries 3/34 when exactly one local coordinate agrees, and 9/136 otherwise. Its two partial traces are the displayed two-by-two and three-by-three matrices.

The explicit radical matrix for the joint witness is positive semidefinite because it is a positive real scaling of a weighted sum of six vector outer products. Its square is the witness matrix, and the witness is a density matrix by the conjugate-transpose square identity and a direct trace computation. Direct finite sums give its two stated partial traces.

The explicit radical matrices for the two partial traces are positive semidefinite sums of vector outer products, and their squares are the corresponding partial traces. Uniqueness of the positive continuous-functional-calculus square root therefore identifies all three positive square roots used below.

Reading the diagonal entries of these three roots yields, in order, the joint complement (25/34 + (1/2 + sqrt(145)/34))/2, the two-by-two marginal complement 1/2 + sqrt(145)/34, and the three-by-three marginal complement ((1/2 + sqrt(145)/34) + 1)/2.

Subtracting the product of the two marginal values from the joint value gives (208 − 17 sqrt(145))/1156, which is positive because 17 sqrt(145) < 208. If the claim held, instantiate it at m = 2, n = 3 and the witness matrix. Replacing its two partial traces by the displayed marginals would make the strict violation nonpositive, a contradiction. Thus result proves the negation of claim.

## References

- Truth anchor: `D5/S3/Quantum/Information/SkewCoherencePolygamyMixedRefutation.claim`
- Truth anchor: `D5/S3/Quantum/Information/SkewCoherencePolygamyMixedRefutation.result`
- Truth anchor: `D5/S3/Quantum/Information/SkewCoherencePolygamyMixedRefutation.skewCoherence`
- Dependency: [D5/S3/Quantum/Information/PartialTraceMutualInformation](PartialTraceMutualInformation.md)
- Dependency: [D5/S3/Quantum/Information/SLDSpectralEnergy](SLDSpectralEnergy.md)
