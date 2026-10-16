# Three-row scalar spectral bound

## Abstract

Three boundary inequalities bound the squared mass of every ordered probability spectrum in every dimension at least 67.

For l:Fin N to the reals, indices inside prefix and tail sums mean their natural values embedded in Fin N. Thus the three rows compare the first three entries with the last six, the first six with the last ten, and the first entry with the last three. N is arbitrary subject to N at least 67, with zero entries and repeated eigenvalues allowed.

**Theorem 1.1 (Arbitrary-dimension squared-mass estimate).**

$$\forall (N:\mathbb{N}), (67\leq N)\Rightarrow \forall (l:Fin\left(N\right)\to \mathbb{R}), ((Antitone\left(l\right))\land (\forall (i:Fin\left(N\right)), 0\leq l\left(i\right))\land (\sum_{i:Fin\left(N\right)} l\left(i\right)=1)\land (\sum_{i:Fin\left(3\right)} l\left(i\right)\leq \sum_{i:Fin\left(6\right)} l\left(N-6+i\right))\land (\sum_{i:Fin\left(6\right)} l\left(i\right)\leq \sum_{i:Fin\left(10\right)} l\left(N-10+i\right))\land (l\left(0\right)\leq \sum_{i:Fin\left(3\right)} l\left(N-3+i\right)))\Rightarrow \sum_{i:Fin\left(N\right)} (l\left(i\right))^{2}\leq \frac{9\cdot ((N:\mathbb{N}):\mathbb{R})+16\cdot ((\left\lfloor\frac{3\cdot N+4}{8}\right\rfloor:\mathbb{N}):\mathbb{R})}{(3\cdot ((N:\mathbb{N}):\mathbb{R})+2\cdot ((\left\lfloor\frac{3\cdot N+4}{8}\right\rfloor:\mathbb{N}):\mathbb{R}))^{2}}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniformSpectralBound.three_row_scalar_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The integer t is natural-number division (3*N+4)/8, equivalently the displayed floor; its real coercion is taken only after that division. N-6, N-10 and N-3 are natural subtractions before indexing. All ratios in the bound are real divisions. The only hypotheses are the displayed ordering, nonnegativity, mass one and three boundary inequalities.

The proof first reconstructs the complete spectrum from its adjacent nonnegative gaps, including the final gap to zero. The middle gap mass is compressed to one step length j. Positive middle mass uses barycentric weights; zero middle mass uses a division-free reconstruction. Closure of the Euclidean norm-to-mass cone then transfers estimates for the fixed sixteen-slot boundary cone back to every original spectrum.

For the fixed cone, slack coordinates embed it in the nonnegative kernel of B. The general cofactor hull theorem supplies candidate vectors. A separate full-row padding argument applies to each individual candidate, keeps both signs and a positive scale, and produces an ordered support of size four. Checked witnesses cover all 3876 such supports. Their exact determinant identities, mixed-sign or zero alternatives and positively scaled catalog alternatives yield the 187 original ray identifiers; no assertion of 187 distinct extreme rays is needed.

The catalog rays are reconstructed with the original gap coordinates and slacks. Their exact mass and Gram moments satisfy polynomial certificate inequalities on the whole region N at least 67 and 6 at most j at most N-10. The boundary and middle envelopes are dominated by the rounded integer bulk value. The integer maximization argument retains t=(3*N+4)/8 rather than substituting a continuous maximizer. The resulting cone estimate is constructed in the proof, and trace one together with the square-root identity gives the squared-mass conclusion.

Dependencies are the nonnegative-kernel circuit and cofactor completeness results, the cofactor cross identity in CofactorKernel, the shared spectral norm, step-synthesis, gap and additive-closure lemmas in UniformSpectralBound, and pinned Mathlib linear algebra, convex cone and Euclidean norm results. Circuit decomposition is the fully nonnegative specialization of Mueller and Regensburger's Theorem 3 on elementary vectors of subspace cones, as described in NonnegativeKernelCircuit. Signed cofactor kernels and barycentric mixtures are classical constructions; the particular three-row compression, catalog soundness chain and uniform rounded estimate are derived here. This statement concerns scalar spectra. Connecting these inequalities to a physical APPT model, constructing an attaining state, and identifying a purity supremum require further results.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniformSpectralBound.three_row_scalar_bound`
- Dependency: [D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniform/FullRowCofactor](QuadbitUniform/FullRowCofactor.md)
- Dependency: [D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniform/RaySoundness](QuadbitUniform/RaySoundness.md)
- Dependency: [D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniform/ScalarConeSoundness](QuadbitUniform/ScalarConeSoundness.md)
- Dependency: [D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniform/SpectrumCompression](QuadbitUniform/SpectrumCompression.md)
