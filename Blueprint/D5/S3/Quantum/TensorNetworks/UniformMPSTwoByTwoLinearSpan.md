# The linear span of binary bond-two uniform matrix product states

## Abstract

The span of binary uniform matrix product states of bond dimension two has an exact parity-dependent quartic dimension.

**Definition 1.1 (The dimension formula for every positive length).**

$$(\operatorname{D5.S3.Quantum.TensorNetworks.UniformMPSTwoByTwoLinearSpan.claim}) \Leftrightarrow (\forall (n: \mathbb{N}), ((1 \le n) \to ((\operatorname{Nat.cast}\left(\operatorname{Module.finrank}\left(\mathbb{C}, \operatorname{Subtype}\left(\lambda (x: ((\operatorname{Fin}\left(n\right)) \to (\operatorname{Fin}\left(2\right))) \to (\mathbb{C})) \mapsto (x \in \operatorname{Submodule.span}\left(\mathbb{C}, \operatorname{D5.S3.Quantum.TensorNetworks.UniformMPSExpectedDimensionRefutation.uMPS}\left(2, 2, n\right)\right))\right)\right)\right): \mathbb{Q}) = \operatorname{ite}\left(\operatorname{Even}\left(n\right), \frac{((((\operatorname{Nat.cast}\left(n\right): \mathbb{Q})^{4}) - ((4) \cdot ((\operatorname{Nat.cast}\left(n\right): \mathbb{Q})^{2}))) + ((192) \cdot ((\operatorname{Nat.cast}\left(n\right): \mathbb{Q})))) + (192)}{192}, \frac{((((\operatorname{Nat.cast}\left(n\right): \mathbb{Q})^{4}) - ((10) \cdot ((\operatorname{Nat.cast}\left(n\right): \mathbb{Q})^{2}))) + ((192) \cdot ((\operatorname{Nat.cast}\left(n\right): \mathbb{Q})))) + (201)}{192}\right))))$$

*Formalization.* `D5/S3/Quantum/TensorNetworks/UniformMPSTwoByTwoLinearSpan.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Claudia De Lazzari; Harshit J. Motwani; Tim Seynnaeve (2022). *The Linear Span of Uniform Matrix Product States*. DOI: [10.3842/SIGMA.2022.099](https://doi.org/10.3842/SIGMA.2022.099). URL: <https://arxiv.org/abs/2204.10363v3>.

*Commentary.*

For each natural length n at least one, take the complex linear span of all tensors whose coefficient at a binary word is the trace of the corresponding ordered product of two complex 2 by 2 matrices. The formula asserts that its dimension is (n⁴ − 4n² + 192n + 192)/192 for even n and (n⁴ − 10n² + 192n + 201)/192 for odd n. The dimension and every occurrence of n in these two polynomials are cast from natural numbers to rational numbers. This is Conjecture 3.8 in sigma22-099.tex, lines 540–547, for positive lengths. The parametrization is given in lines 215–223; lines 224–225 distinguish its image from its closure. A finite-dimensional complex linear subspace is closed, so taking the span of the image gives the same span as taking the span of that closure.

**Theorem 1.2 (The exact dimension).**

$$\forall (n: \mathbb{N}), ((1 \le n) \to ((\operatorname{Nat.cast}\left(\operatorname{Module.finrank}\left(\mathbb{C}, \operatorname{Subtype}\left(\lambda (x: ((\operatorname{Fin}\left(n\right)) \to (\operatorname{Fin}\left(2\right))) \to (\mathbb{C})) \mapsto (x \in \operatorname{Submodule.span}\left(\mathbb{C}, \operatorname{D5.S3.Quantum.TensorNetworks.UniformMPSExpectedDimensionRefutation.uMPS}\left(2, 2, n\right)\right))\right)\right)\right): \mathbb{Q}) = \operatorname{ite}\left(\operatorname{Even}\left(n\right), \frac{((((\operatorname{Nat.cast}\left(n\right): \mathbb{Q})^{4}) - ((4) \cdot ((\operatorname{Nat.cast}\left(n\right): \mathbb{Q})^{2}))) + ((192) \cdot ((\operatorname{Nat.cast}\left(n\right): \mathbb{Q})))) + (192)}{192}, \frac{((((\operatorname{Nat.cast}\left(n\right): \mathbb{Q})^{4}) - ((10) \cdot ((\operatorname{Nat.cast}\left(n\right): \mathbb{Q})^{2}))) + ((192) \cdot ((\operatorname{Nat.cast}\left(n\right): \mathbb{Q})))) + (201)}{192}\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/UniformMPSTwoByTwoLinearSpan.result` (`✓ std3`). ∎

*Resolves.* `Problems/de-lazzari-motwani-seynnaeve-2022-umps-two-by-two-linear-span` (proved) by `D5/S3/Quantum/TensorNetworks/UniformMPSTwoByTwoLinearSpan.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"de-lazzari-motwani-seynnaeve-2022-umps-two-by-two-linear-span","declaration_gid":"D5/S3/Quantum/TensorNetworks/UniformMPSTwoByTwoLinearSpan.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Claudia De Lazzari; Harshit J. Motwani; Tim Seynnaeve (2022). *The Linear Span of Uniform Matrix Product States*. DOI: [10.3842/SIGMA.2022.099](https://doi.org/10.3842/SIGMA.2022.099). URL: <https://arxiv.org/abs/2204.10363v3>.

*Commentary.*

First compare the tensor span with the span of its coordinate functions. Let V be the space of complex functions on binary words of length n, and let S be the span of the trace tensors in V. Send a linear functional f on V to the function of a matrix pair p given by f(traceWord 2 2 n p). Expanding a tensor in the coordinate basis expresses this function as a linear combination of the trace coordinates. Conversely, each coordinate function is the image of the corresponding coordinate projection. Thus the image of this linear map is exactly the coordinate span, and its kernel is the annihilator of S. Rank-nullity, the dimension formula for an annihilator, and equality of the dimensions of V and its dual show that the tensor span and coordinate span have the same dimension.

Next count the exponent vectors e with five natural entries satisfying e(0) + e(1) + 2e(2) + 2e(3) + 2e(4) + 4 = n. Each entry is at most the weighted sum, so imposing the bound e(j) < n + 1 does not change this count. The number of five-entry vectors with ordinary sum k is the cardinality of the kth symmetric power of a five-element set: the binomial coefficient (k + 4 choose 4), or (k + 1)(k + 2)(k + 3)(k + 4)/24.

Divide the first two exponents by two and retain their residues modulo two. At length 2k + 5 their residues are opposite. Either choice of the first residue leaves a five-entry vector of ordinary sum k, giving twice (k + 4 choose 4). At length 2k + 6 the residues agree: the even-even case leaves ordinary sum k + 1, and the odd-odd case leaves ordinary sum k. This gives (k + 5 choose 4) + (k + 4 choose 4). The maps are inverted by doubling the first two entries and restoring their residues. There are no such exponent vectors below length four, and at length four only the zero vector occurs. Including these small lengths, polynomial simplification gives (n⁴ − 4n²)/192 exponent vectors for even n, and (n⁴ − 10n² + 9)/192 for odd n.

The trace-coordinate dimension theorem `D5/S3/Quantum/TensorNetworks/UniformMPSTwoByTwoTraceWords.coordinate_dimension` gives n + 1 plus exactly this exponent count. Its independent family consists of the n + 1 traces tr(XᵃYⁿ⁻ᵃ), together with the commutator-square invariant times every invariant monomial of weighted degree n − 4. Substitute that dimension in the equality of tensor and coordinate dimensions. Finally cast the natural-number sum to the rational numbers and add n + 1 to the two counts, obtaining the asserted even and odd formulas.

## References

- Truth anchor: `D5/S3/Quantum/TensorNetworks/UniformMPSTwoByTwoLinearSpan.claim`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/UniformMPSTwoByTwoLinearSpan.result`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/UniformMPSTwoByTwoTraceWords.coordinate_dimension`
- Dependency: [D5/S3/Quantum/TensorNetworks/UniformMPSTwoByTwoTraceWords](UniformMPSTwoByTwoTraceWords.md)
