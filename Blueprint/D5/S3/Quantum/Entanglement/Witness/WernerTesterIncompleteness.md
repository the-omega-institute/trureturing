# Werner states undetected by all complex testers

## Abstract

Entangled Werner states with dimension at least three and parameter between one over the dimension and one half escape every pair of complex testers.

**Definition 1.1 (Complex testers).**

$$\forall (d: \mathbb{N}), (\forall (n: \mathbb{N}), (\forall (e: (\operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)) \to_{l}[\mathbb{C}] (\operatorname{EuclideanSpace}\left(\mathbb{C}, \operatorname{Fin}\left(n\right)\right))), (\operatorname{D5.S3.Quantum.Entanglement.Witness.WernerTesterIncompleteness.IsTester}\left(e\right) = \left((\forall (x: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)), (\left\lVert \operatorname{DFunLike.coe}\left(e\right)\left(x\right) \right\rVert \le \operatorname{D5.S3.Quantum.Foundation.FiniteTraceDistance.traceNorm}\left(x\right))) \land (\exists (x: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)), ((x \ne (0: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right))) \land (\left\lVert \operatorname{DFunLike.coe}\left(e\right)\left(x\right) \right\rVert = \operatorname{D5.S3.Quantum.Foundation.FiniteTraceDistance.traceNorm}\left(x\right))))\right))))$$

*Formalization.* `D5/S3/Quantum/Entanglement/Witness/WernerTesterIncompleteness.IsTester` (`✓ std3`).

*Citation.* Maria Anastasia Jivulescu; Cécilia Lancien; Ion Nechita (2022). *Multipartite Entanglement Detection Via Projective Tensor Norms*. DOI: [10.1007/s00023-022-01187-9](https://doi.org/10.1007/s00023-022-01187-9). URL: <https://arxiv.org/abs/2010.06365v1>.

*Commentary.*

A complex tester is a complex linear contraction from the trace norm to the Euclidean norm that attains equality at a nonzero matrix. This expresses operator norm exactly one. The source defines complex testers in main.tex, lines 340–352, and the trace norm in lines 288–290.

**Definition 1.2 (Pure tensors of Euclidean outputs).**

$$\forall (n_{1}: \mathbb{N}), (\forall (n_{2}: \mathbb{N}), (\forall (a: \operatorname{EuclideanSpace}\left(\mathbb{C}, \operatorname{Fin}\left(n_{1}\right)\right)), (\forall (b: \operatorname{EuclideanSpace}\left(\mathbb{C}, \operatorname{Fin}\left(n_{2}\right)\right)), (\operatorname{D5.S3.Quantum.Entanglement.Witness.WernerTesterIncompleteness.tensorPair}\left(a, b\right) = \operatorname{PiTensorProduct.tprod}\left(\mathbb{C}, \operatorname{Bool.rec}\left(a, b\right)\right)))))$$

*Formalization.* `D5/S3/Quantum/Entanglement/Witness/WernerTesterIncompleteness.tensorPair` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Maria Anastasia Jivulescu; Cécilia Lancien; Ion Nechita (2022). *Multipartite Entanglement Detection Via Projective Tensor Norms*. DOI: [10.1007/s00023-022-01187-9](https://doi.org/10.1007/s00023-022-01187-9). URL: <https://arxiv.org/abs/2010.06365v1>.

*Commentary.*

The two Euclidean vectors form a pure tensor in the Bool-indexed PiTensorProduct. The false factor has dimension n₁ and the true factor has dimension n₂. Bool.rec selects the first or second vector accordingly. This tensor space carries the bundled projective norm.

**Definition 1.3 (The tensor product image).**

$$\forall (d_{1}: \mathbb{N}), (\forall (d_{2}: \mathbb{N}), (\forall (n_{1}: \mathbb{N}), (\forall (n_{2}: \mathbb{N}), (\forall (e_{1}: (\operatorname{Matrix}\left(\operatorname{Fin}\left(d_{1}\right), \operatorname{Fin}\left(d_{1}\right), \mathbb{C}\right)) \to_{l}[\mathbb{C}] (\operatorname{EuclideanSpace}\left(\mathbb{C}, \operatorname{Fin}\left(n_{1}\right)\right))), (\forall (e_{2}: (\operatorname{Matrix}\left(\operatorname{Fin}\left(d_{2}\right), \operatorname{Fin}\left(d_{2}\right), \mathbb{C}\right)) \to_{l}[\mathbb{C}] (\operatorname{EuclideanSpace}\left(\mathbb{C}, \operatorname{Fin}\left(n_{2}\right)\right))), (\forall (\rho: \operatorname{Matrix}\left((\operatorname{Fin}\left(d_{1}\right) \times \operatorname{Fin}\left(d_{2}\right)), (\operatorname{Fin}\left(d_{1}\right) \times \operatorname{Fin}\left(d_{2}\right)), \mathbb{C}\right)), (\operatorname{D5.S3.Quantum.Entanglement.Witness.WernerTesterIncompleteness.testerImage}\left(e_{1}, e_{2}, \rho\right) = \sum_{i: \operatorname{Fin}\left(d_{1}\right)} (\sum_{j: \operatorname{Fin}\left(d_{2}\right)} (\sum_{k: \operatorname{Fin}\left(d_{1}\right)} (\sum_{l: \operatorname{Fin}\left(d_{2}\right)} ((\rho\left((i, j), (k, l)\right)) \cdot (\operatorname{D5.S3.Quantum.Entanglement.Witness.WernerTesterIncompleteness.tensorPair}\left(\operatorname{DFunLike.coe}\left(e_{1}\right)\left(\operatorname{Matrix.single}\left(i, k, (1: \mathbb{C})\right)\right), \operatorname{DFunLike.coe}\left(e_{2}\right)\left(\operatorname{Matrix.single}\left(j, l, (1: \mathbb{C})\right)\right)\right)))))))))))))$$

*Formalization.* `D5/S3/Quantum/Entanglement/Witness/WernerTesterIncompleteness.testerImage` (`✓ std3`).

*Citation.* Maria Anastasia Jivulescu; Cécilia Lancien; Ion Nechita (2022). *Multipartite Entanglement Detection Via Projective Tensor Norms*. DOI: [10.1007/s00023-022-01187-9](https://doi.org/10.1007/s00023-022-01187-9). URL: <https://arxiv.org/abs/2010.06365v1>.

*Commentary.*

Expand the input in tensor products of matrix units and apply the two linear maps to the respective factors. Sum the resulting pure tensors with the input entries as complex scalar coefficients. The output belongs to the Bool-indexed PiTensorProduct of the two Euclidean spaces. DFunLike.coe displays evaluation of a linear map as a function. This is the bipartite tensor product action described in main.tex, lines 377–380.

**Definition 1.4 (Separable density matrices).**

$$\forall (d_{1}: \mathbb{N}), (\forall (d_{2}: \mathbb{N}), (\forall (\rho: \operatorname{Matrix}\left((\operatorname{Fin}\left(d_{1}\right) \times \operatorname{Fin}\left(d_{2}\right)), (\operatorname{Fin}\left(d_{1}\right) \times \operatorname{Fin}\left(d_{2}\right)), \mathbb{C}\right)), (\operatorname{D5.S3.Quantum.Entanglement.Witness.WernerTesterIncompleteness.Separable}\left(\rho\right) = \left(\rho \in \operatorname{convexHull}\left(\mathbb{R}, \{(\sigma: \operatorname{Matrix}\left((\operatorname{Fin}\left(d_{1}\right) \times \operatorname{Fin}\left(d_{2}\right)), (\operatorname{Fin}\left(d_{1}\right) \times \operatorname{Fin}\left(d_{2}\right)), \mathbb{C}\right)) \mid (\exists (\rho_{1}: \operatorname{Matrix}\left(\operatorname{Fin}\left(d_{1}\right), \operatorname{Fin}\left(d_{1}\right), \mathbb{C}\right)), (\exists (\rho_{2}: \operatorname{Matrix}\left(\operatorname{Fin}\left(d_{2}\right), \operatorname{Fin}\left(d_{2}\right), \mathbb{C}\right)), ((\operatorname{Matrix.PosSemidef}\left(\rho_{1}\right)) \land ((\operatorname{Matrix.trace}\left(\rho_{1}\right) = (1: \mathbb{C})) \land ((\operatorname{Matrix.PosSemidef}\left(\rho_{2}\right)) \land ((\operatorname{Matrix.trace}\left(\rho_{2}\right) = (1: \mathbb{C})) \land (\sigma = \operatorname{Matrix.kroneckerMap}\left(\lambda (x1: \mathbb{C}) \mapsto (\lambda (x2: \mathbb{C}) \mapsto ((x1) \cdot (x2))), \rho_{1}, \rho_{2}\right))))))))\}\right)\right))))$$

*Formalization.* `D5/S3/Quantum/Entanglement/Witness/WernerTesterIncompleteness.Separable` (`✓ std3`).

*Citation.* Maria Anastasia Jivulescu; Cécilia Lancien; Ion Nechita (2022). *Multipartite Entanglement Detection Via Projective Tensor Norms*. DOI: [10.1007/s00023-022-01187-9](https://doi.org/10.1007/s00023-022-01187-9). URL: <https://arxiv.org/abs/2010.06365v1>.

*Commentary.*

A matrix is separable when it lies in the real convex hull of tensor products of positive semidefinite matrices of trace one. The factors may have different dimensions. The source discusses mixed states and their separable decompositions in main.tex, lines 288–309.

**Definition 1.5 (The Werner mixture).**

$$\forall (d: \mathbb{N}), (\forall (\mu: \mathbb{R}), (\operatorname{D5.S3.Quantum.Entanglement.Witness.WernerTesterIncompleteness.werner}\left(d, \mu\right) = ((\frac{\mu}{((\operatorname{Nat.cast}\left(d\right): \mathbb{R})) \cdot (((\operatorname{Nat.cast}\left(d\right): \mathbb{R})) + ((1: \mathbb{R})))}) \cdot (((1: \operatorname{Matrix}\left((\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right)), (\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right)), \mathbb{C}\right))) + (\operatorname{Equiv.Perm.permMatrix}\left(\mathbb{C}, \operatorname{Equiv.prodComm}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right)\right)\right)))) + ((\frac{((1: \mathbb{R})) - (\mu)}{((\operatorname{Nat.cast}\left(d\right): \mathbb{R})) \cdot (((\operatorname{Nat.cast}\left(d\right): \mathbb{R})) - ((1: \mathbb{R})))}) \cdot (((1: \operatorname{Matrix}\left((\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right)), (\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right)), \mathbb{C}\right))) - (\operatorname{Equiv.Perm.permMatrix}\left(\mathbb{C}, \operatorname{Equiv.prodComm}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right)\right)\right))))))$$

*Formalization.* `D5/S3/Quantum/Entanglement/Witness/WernerTesterIncompleteness.werner` (`✓ std3`).

*Citation.* Maria Anastasia Jivulescu; Cécilia Lancien; Ion Nechita (2022). *Multipartite Entanglement Detection Via Projective Tensor Norms*. DOI: [10.1007/s00023-022-01187-9](https://doi.org/10.1007/s00023-022-01187-9). URL: <https://arxiv.org/abs/2010.06365v1>.

*Commentary.*

The coordinate swap F exchanges the two factors. The Werner matrix is the weighted sum of I + F and I − F with the displayed normalizing denominators. For d greater than one and parameter between zero and one, these are mixtures of the normalized symmetric and antisymmetric projections. The formula is from main.tex, line 946. Nat.cast explicitly includes d in the reals; the dots between real coefficients and complex matrices denote real scalar multiplication.

**Definition 1.6 (The normalized identity matrix).**

$$\forall (d: \mathbb{N}), ((\operatorname{D5.S3.Quantum.Entanglement.Witness.WernerTesterIncompleteness.designAverage}\left(d\right): \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)) = (\frac{1}{(\operatorname{Nat.cast}\left(d\right): \mathbb{R})}) \cdot ((1: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right))))$$

*Formalization.* `D5/S3/Quantum/Entanglement/Witness/WernerTesterIncompleteness.designAverage` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Maria Anastasia Jivulescu; Cécilia Lancien; Ion Nechita (2022). *Multipartite Entanglement Detection Via Projective Tensor Norms*. DOI: [10.1007/s00023-022-01187-9](https://doi.org/10.1007/s00023-022-01187-9). URL: <https://arxiv.org/abs/2010.06365v1>.

*Commentary.*

The normalized identity on d coordinates is the identity matrix scaled by the real reciprocal of d.

**Definition 1.7 (Completeness without permuting indices).**

$$\operatorname{D5.S3.Quantum.Entanglement.Witness.WernerTesterIncompleteness.claim} = \forall (d_{1}: \mathbb{N}), (\forall (d_{2}: \mathbb{N}), (\forall (\rho: \operatorname{Matrix}\left((\operatorname{Fin}\left(d_{1}\right) \times \operatorname{Fin}\left(d_{2}\right)), (\operatorname{Fin}\left(d_{1}\right) \times \operatorname{Fin}\left(d_{2}\right)), \mathbb{C}\right)), ((\operatorname{Matrix.PosSemidef}\left(\rho\right)) \Rightarrow ((\operatorname{Matrix.trace}\left(\rho\right) = (1: \mathbb{C})) \Rightarrow ((\neg \operatorname{D5.S3.Quantum.Entanglement.Witness.WernerTesterIncompleteness.Separable}\left(\rho\right)) \Rightarrow (\exists (n_{1}: \mathbb{N}), (\exists (n_{2}: \mathbb{N}), (\exists (e_{1}: (\operatorname{Matrix}\left(\operatorname{Fin}\left(d_{1}\right), \operatorname{Fin}\left(d_{1}\right), \mathbb{C}\right)) \to_{l}[\mathbb{C}] (\operatorname{EuclideanSpace}\left(\mathbb{C}, \operatorname{Fin}\left(n_{1}\right)\right))), (\exists (e_{2}: (\operatorname{Matrix}\left(\operatorname{Fin}\left(d_{2}\right), \operatorname{Fin}\left(d_{2}\right), \mathbb{C}\right)) \to_{l}[\mathbb{C}] (\operatorname{EuclideanSpace}\left(\mathbb{C}, \operatorname{Fin}\left(n_{2}\right)\right))), ((\operatorname{D5.S3.Quantum.Entanglement.Witness.WernerTesterIncompleteness.IsTester}\left(e_{1}\right)) \land ((\operatorname{D5.S3.Quantum.Entanglement.Witness.WernerTesterIncompleteness.IsTester}\left(e_{2}\right)) \land ((1: \mathbb{R}) < \left\lVert \operatorname{D5.S3.Quantum.Entanglement.Witness.WernerTesterIncompleteness.testerImage}\left(e_{1}, e_{2}, \rho\right) \right\rVert))))))))))))$$

*Formalization.* `D5/S3/Quantum/Entanglement/Witness/WernerTesterIncompleteness.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Maria Anastasia Jivulescu; Cécilia Lancien; Ion Nechita (2022). *Multipartite Entanglement Detection Via Projective Tensor Norms*. DOI: [10.1007/s00023-022-01187-9](https://doi.org/10.1007/s00023-022-01187-9). URL: <https://arxiv.org/abs/2010.06365v1>.

*Commentary.*

The bipartite completeness assertion asks for two complex testers detecting each entangled density matrix, in arbitrary natural dimensions, by a projective norm strictly greater than one. No permutation of the input indices is allowed. This is the bipartite reading of the question in main.tex, line 1365; a bipartite counterexample also disproves the assertion for all numbers of parties.

**Theorem 1.8 (An undetected entangled family).**

$$\forall (d: \mathbb{N}), (\forall (\mu: \mathbb{R}), (((3: \mathbb{N}) \le d) \Rightarrow ((\frac{(1: \mathbb{R})}{(\operatorname{Nat.cast}\left(d\right): \mathbb{R})} \le \mu) \Rightarrow ((\mu < \frac{(1: \mathbb{R})}{(2: \mathbb{R})}) \Rightarrow ((\operatorname{Matrix.PosSemidef}\left(\operatorname{D5.S3.Quantum.Entanglement.Witness.WernerTesterIncompleteness.werner}\left(d, \mu\right)\right)) \land ((\operatorname{Matrix.trace}\left(\operatorname{D5.S3.Quantum.Entanglement.Witness.WernerTesterIncompleteness.werner}\left(d, \mu\right)\right) = (1: \mathbb{C})) \land ((\neg \operatorname{D5.S3.Quantum.Entanglement.Witness.WernerTesterIncompleteness.Separable}\left(\operatorname{D5.S3.Quantum.Entanglement.Witness.WernerTesterIncompleteness.werner}\left(d, \mu\right)\right)) \land (\forall (n_{1}: \mathbb{N}), (\forall (n_{2}: \mathbb{N}), (\forall (e_{1}: (\operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)) \to_{l}[\mathbb{C}] (\operatorname{EuclideanSpace}\left(\mathbb{C}, \operatorname{Fin}\left(n_{1}\right)\right))), (\forall (e_{2}: (\operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)) \to_{l}[\mathbb{C}] (\operatorname{EuclideanSpace}\left(\mathbb{C}, \operatorname{Fin}\left(n_{2}\right)\right))), ((\forall (x: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)), (\left\lVert \operatorname{DFunLike.coe}\left(e_{1}\right)\left(x\right) \right\rVert \le \operatorname{D5.S3.Quantum.Foundation.FiniteTraceDistance.traceNorm}\left(x\right))) \Rightarrow ((\forall (x: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)), (\left\lVert \operatorname{DFunLike.coe}\left(e_{2}\right)\left(x\right) \right\rVert \le \operatorname{D5.S3.Quantum.Foundation.FiniteTraceDistance.traceNorm}\left(x\right))) \Rightarrow (\left\lVert \operatorname{D5.S3.Quantum.Entanglement.Witness.WernerTesterIncompleteness.testerImage}\left(e_{1}, e_{2}, \operatorname{D5.S3.Quantum.Entanglement.Witness.WernerTesterIncompleteness.werner}\left(d, \mu\right)\right) \right\rVert \le (1: \mathbb{R})))))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/WernerTesterIncompleteness.werner_family` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Maria Anastasia Jivulescu; Cécilia Lancien; Ion Nechita (2022). *Multipartite Entanglement Detection Via Projective Tensor Norms*. DOI: [10.1007/s00023-022-01187-9](https://doi.org/10.1007/s00023-022-01187-9). URL: <https://arxiv.org/abs/2010.06365v1>.

*Commentary.*

For d at least three and parameter in the interval from 1/d inclusive to 1/2 exclusive, the Werner matrix is positive semidefinite, has trace one, and is entangled. Every pair of complex linear contractions has image projective norm at most one, whether or not the contractions attain norm one.

**Theorem 1.9 (Complex testers are incomplete).**

$$\neg \operatorname{D5.S3.Quantum.Entanglement.Witness.WernerTesterIncompleteness.claim}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/WernerTesterIncompleteness.result` (`✓ std3`). ∎

*Resolves.* `Problems/jivulescu-lancien-nechita-2022-werner-tester-incompleteness` (refuted) by `D5/S3/Quantum/Entanglement/Witness/WernerTesterIncompleteness.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"jivulescu-lancien-nechita-2022-werner-tester-incompleteness","declaration_gid":"D5/S3/Quantum/Entanglement/Witness/WernerTesterIncompleteness.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Maria Anastasia Jivulescu; Cécilia Lancien; Ion Nechita (2022). *Multipartite Entanglement Detection Via Projective Tensor Norms*. DOI: [10.1007/s00023-022-01187-9](https://doi.org/10.1007/s00023-022-01187-9). URL: <https://arxiv.org/abs/2010.06365v1>.

*Commentary.*

Let F be the coordinate swap. For positive semidefinite matrices a and b, the real part of the trace of F(a ⊗ b) equals the real part of the trace of ab and is nonnegative. This real linear functional remains nonnegative on the convex hull of product density matrices, hence on every separable matrix.

The tensor product image of any finite sum of product matrices is the sum of the pure tensors of their images. If the two families of image vectors each have sum of squared norms at most one, Cauchy–Schwarz bounds the sum of the products of their norms by one. The triangle inequality and the projective seminorm bound on each pure tensor then bound the bundled norm of the sum by one.

For positive d, use a finite ensemble of rank-one projectors P indexed by the computational basis and by all d-tuples of fourth roots of unity. Each basis projector has weight 1/(d(d + 1)); each projector onto a flat unit vector with those phases has weight d/((d + 1)4^d). The weights are nonnegative and sum to one, and every projector is positive semidefinite with trace one. The fourth-root moment identity gives the weighted tensor second moment (I + F)/(d(d + 1)). Taking a partial trace of this identity gives the weighted mean m = I/d.

The swap is Hermitian and squares to the identity, so I + F and I − F are positive semidefinite. Their traces are d squared plus d and d squared minus d, since the trace of F is d. The Werner mixture is consequently positive semidefinite with trace one whenever d > 1 and 0 ≤ μ ≤ 1. Its swap trace is 2μ − 1. For μ < 1/2 this is negative, contradicting the nonnegativity of the swap trace on separable matrices.

Center each ensemble projector by subtracting m. Expanding the centered tensor second moment using its mean and total weight expresses the Werner matrix as m ⊗ m minus c times the weighted sum of the tensors (P − m) ⊗ (P − m), where c = (d + 1 − 2μd)/(d − 1).

For any trace-norm-to-Euclidean contraction e, the squared norm of e(m) plus the weighted sum of the squared norms of e(P − m) equals the weighted sum of the squared norms of e(P). This follows by expanding squared differences and using the weighted mean. Each P has trace norm one, so contraction and the total weight one bound that sum by one. On 1/d ≤ μ < 1/2, elementary inequalities give 0 ≤ c ≤ 1.

In the product decomposition of the Werner matrix, take m on both sides for one summand. For each projector of weight w, take the two factors to be the centered projector scaled by the square root of cw and its negative. Their tensor product is minus cw times the tensor square of the centered projector. The preceding squared-norm estimate, together with 0 ≤ c ≤ 1, bounds each family's sum of squared image norms by one. Applying the tensor product image identity and the Cauchy–Schwarz bound proves the uniform projective norm estimate. For d ≥ 3 the parameter interval also ensures 0 ≤ μ ≤ 1, so positivity, unit trace, entanglement, and this estimate hold together.

Finally take d = 3 and μ = 1/3. Completeness would supply testers with image projective norm strictly greater than one for this entangled density matrix. Each tester is a contraction, so the uniform estimate makes that same norm at most one, a contradiction.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/WernerTesterIncompleteness.IsTester`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/WernerTesterIncompleteness.Separable`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/WernerTesterIncompleteness.claim`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/WernerTesterIncompleteness.designAverage`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/WernerTesterIncompleteness.result`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/WernerTesterIncompleteness.tensorPair`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/WernerTesterIncompleteness.testerImage`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/WernerTesterIncompleteness.werner`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/WernerTesterIncompleteness.werner_family`
- Dependency: [D5/S3/Quantum/Entanglement/AbsoluteSeparability/GurvitsBarnumMoments](../AbsoluteSeparability/GurvitsBarnumMoments.md)
- Dependency: [D5/S3/Quantum/Foundation/FiniteTraceDistance](../../Foundation/FiniteTraceDistance.md)
- Dependency: [D5/S3/Quantum/RandomCircuits/CHaarConcatenationNonmonotone](../../RandomCircuits/CHaarConcatenationNonmonotone.md)
- Dependency: [D5/S3/QuantumBounds/NonlocalityDepthQuantumBound](../../../QuantumBounds/NonlocalityDepthQuantumBound.md)
