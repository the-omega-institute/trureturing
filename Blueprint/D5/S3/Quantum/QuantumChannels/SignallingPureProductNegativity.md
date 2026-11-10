# Pure product inputs detect signalling through PDM negativity

## Abstract

Every finite-dimensional signalling channel admits a pure product input with strictly positive PDM negativity.

**Definition 1.1 (The input-transposed Choi-Jamiolkowski matrix).**

$$\forall (\alpha: Type*), (\forall (\beta: Type*), (\forall [\operatorname{Fintype}\left(\alpha\right)] [\operatorname{DecidableEq}\left(\alpha\right)], (\forall (e: (\operatorname{Matrix}\left(\alpha, \alpha, \mathbb{C}\right)\to_{l[\mathbb{C}]} \operatorname{Matrix}\left(\beta, \beta, \mathbb{C}\right))), (\operatorname{cjMatrix}\left(e\right) = \sum_{i: \alpha} (\sum_{j: \alpha} (\operatorname{Matrix.kronecker}\left(\operatorname{Matrix.single}\left(j, i, (1: \mathbb{C})\right), e\left(\operatorname{Matrix.single}\left(i, j, (1: \mathbb{C})\right)\right)\right)))))))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/SignallingPureProductNegativity.cjMatrix` (`✓ std3`).

*Citation.* Xiangjing Liu; Yixian Qiu; Oscar Dahlsten; Vlatko Vedral (2025). *Quantum causal inference with extremely light touch*. DOI: [10.1038/s41534-024-00956-0](https://doi.org/10.1038/s41534-024-00956-0). URL: <https://arxiv.org/abs/2303.10544v4>.

*Commentary.*

For a complex linear map e between matrix spaces, cjMatrix is the sum of the transposed input matrix units tensored with their images under e. Thus its entry at row (i,r) and column (j,s) is the (r,s) entry of e applied to the matrix unit with row j and column i. This is the transposed-input convention of Eq. eq: CHOI, arxiv.tex lines 161–164 of arXiv:2303.10544v4. The definition applies to arbitrary finite input index types and arbitrary output index types.

**Definition 1.2 (The reduced two-time pseudo-density matrix).**

$$\forall (\alpha_{1}: Type*), (\forall (\beta_{1}: Type*), (\forall (\alpha_{2}: Type*), (\forall (\beta_{2}: Type*), (\forall [\operatorname{Fintype}\left(\alpha_{1}\right)] [\operatorname{DecidableEq}\left(\alpha_{1}\right)], (\forall [\operatorname{Fintype}\left(\beta_{1}\right)] [\operatorname{DecidableEq}\left(\beta_{1}\right)], (\forall [\operatorname{Fintype}\left(\alpha_{2}\right)] [\operatorname{DecidableEq}\left(\alpha_{2}\right)], (\forall [\operatorname{Fintype}\left(\beta_{2}\right)] [\operatorname{DecidableEq}\left(\beta_{2}\right)], (\forall (p: \operatorname{QuantumChannel}\left((\alpha_{1} \times \beta_{1}), (\alpha_{2} \times \beta_{2})\right)), (\forall (a: (\alpha_{1} \to \mathbb{C})), (\forall (b: (\beta_{1} \to \mathbb{C})), (\operatorname{pdmBA}\left(p, a, b\right) = \operatorname{let} (m: \operatorname{Matrix}\left(((\alpha_{1} \times \beta_{1}) \times (\alpha_{2} \times \beta_{2})), ((\alpha_{1} \times \beta_{1}) \times (\alpha_{2} \times \beta_{2})), \mathbb{C}\right)) := \operatorname{cjMatrix}\left(\operatorname{matrixAction}\left(\operatorname{QuantumChannel.toCompletelyPositiveMap}\left(p\right)\right)\right); (\operatorname{let} (\rho: \operatorname{Matrix}\left(((\alpha_{1} \times \beta_{1}) \times (\alpha_{2} \times \beta_{2})), ((\alpha_{1} \times \beta_{1}) \times (\alpha_{2} \times \beta_{2})), \mathbb{C}\right)) := \operatorname{Matrix.kronecker}\left(\operatorname{Matrix.kronecker}\left(\operatorname{Matrix.vecMulVec}\left(a, \operatorname{star}\left(a\right)\right), \operatorname{Matrix.vecMulVec}\left(b, \operatorname{star}\left(b\right)\right)\right), (1: \operatorname{Matrix}\left((\alpha_{2} \times \beta_{2}), (\alpha_{2} \times \beta_{2}), \mathbb{C}\right))\right); (\operatorname{partialTraceLeft}\left(\operatorname{Matrix.submatrix}\left(((\frac{1}{2}: \mathbb{C})) \cdot (((m) \cdot (\rho)) + ((\rho) \cdot (m))), \lambda (x: ((\alpha_{1} \times \beta_{2}) \times (\beta_{1} \times \alpha_{2}))) \mapsto (((x.1.1, x.2.1), (x.2.2, x.1.2))), \lambda (x: ((\alpha_{1} \times \beta_{2}) \times (\beta_{1} \times \alpha_{2}))) \mapsto (((x.1.1, x.2.1), (x.2.2, x.1.2)))\right)\right))))))))))))))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/SignallingPureProductNegativity.pdmBA` (`✓ std3`).

*Citation.* Xiangjing Liu; Yixian Qiu; Oscar Dahlsten; Vlatko Vedral (2025). *Quantum causal inference with extremely light touch*. DOI: [10.1038/s41534-024-00956-0](https://doi.org/10.1038/s41534-024-00956-0). URL: <https://arxiv.org/abs/2303.10544v4>.

*Commentary.*

Form the product of the rank-one operators associated with a and b, and tensor it with the output identity. The two-time pseudo-density matrix is half the sum of its two products with the input-transposed Choi-Jamiolkowski matrix. This is the Jordan product in Theorem thm: 2timesPDM, arxiv.tex lines 166–173 of arXiv:2303.10544v4. Reorder the factors as (A₁,B₂),(B₁,A₂) using the displayed index map, then trace out the first pair. The remaining matrix acts on B₁ together with A₂. The formula is defined for all vectors a and b; unit vectors give a pure product input. The finite dimensions need not be powers of two.

**Definition 1.3 (Signalling from B to A).**

$$\forall (\alpha_{1}: Type*), (\forall (\beta_{1}: Type*), (\forall (\alpha_{2}: Type*), (\forall (\beta_{2}: Type*), (\forall [\operatorname{Fintype}\left(\alpha_{1}\right)] [\operatorname{DecidableEq}\left(\alpha_{1}\right)], (\forall [\operatorname{Fintype}\left(\beta_{1}\right)] [\operatorname{DecidableEq}\left(\beta_{1}\right)], (\forall [\operatorname{Fintype}\left(\alpha_{2}\right)] [\operatorname{DecidableEq}\left(\alpha_{2}\right)], (\forall [\operatorname{Fintype}\left(\beta_{2}\right)] [\operatorname{DecidableEq}\left(\beta_{2}\right)], (\forall (p: \operatorname{QuantumChannel}\left((\alpha_{1} \times \beta_{1}), (\alpha_{2} \times \beta_{2})\right)), ((\operatorname{IsSignallingBA}\left(p\right)) \Leftrightarrow (\neg (\exists (t: \operatorname{QuantumChannel}\left(\alpha_{1}, \alpha_{2}\right)), (\forall (x: \operatorname{Matrix}\left((\alpha_{1} \times \beta_{1}), (\alpha_{1} \times \beta_{1}), \mathbb{C}\right)), (\operatorname{partialTraceRight}\left(\operatorname{matrixAction}\left(\operatorname{QuantumChannel.toCompletelyPositiveMap}\left(p\right)\right)\left(x\right)\right) = \operatorname{matrixAction}\left(\operatorname{QuantumChannel.toCompletelyPositiveMap}\left(t\right)\right)\left(\operatorname{partialTraceRight}\left(x\right)\right))))))))))))))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/SignallingPureProductNegativity.IsSignallingBA` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Xiangjing Liu; Yixian Qiu; Oscar Dahlsten; Vlatko Vedral (2025). *Quantum causal inference with extremely light touch*. DOI: [10.1038/s41534-024-00956-0](https://doi.org/10.1038/s41534-024-00956-0). URL: <https://arxiv.org/abs/2303.10544v4>.

*Commentary.*

A channel signals from B to A when its A₂ marginal cannot factor through the A₁ input marginal by any trace-preserving completely positive channel t. The factorization is required on every complex input matrix, including non-Hermitian matrices. This gives the precise marginal-factorization reading of signalling used here. The source discusses semicausal channels at arxiv.tex line 216; its pure product conjecture is at line 231.

**Theorem 1.4 (A pure product input with strictly positive negativity).**

$$\forall (\alpha_{1}: Type*), (\forall (\beta_{1}: Type*), (\forall (\alpha_{2}: Type*), (\forall (\beta_{2}: Type*), (\forall [\operatorname{Fintype}\left(\alpha_{1}\right)] [\operatorname{DecidableEq}\left(\alpha_{1}\right)], (\forall [\operatorname{Fintype}\left(\beta_{1}\right)] [\operatorname{DecidableEq}\left(\beta_{1}\right)], (\forall [\operatorname{Fintype}\left(\alpha_{2}\right)] [\operatorname{DecidableEq}\left(\alpha_{2}\right)], (\forall [\operatorname{Fintype}\left(\beta_{2}\right)] [\operatorname{DecidableEq}\left(\beta_{2}\right)], (\forall [\operatorname{Nonempty}\left(\alpha_{1}\right)] [\operatorname{Nonempty}\left(\beta_{1}\right)] [\operatorname{Nonempty}\left(\alpha_{2}\right)] [\operatorname{Nonempty}\left(\beta_{2}\right)], (\forall (p: \operatorname{QuantumChannel}\left((\alpha_{1} \times \beta_{1}), (\alpha_{2} \times \beta_{2})\right)), ((\operatorname{IsSignallingBA}\left(p\right)) \Rightarrow (\exists (a: (\alpha_{1} \to \mathbb{C})), (\exists (b: (\beta_{1} \to \mathbb{C})), ((\operatorname{dotProduct}\left(\operatorname{star}\left(a\right), a\right) = (1: \mathbb{C})) \land ((\operatorname{dotProduct}\left(\operatorname{star}\left(b\right), b\right) = (1: \mathbb{C})) \land ((0: \mathbb{R}) < (\operatorname{traceNorm}\left(\operatorname{Matrix.conjTranspose}\left(\operatorname{pdmBA}\left(p, a, b\right)\right)\right)) - ((1: \mathbb{R})))))))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/SignallingPureProductNegativity.result` (`✓ std3`). ∎

*Resolves.* `Problems/liu-qiu-dahlsten-vedral-2025-pure-product-signalling-negativity` (proved) by `D5/S3/Quantum/QuantumChannels/SignallingPureProductNegativity.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"liu-qiu-dahlsten-vedral-2025-pure-product-signalling-negativity","declaration_gid":"D5/S3/Quantum/QuantumChannels/SignallingPureProductNegativity.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Xiangjing Liu; Yixian Qiu; Oscar Dahlsten; Vlatko Vedral (2025). *Quantum causal inference with extremely light touch*. DOI: [10.1038/s41534-024-00956-0](https://doi.org/10.1038/s41534-024-00956-0). URL: <https://arxiv.org/abs/2303.10544v4>.

*Commentary.*

All four index types are finite and nonempty. Write Q for the channel p followed by tracing out B₂. For a unit vector a, let Eₐ send X to Q applied to the tensor product of the projector onto a with X. Call a map a replacement map if its value at X is the trace of X times one fixed matrix.

Tracing out a tensor factor is a quantum channel: its Kraus operators select the coordinates of that factor, and their adjoint products sum to the identity. Appending the maximally mixed state μ on B₁ is also a quantum channel. Its Kraus operators append one coordinate vector each, scaled by the complex image of the real square root of the inverse of the real cardinality of B₁. Their adjoint products again sum to the identity. The matrix μ is the identity scaled by the inverse of the complex image of that cardinality, and has trace one.

Unit pure projectors span the complex matrix space. Indeed, the spectral decomposition expresses each Hermitian matrix as a real linear combination of unit eigenvector projectors, with its real eigenvalues embedded in the complex scalars. Every matrix is its Hermitian real part plus the imaginary unit times its Hermitian imaginary part. Thus a complex linear map vanishing on all unit pure projectors vanishes everywhere.

Suppose every Eₐ were a replacement map. Compose the channel appending μ, p, and the channel discarding B₂ to obtain a channel t from A₁ to A₂. Evaluating the replacement identity at μ identifies its fixed output matrix with t applied to the projector onto a. The spanning argument then gives Q(Y tensor X) equal to the trace of X times t(Y) for every Y and X. Expanding arbitrary input matrices in product matrix units extends this identity to the required marginal factorization. This contradicts signalling. Consequently some unit a makes Eₐ a non-replacement map.

For any a and b, expansion of the Choi-Jamiolkowski entries and the two partial traces reduces the pseudo-density matrix to half of DM + MD, where M is the input-transposed Choi-Jamiolkowski matrix of Eₐ and D is the projector onto b tensored with the identity on A₂. The contraction over A₁ produces exactly Eₐ; the contraction over B₂ is its output partial trace.

A non-replacement map E admits orthogonal unit vectors b and c for which E applied to the rank-one operator c b* is nonzero. To see this, suppose all such images vanished. Distinct coordinate vectors first show that every off-diagonal matrix unit has zero image. For distinct indices i and j, use the normalized sum and difference of their coordinate vectors. Their cross image is one half of the difference of the two diagonal matrix-unit images, so those images must agree. Expansion in matrix units then makes E a replacement map, a contradiction. Apply this conclusion to the chosen Eₐ to obtain b and c.

Complete positivity makes p preserve Hermitian matrices. Decomposition into Hermitian real and imaginary parts consequently shows that it commutes with taking adjoints. The same holds for Eₐ, so M is Hermitian. Since D is Hermitian, half of DM + MD is Hermitian. Cyclicity of trace and contraction of the Choi-Jamiolkowski matrix identify its trace with the trace of Eₐ applied to the projector onto b. Trace preservation of p and the unit norms of a and b make this trace one.

Choose a nonzero (r,s) entry of Eₐ applied to c b*. Let v be c tensored with the s-th coordinate vector of A₂, and w be b tensored with its r-th coordinate vector. Orthogonality and normalization give Dv = 0 and Dw = w. The quadratic form of R = pdmBA(p,a,b) at v is therefore zero. If R were positive semidefinite, zero quadratic form would imply Rv = 0. However, pairing Rv with w gives one half of the chosen nonzero entry: the term containing Dv vanishes, while the other contracts M against b and c. This contradiction proves that R is not positive semidefinite.

Finally, the negative part of this Hermitian R is positive semidefinite and nonzero, and hence has strictly positive real trace. The Jordan decomposition expresses R as its positive part minus its negative part, whereas the trace norm is the sum of their real traces. Since the trace of R is one, its trace norm minus one is twice the strictly positive trace of the negative part. Hermiticity identifies R with its adjoint, giving exactly the displayed inequality. In the traceNorm convention the adjoint argument computes the real trace of the square root of RR*, as in Eq. eq: causmono at arxiv.tex lines 143–145. Thus the unit vectors a and b provide the required pure product input.

## References

- Truth anchor: `D5/S3/Quantum/QuantumChannels/SignallingPureProductNegativity.IsSignallingBA`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/SignallingPureProductNegativity.cjMatrix`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/SignallingPureProductNegativity.pdmBA`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/SignallingPureProductNegativity.result`
- Dependency: [D5/S3/Quantum/QuantumChannels/ElementaryChannelDivisibility](ElementaryChannelDivisibility.md)
- Dependency: [D5/S3/Quantum/Recovery/LiJiangPolarPairOptimalityRefutation](../Recovery/LiJiangPolarPairOptimalityRefutation.md)
