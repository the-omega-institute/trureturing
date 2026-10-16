# Orthogonal reduction for conditional hockey-stick ratios

## Abstract

Conditional hockey-stick ratio sets equal their orthogonal subsets and are independent of gamma at least one.

QuantumChannel(A,B) is the completely positive, trace-preserving map from A to B of FiniteStateChannel. The reference coordinate is the first factor of R times A. Matrix.PosSemidef means positive semidefinite, Matrix.trace is the complex trace, and RHLinalg.rtrace is its real part. The notation X+ denotes CFC.posPart(X). Anonymous brackets supply the displayed type-class structures; Type allows arbitrary universes except that the types in ratios and claim lie in Type 0.

**Theorem 1.1 (Positive semidefinite dependent block matrices).**

$$\forall (iota: \operatorname{Type}), [\operatorname{Fintype}\left(iota\right)] [\operatorname{DecidableEq}\left(iota\right)] \forall (kappa: iota \to \operatorname{Type}), [\forall (i: iota), \operatorname{Fintype}\left(kappa\left(i\right)\right)] [\forall (i: iota), \operatorname{DecidableEq}\left(kappa\left(i\right)\right)] \forall (M: \forall (i: iota), \operatorname{Matrix}\left(kappa\left(i\right), kappa\left(i\right), \mathbb{C}\right)), (\forall (i: iota), \operatorname{Matrix.PosSemidef}\left(M\left(i\right)\right)) \Rightarrow (\operatorname{Matrix.PosSemidef}\left(\operatorname{Matrix.blockDiagonal}'\left(M\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/ConditionalHockeyStickOrthogonalReduction.posSemidef_blockDiagonal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite family of finite square complex matrices, positivity of every block implies positivity of Matrix.blockDiagonal'. Each block may have its own index type, including an empty one.

**Theorem 1.2 (Scalar multiplication commutes with the right partial trace).**

$$\forall (S: \operatorname{Type}), \forall (R: \operatorname{Type}), \forall (A: \operatorname{Type}), [\operatorname{DistribSMul}\left(S, \mathbb{C}\right)] [\operatorname{Fintype}\left(A\right)] \forall (c: S), \forall (X: \operatorname{Matrix}\left(R \times A, R \times A, \mathbb{C}\right)), \operatorname{PartialTraceMutualInformation.partialTraceRight}\left(c \cdot (X)\right) = c \cdot (\operatorname{PartialTraceMutualInformation.partialTraceRight}\left(X\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/ConditionalHockeyStickOrthogonalReduction.partialTraceRight_smul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

PartialTraceMutualInformation.partialTraceRight sums the diagonal A coordinate and retains R. Any scalar action on C distributing over addition commutes with this finite sum. Neither finiteness of R nor decidable equality on R is assumed.

**Definition 1.3 (Trace of the positive part).**

$$\forall (n: \operatorname{Type}), [\operatorname{Fintype}\left(n\right)] [\operatorname{DecidableEq}\left(n\right)] \forall (X: \operatorname{Matrix}\left(n, n, \mathbb{C}\right)), \operatorname{D5.S3.Quantum.Divergence.ConditionalHockeyStickOrthogonalReduction.posTrace}\left(X\right) = \operatorname{RHLinalg.rtrace}\left(X^{+}\right)$$

*Formalization.* `D5/S3/Quantum/Divergence/ConditionalHockeyStickOrthogonalReduction.posTrace` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Christoph Hirche; Ian George; Theshani Nuradha; Mark M. Wilde (2026). *Conditional contraction coefficients and their applications to quantum networks*. URL: <https://arxiv.org/abs/2608.27171v1>.

*Commentary.*

posTrace(X) is the real trace of the CFC positive part X+. For Hermitian X this is the sum of its positive eigenvalues, with multiplicity. The definition itself accepts every square matrix.

**Definition 1.4 (Hockey-stick divergence).**

$$\forall (n: \operatorname{Type}), [\operatorname{Fintype}\left(n\right)] [\operatorname{DecidableEq}\left(n\right)] \forall (gamma: \mathbb{R}), \forall (rho: \operatorname{Matrix}\left(n, n, \mathbb{C}\right)), \forall (sigma: \operatorname{Matrix}\left(n, n, \mathbb{C}\right)), \operatorname{D5.S3.Quantum.Divergence.ConditionalHockeyStickOrthogonalReduction.E}\left(gamma, rho, sigma\right) = \operatorname{D5.S3.Quantum.Divergence.ConditionalHockeyStickOrthogonalReduction.posTrace}\left(rho - gamma \cdot (sigma)\right)$$

*Formalization.* `D5/S3/Quantum/Divergence/ConditionalHockeyStickOrthogonalReduction.E` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Christoph Hirche; Ian George; Theshani Nuradha; Mark M. Wilde (2026). *Conditional contraction coefficients and their applications to quantum networks*. URL: <https://arxiv.org/abs/2608.27171v1>.

*Commentary.*

For density matrices rho and sigma, E_gamma(rho||sigma) is Tr(rho - gamma sigma)+, the hockey-stick divergence of Eq. (5.1). The matrix definition permits every real gamma and every pair of square matrices; positivity and normalization enter the ratio set.

**Definition 1.5 (Reference amplification of a quantum channel).**

$$\forall (A: \operatorname{Type}), [\operatorname{Fintype}\left(A\right)] [\operatorname{DecidableEq}\left(A\right)] \forall (B: \operatorname{Type}), [\operatorname{Fintype}\left(B\right)] [\operatorname{DecidableEq}\left(B\right)] \forall (R: \operatorname{Type}), [\operatorname{Fintype}\left(R\right)] [\operatorname{DecidableEq}\left(R\right)] \forall (N: \operatorname{FiniteStateChannel.QuantumChannel}\left(A, B\right)), \forall (X: \operatorname{Matrix}\left(R \times A, R \times A, \mathbb{C}\right)), \operatorname{D5.S3.Quantum.Divergence.ConditionalHockeyStickOrthogonalReduction.amp}\left(N, X\right) = \operatorname{CStarMatrix.ofMatrix.symm}\left(\operatorname{FiniteDiamondDistance.referenceLinear}\left(N, \operatorname{CStarMatrix.ofMatrix}\left(X\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Divergence/ConditionalHockeyStickOrthogonalReduction.amp` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Christoph Hirche; Ian George; Theshani Nuradha; Mark M. Wilde (2026). *Conditional contraction coefficients and their applications to quantum networks*. URL: <https://arxiv.org/abs/2608.27171v1>.

*Commentary.*

amp(N,X) is (id_R tensor N)(X). CStarMatrix.ofMatrix converts ordinary matrices to the C*-matrix coordinates of FiniteDiamondDistance.referenceLinear, and its inverse returns the output matrix on R times B. Every reference block is acted on by the same channel N.

**Definition 1.6 (Conditional hockey-stick gap).**

$$\forall (R: \operatorname{Type}), [\operatorname{Fintype}\left(R\right)] [\operatorname{DecidableEq}\left(R\right)] \forall (A: \operatorname{Type}), [\operatorname{Fintype}\left(A\right)] [\operatorname{DecidableEq}\left(A\right)] \forall (gamma: \mathbb{R}), \forall (rho: \operatorname{Matrix}\left(R \times A, R \times A, \mathbb{C}\right)), \forall (sigma: \operatorname{Matrix}\left(R \times A, R \times A, \mathbb{C}\right)), \operatorname{D5.S3.Quantum.Divergence.ConditionalHockeyStickOrthogonalReduction.gap}\left(gamma, rho, sigma\right) = \operatorname{D5.S3.Quantum.Divergence.ConditionalHockeyStickOrthogonalReduction.E}\left(gamma, rho, sigma\right) - \operatorname{D5.S3.Quantum.Divergence.ConditionalHockeyStickOrthogonalReduction.E}\left(gamma, \operatorname{PartialTraceMutualInformation.partialTraceRight}\left(rho\right), \operatorname{PartialTraceMutualInformation.partialTraceRight}\left(sigma\right)\right)$$

*Formalization.* `D5/S3/Quantum/Divergence/ConditionalHockeyStickOrthogonalReduction.gap` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Christoph Hirche; Ian George; Theshani Nuradha; Mark M. Wilde (2026). *Conditional contraction coefficients and their applications to quantum networks*. URL: <https://arxiv.org/abs/2608.27171v1>.

*Commentary.*

The conditional gap is E_gamma(rho||sigma) minus E_gamma(rho_R||sigma_R), where both reference marginals are taken by PartialTraceMutualInformation.partialTraceRight. Trace preservation makes the reference marginals of the amplified outputs equal the input reference marginals.

**Definition 1.7 (Ratios over all finite reference systems).**

$$\forall (A: \operatorname{Type}), [\operatorname{Fintype}\left(A\right)] [\operatorname{DecidableEq}\left(A\right)] \forall (B: \operatorname{Type}), [\operatorname{Fintype}\left(B\right)] [\operatorname{DecidableEq}\left(B\right)] \forall (N: \operatorname{FiniteStateChannel.QuantumChannel}\left(A, B\right)), \forall (gamma: \mathbb{R}), \forall (orth: \operatorname{Bool}), \operatorname{D5.S3.Quantum.Divergence.ConditionalHockeyStickOrthogonalReduction.ratios}\left(N, gamma, orth\right) = \{(x: \mathbb{R}) \mid \exists (R: \operatorname{Type}), [\operatorname{Fintype}\left(R\right)] [\operatorname{DecidableEq}\left(R\right)] \exists (rho: \operatorname{Matrix}\left(R \times A, R \times A, \mathbb{C}\right)), \exists (sigma: \operatorname{Matrix}\left(R \times A, R \times A, \mathbb{C}\right)), (\operatorname{Matrix.PosSemidef}\left(rho\right)) \land ((\operatorname{Matrix.trace}\left(rho\right) = 1) \land ((\operatorname{Matrix.PosSemidef}\left(sigma\right)) \land ((\operatorname{Matrix.trace}\left(sigma\right) = 1) \land (((orth = \operatorname{true}) \Rightarrow (rho \cdot sigma = 0)) \land ((0 < \operatorname{D5.S3.Quantum.Divergence.ConditionalHockeyStickOrthogonalReduction.gap}\left(gamma, rho, sigma\right)) \land (x = \frac{\operatorname{D5.S3.Quantum.Divergence.ConditionalHockeyStickOrthogonalReduction.gap}\left(gamma, \operatorname{D5.S3.Quantum.Divergence.ConditionalHockeyStickOrthogonalReduction.amp}\left(N, rho\right), \operatorname{D5.S3.Quantum.Divergence.ConditionalHockeyStickOrthogonalReduction.amp}\left(N, sigma\right)\right)}{\operatorname{D5.S3.Quantum.Divergence.ConditionalHockeyStickOrthogonalReduction.gap}\left(gamma, rho, sigma\right)}))))))\}$$

*Formalization.* `D5/S3/Quantum/Divergence/ConditionalHockeyStickOrthogonalReduction.ratios` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Christoph Hirche; Ian George; Theshani Nuradha; Mark M. Wilde (2026). *Conditional contraction coefficients and their applications to quantum networks*. URL: <https://arxiv.org/abs/2608.27171v1>.

*Commentary.*

The set ranges over every finite reference type R and every pair of positive semidefinite trace-one matrices on R times A. Its denominator is strictly positive as required by Remark 2; all quantities are finite real numbers in finite dimension. The choice orth=true adds rho sigma=0, giving the orthogonal subset; orth=false imposes no extra condition. The numerator is the conditional output gap, so these are the ratios in Eq. (2.14). The existential brackets choose the finite-type structures for each reference type.

**Definition 1.8 (Orthogonal reduction and independence of the parameter).**

$$(\operatorname{D5.S3.Quantum.Divergence.ConditionalHockeyStickOrthogonalReduction.claim}) \Leftrightarrow (\forall (A: \operatorname{Type}), [\operatorname{Fintype}\left(A\right)] [\operatorname{DecidableEq}\left(A\right)] \forall (B: \operatorname{Type}), [\operatorname{Fintype}\left(B\right)] [\operatorname{DecidableEq}\left(B\right)] \forall (N: \operatorname{FiniteStateChannel.QuantumChannel}\left(A, B\right)), (\forall (gamma: \mathbb{R}), (1 \le gamma) \Rightarrow (\operatorname{D5.S3.Quantum.Divergence.ConditionalHockeyStickOrthogonalReduction.ratios}\left(N, gamma, \operatorname{false}\right) = \operatorname{D5.S3.Quantum.Divergence.ConditionalHockeyStickOrthogonalReduction.ratios}\left(N, gamma, \operatorname{true}\right))) \land (\forall (gamma: \mathbb{R}), \forall (delta: \mathbb{R}), (1 \le gamma) \Rightarrow ((1 \le delta) \Rightarrow (\operatorname{D5.S3.Quantum.Divergence.ConditionalHockeyStickOrthogonalReduction.ratios}\left(N, gamma, \operatorname{false}\right) = \operatorname{D5.S3.Quantum.Divergence.ConditionalHockeyStickOrthogonalReduction.ratios}\left(N, delta, \operatorname{false}\right)))))$$

*Formalization.* `D5/S3/Quantum/Divergence/ConditionalHockeyStickOrthogonalReduction.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Christoph Hirche; Ian George; Theshani Nuradha; Mark M. Wilde (2026). *Conditional contraction coefficients and their applications to quantum networks*. URL: <https://arxiv.org/abs/2608.27171v1>.

*Commentary.*

Section 9 asks whether the hockey-stick contraction coefficient can be optimized over orthogonal states, extending the trace-distance conclusion of Proposition 8. Here the conditional coefficient is considered: equality holds for the full sets of attainable ratios, and the second conjunct strengthens monotonicity to independence of gamma for gamma at least one. Equality of the sets gives equality of their suprema, including the source's zero convention when no positive denominator exists.

**Theorem 1.9 (Orthogonal states attain exactly the same ratios).**

$$\operatorname{D5.S3.Quantum.Divergence.ConditionalHockeyStickOrthogonalReduction.claim}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/ConditionalHockeyStickOrthogonalReduction.result` (`✓ std3`). ∎

*Resolves.* `Problems/hirche-george-nuradha-wilde-2026-conditional-hockey-stick-orthogonal-reduction` (proved) by `D5/S3/Quantum/Divergence/ConditionalHockeyStickOrthogonalReduction.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"hirche-george-nuradha-wilde-2026-conditional-hockey-stick-orthogonal-reduction","declaration_gid":"D5/S3/Quantum/Divergence/ConditionalHockeyStickOrthogonalReduction.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Christoph Hirche; Ian George; Theshani Nuradha; Mark M. Wilde (2026). *Conditional contraction coefficients and their applications to quantum networks*. URL: <https://arxiv.org/abs/2608.27171v1>.

*Commentary.*

Given density matrices rho and sigma and a positive target parameter delta, write H = rho - gamma sigma = P - Q for the Jordan decomposition: P=H+, Q=(-H)+, P,Q are positive semidefinite and PQ=0. Put p=Tr(P), q=Tr(Q), c=1/(1+p+q/delta), a=1-cp and b=delta-cq. Then c>0 and a,b are nonnegative, with cp+a=1 and (c/delta)q+b/delta=1.

Choose a pure density matrix tau on A and enlarge the reference to R direct-sum C direct-sum C. The two C summands are one-dimensional reference spaces, represented by singleton index types. After distributing the tensor product, set rho' = cP direct-sum a tau direct-sum 0 and sigma' = (c/delta)Q direct-sum 0 direct-sum (b/delta)tau. They are orthogonal density matrices, and their difference rho' - delta sigma' is cH direct-sum a tau direct-sum (-b tau).

Positive-part traces add across the three blocks. Both the reference amplification and the partial trace respect the three blocks. Consequently the input divergence, output divergence and reference-marginal divergence each become c times their original value plus a. Subtracting the marginal term cancels a, so both conditional gaps are multiplied by the same positive c. The denominator stays positive and the ratio is unchanged. Taking delta=gamma yields the orthogonal reduction; transferring in both directions between any gamma,delta at least one yields parameter independence. Thus the conditional coefficient equals its trace-distance value throughout this range.

## References

- Truth anchor: `D5/S3/Quantum/Divergence/ConditionalHockeyStickOrthogonalReduction.E`
- Truth anchor: `D5/S3/Quantum/Divergence/ConditionalHockeyStickOrthogonalReduction.amp`
- Truth anchor: `D5/S3/Quantum/Divergence/ConditionalHockeyStickOrthogonalReduction.claim`
- Truth anchor: `D5/S3/Quantum/Divergence/ConditionalHockeyStickOrthogonalReduction.gap`
- Truth anchor: `D5/S3/Quantum/Divergence/ConditionalHockeyStickOrthogonalReduction.partialTraceRight_smul`
- Truth anchor: `D5/S3/Quantum/Divergence/ConditionalHockeyStickOrthogonalReduction.posSemidef_blockDiagonal`
- Truth anchor: `D5/S3/Quantum/Divergence/ConditionalHockeyStickOrthogonalReduction.posTrace`
- Truth anchor: `D5/S3/Quantum/Divergence/ConditionalHockeyStickOrthogonalReduction.ratios`
- Truth anchor: `D5/S3/Quantum/Divergence/ConditionalHockeyStickOrthogonalReduction.result`
- Dependency: [D5/S3/Quantum/Foundation/FiniteDensityPurification](../Foundation/FiniteDensityPurification.md)
- Dependency: [D5/S3/Quantum/Foundation/FiniteDiamondDistance](../Foundation/FiniteDiamondDistance.md)
- Dependency: [D5/S3/Quantum/Information/OrthogonalRecordEntropy](../Information/OrthogonalRecordEntropy.md)
