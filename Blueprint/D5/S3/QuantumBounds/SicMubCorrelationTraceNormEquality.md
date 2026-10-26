# SIC–MUB correlation trace-norm equality

## Abstract

SIC and complete-MUB correlation matrices have proportional rectangular trace norms.

All vector and matrix entries are complex. Natural dimensions are used as finite index sizes, and FiniteTraceDistance.traceNorm is the real part of the trace of the positive square root of the matrix's conjugate transpose times the matrix. MUBFamily and its effect are those of TavakoliMorelliIncompleteMUB: a complete family has d + 1 unitary bases, with squared overlaps 1/(d : ℝ) between distinct bases. Its effect at a pair p is the rank-one projector onto column p.2 of basis p.1.

**Definition 1.1 (SIC families).**

$$\forall (d: \mathbb{N}), (SICFamily\left(d\right) = \{(psi: (Fin\left(d \cdot d\right) \to (Fin\left(d\right) \to \mathbb{C}))) / / (\forall (i: Fin\left(d \cdot d\right)), (dotProduct\left(star\left(psi\left(i\right)\right), psi\left(i\right)\right) = 1)) \land (\forall (i: Fin\left(d \cdot d\right)), (\forall (j: Fin\left(d \cdot d\right)), ((i \ne j) \Rightarrow ((\left\lVert dotProduct\left(star\left(psi\left(i\right)\right), psi\left(j\right)\right) \right\rVert)^{2} = \frac{1}{(d: \mathbb{R}) + 1}))))\})$$

*Formalization.* `D5/S3/QuantumBounds/SicMubCorrelationTraceNormEquality.SICFamily` (`✓ std3`).

*Citation.* Armin Tavakoli; Simon Morelli (2024). *Enhanced Schmidt number criteria based on correlation trace norms*. DOI: [10.1103/PhysRevA.110.062417](https://doi.org/10.1103/PhysRevA.110.062417). URL: <https://arxiv.org/abs/2402.09972v2>.

*Commentary.*

A SIC family consists of d squared vectors in C to the d, each of unit norm, with squared modulus overlap 1/(d+1) for every distinct pair. The subtype retains exactly these normalization and equiangularity conditions.

**Definition 1.2 (SIC effects).**

$$\forall (d: \mathbb{N}), (\forall (S: SICFamily\left(d\right)), (\forall (i: Fin\left(d \cdot d\right)), (sicEffect\left(S, i\right) = smul\left(\frac{1}{(d: \mathbb{C})}, rankOneDensity\left(val\left(S\right)\left(i\right)\right)\right))))$$

*Formalization.* `D5/S3/QuantumBounds/SicMubCorrelationTraceNormEquality.sicEffect` (`✓ std3`).

*Citation.* Armin Tavakoli; Simon Morelli (2024). *Enhanced Schmidt number criteria based on correlation trace norms*. DOI: [10.1103/PhysRevA.110.062417](https://doi.org/10.1103/PhysRevA.110.062417). URL: <https://arxiv.org/abs/2402.09972v2>.

*Commentary.*

The effect indexed by i is the rank-one projector of the i-th SIC vector scaled by the inverse of d.

**Definition 1.3 (The SIC correlation matrix).**

$$\forall (dA: \mathbb{N}), (\forall (dB: \mathbb{N}), (\forall (rho: Matrix\left((Fin\left(dA\right) \times Fin\left(dB\right)), (Fin\left(dA\right) \times Fin\left(dB\right)), \mathbb{C}\right)), (\forall (SA: SICFamily\left(dA\right)), (\forall (SB: SICFamily\left(dB\right)), (sicCorrelation\left(rho, SA, SB\right) = \operatorname{Matrix.of}\left((\lambda (i: Fin\left(dA \cdot dA\right)) \mapsto (\lambda (j: Fin\left(dB \cdot dB\right)) \mapsto trace\left(rho \cdot kronecker\left(sicEffect\left(SA, i\right), sicEffect\left(SB, j\right)\right)\right)))\right))))))$$

*Formalization.* `D5/S3/QuantumBounds/SicMubCorrelationTraceNormEquality.sicCorrelation` (`✓ std3`).

*Citation.* Armin Tavakoli; Simon Morelli (2024). *Enhanced Schmidt number criteria based on correlation trace norms*. DOI: [10.1103/PhysRevA.110.062417](https://doi.org/10.1103/PhysRevA.110.062417). URL: <https://arxiv.org/abs/2402.09972v2>.

*Commentary.*

For a bipartite operator and two local SIC families, the rectangular matrix records the trace of the operator against every tensor product of local SIC effects. Its row and column sets have sizes d_A squared and d_B squared.

**Definition 1.4 (The complete-MUB correlation matrix).**

$$\forall (dA: \mathbb{N}), (\forall (dB: \mathbb{N}), (\forall (rho: Matrix\left((Fin\left(dA\right) \times Fin\left(dB\right)), (Fin\left(dA\right) \times Fin\left(dB\right)), \mathbb{C}\right)), (\forall (MA: MUBFamily\left(dA, dA + 1\right)), (\forall (MB: MUBFamily\left(dB, dB + 1\right)), (mubCorrelation\left(rho, MA, MB\right) = \operatorname{Matrix.of}\left((\lambda (i: (Fin\left(dA + 1\right) \times Fin\left(dA\right))) \mapsto (\lambda (j: (Fin\left(dB + 1\right) \times Fin\left(dB\right))) \mapsto trace\left(rho \cdot kronecker\left((MA).effect\left(i\right), (MB).effect\left(j\right)\right)\right)))\right))))))$$

*Formalization.* `D5/S3/QuantumBounds/SicMubCorrelationTraceNormEquality.mubCorrelation` (`✓ std3`).

*Citation.* Armin Tavakoli; Simon Morelli (2024). *Enhanced Schmidt number criteria based on correlation trace norms*. DOI: [10.1103/PhysRevA.110.062417](https://doi.org/10.1103/PhysRevA.110.062417). URL: <https://arxiv.org/abs/2402.09972v2>.

*Commentary.*

For two complete MUB families, the rectangular matrix records the trace against every pair of rank-one MUB effects. Its row and column labels are basis and outcome pairs.

**Definition 1.5 (The SIC–MUB trace-norm equality).**

$$\forall (dA: \mathbb{N}), (\forall (dB: \mathbb{N}), ((2 \le dA) \Rightarrow ((2 \le dB) \Rightarrow (\forall (SA: SICFamily\left(dA\right)), (\forall (SB: SICFamily\left(dB\right)), (\forall (MA: MUBFamily\left(dA, dA + 1\right)), (\forall (MB: MUBFamily\left(dB, dB + 1\right)), (\forall (rho: Matrix\left((Fin\left(dA\right) \times Fin\left(dB\right)), (Fin\left(dA\right) \times Fin\left(dB\right)), \mathbb{C}\right)), ((PosSemidef\left(rho\right)) \Rightarrow ((trace\left(rho\right) = 1) \Rightarrow (traceNorm\left(mubCorrelation\left(rho, MA, MB\right)\right) = \operatorname{Real.sqrt}\left((dA: \mathbb{R}) \cdot \left((dA: \mathbb{R}) + 1\right)\right) \cdot \operatorname{Real.sqrt}\left((dB: \mathbb{R}) \cdot \left((dB: \mathbb{R}) + 1\right)\right) \cdot traceNorm\left(sicCorrelation\left(rho, SA, SB\right)\right))))))))))))$$

*Formalization.* `D5/S3/QuantumBounds/SicMubCorrelationTraceNormEquality.claim` (`✓ std3`).

*Citation.* Armin Tavakoli; Simon Morelli (2024). *Enhanced Schmidt number criteria based on correlation trace norms*. DOI: [10.1103/PhysRevA.110.062417](https://doi.org/10.1103/PhysRevA.110.062417). URL: <https://arxiv.org/abs/2402.09972v2>.

*Commentary.*

Conjecture 1 states that for local dimensions at least two, every pair of SIC families, every pair of complete MUB families, and every positive semidefinite trace-one bipartite operator, the complete-MUB trace norm equals the SIC trace norm multiplied by the two dimension factors.

**Theorem 1.6 (Trace pairings on a spanning family).**

$$\forall (d: \mathbb{N}), (\forall (\iota: Type), (\forall (P: (\iota \to Matrix\left(Fin\left(d\right), Fin\left(d\right), \mathbb{C}\right))), ((\operatorname{Submodule.span}\left(\mathbb{C}, \operatorname{Set.range}\left(P\right)\right) = \operatorname{Top.top}) \Rightarrow (\forall (X: Matrix\left(Fin\left(d\right), Fin\left(d\right), \mathbb{C}\right)), (\forall (Y: Matrix\left(Fin\left(d\right), Fin\left(d\right), \mathbb{C}\right)), ((\forall (i: \iota), (trace\left(X \cdot P\left(i\right)\right) = trace\left(Y \cdot P\left(i\right)\right))) \Rightarrow (X = Y)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumBounds/SicMubCorrelationTraceNormEquality.trace_pairing_ext` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Armin Tavakoli; Simon Morelli (2024). *Enhanced Schmidt number criteria based on correlation trace norms*. DOI: [10.1103/PhysRevA.110.062417](https://doi.org/10.1103/PhysRevA.110.062417). URL: <https://arxiv.org/abs/2402.09972v2>.

*Commentary.*

Two complex square matrices are equal when their trace pairings agree on a family whose complex linear span is the full matrix space.

**Theorem 1.7 (The equality follows from two frames and an isometry).**

$$claim$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumBounds/SicMubCorrelationTraceNormEquality.result` (`✓ std3`). ∎

*Resolves.* `Problems/tavakoli-morelli-2024-conjecture-1-sic-mub-trace-norm-equality` (proved) by `D5/S3/QuantumBounds/SicMubCorrelationTraceNormEquality.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"tavakoli-morelli-2024-conjecture-1-sic-mub-trace-norm-equality","declaration_gid":"D5/S3/QuantumBounds/SicMubCorrelationTraceNormEquality.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Armin Tavakoli; Simon Morelli (2024). *Enhanced Schmidt number criteria based on correlation trace norms*. DOI: [10.1103/PhysRevA.110.062417](https://doi.org/10.1103/PhysRevA.110.062417). URL: <https://arxiv.org/abs/2402.09972v2>.

*Commentary.*

For a local dimension d at least two, a SIC family S, and any complex d by d matrix X, sic_frame reconstructs X from its traces against sicEffect S i. The identity sicProjector_sum says that the sum of rankOneDensity(S.val i) over all i in Fin (d * d) is (d : ℂ) times the identity. For a complete MUB family M, mub_frame says that the sum of trace(M.effect p * X) times M.effect p over p in Fin (d + 1) times Fin d is X plus trace(X) times the identity.

For a local dimension d at least two, a SIC family S, and a complete MUB family M, transition S M has row indices p in Fin (d + 1) times Fin d and column indices i in Fin (d * d). Its (p, i) entry is ((d : ℂ) + 1) times trace(rankOneDensity(S.val i) * M.effect p), minus one. The entries are real by transition_real, and transition_gram says that its conjugate transpose times itself is (d : ℂ) * ((d : ℂ) + 1) times the identity.

For the dimensions, families, and operator in claim, correlation_transition expresses mubCorrelation rho MA MB as transition SA MA times sicCorrelation rho SA SB times the conjugate transpose of transition SB MB. For each local dimension d, the transition matrix is the square root of (d : ℝ) * ((d : ℝ) + 1) times an isometry. The theorem scaled_isometry_traceNorm uses uniqueness of the positive square root and cyclicity of the trace to give the stated product of square-root factors.

## References

- Truth anchor: `D5/S3/QuantumBounds/SicMubCorrelationTraceNormEquality.SICFamily`
- Truth anchor: `D5/S3/QuantumBounds/SicMubCorrelationTraceNormEquality.claim`
- Truth anchor: `D5/S3/QuantumBounds/SicMubCorrelationTraceNormEquality.mubCorrelation`
- Truth anchor: `D5/S3/QuantumBounds/SicMubCorrelationTraceNormEquality.result`
- Truth anchor: `D5/S3/QuantumBounds/SicMubCorrelationTraceNormEquality.sicCorrelation`
- Truth anchor: `D5/S3/QuantumBounds/SicMubCorrelationTraceNormEquality.sicEffect`
- Truth anchor: `D5/S3/QuantumBounds/SicMubCorrelationTraceNormEquality.trace_pairing_ext`
- Dependency: [D5/S3/Quantum/Entanglement/TavakoliMorelliIncompleteMUB](../Quantum/Entanglement/TavakoliMorelliIncompleteMUB.md)
- Dependency: [D5/S3/Quantum/Tomography/CompleteContextTomography](../Quantum/Tomography/CompleteContextTomography.md)
