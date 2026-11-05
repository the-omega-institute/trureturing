# Trace bounds, interpolation and phase rigidity

## Abstract

Unitary rank-one trace and scalar analytic certificates for the spectral moment argument.

**Theorem 1.1 (The finite rank-one trace identity).**

$$\forall (\iota: Type), ([\operatorname{Fintype}\left(\iota\right)], (\forall (n: Type), ([\operatorname{Fintype}\left(n\right)], ([\operatorname{DecidableEq}\left(n\right)], (\forall (r: (\iota) \to (\operatorname{EuclideanSpace}\left(\mathbb{C}, n\right))), (\forall (a: (\iota) \to (\mathbb{R})), (\forall (\gamma: (\iota) \to (\mathbb{C})), (\forall (V: \operatorname{Matrix}\left(n, n, \mathbb{C}\right)), (\operatorname{Matrix.trace}\left(V \cdot \sum_{j: \iota} (\operatorname{HSMul.hSMul}\left(\operatorname{Complex.ofReal}\left(a\left(j\right)\right) \cdot \gamma\left(j\right), \operatorname{Matrix.vecMulVec}\left(\operatorname{WithLp.ofLp}\left(r\left(j\right)\right), \operatorname{star}\left(\operatorname{WithLp.ofLp}\left(r\left(j\right)\right)\right)\right)\right))\right) = \sum_{j: \iota} (\operatorname{Complex.ofReal}\left(a\left(j\right)\right) \cdot \gamma\left(j\right) \cdot \operatorname{inner}\left(\mathbb{C}, r\left(j\right), \operatorname{Matrix.toEuclideanLin}\left(V\right)\left(r\left(j\right)\right)\right)))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/CriticalPoints/RankOneTraceBound.trace_rank_one_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any finite family of complex Euclidean vectors, real coefficients a, complex coefficients γ and complex matrix V, the trace of V times their weighted rank-one sum is the corresponding weighted sum of quadratic inner products. No positivity, normalization or unitarity is assumed. Complex.ofReal displays the real coefficients as complex scalars, and WithLp.ofLp reads the coordinate functions.

**Theorem 1.2 (The unitary trace estimate).**

Lean statement: `D5/S3/Zeros/CriticalPoints/RankOneTraceBound.norm_trace_rank_one_sum_le`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/CriticalPoints/RankOneTraceBound.norm_trace_rank_one_sum_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For finite complex Euclidean vectors r_j, nonnegative real weights a_j, unit complex phases gamma_j and a unitary matrix V, the norm of Tr(V sum_j a_j gamma_j r_j r_j*) is at most sum_j a_j times the squared norm of r_j. The estimate includes zero weights and zero vectors.

**Theorem 1.3 (Equality forces a common phase).**

Lean statement: `D5/S3/Zeros/CriticalPoints/RankOneTraceBound.phases_eq_of_norm_trace_rank_one_sum_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/CriticalPoints/RankOneTraceBound.phases_eq_of_norm_trace_rank_one_sum_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume the weights are strictly positive and every pairwise inner product of the r_j is nonzero. If the unitary trace estimate is an equality, then gamma_i=gamma_j for every i,j. Cauchy–Schwarz equality places each r_j in a unitary eigenspace; nonorthogonality identifies those eigenphases, and equality in the finite triangle inequality identifies the original phases.

**Theorem 1.4 (The interpolation bound and equality boundary).**

Lean statement: `D5/S3/Zeros/CriticalPoints/RankOneTraceBound.strip_moment_bound_and_equality`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/CriticalPoints/RankOneTraceBound.strip_moment_bound_and_equality` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let M>0. A complex function continuous on the closed strip and differentiable in its interior, bounded there, with left boundary norm at most one and right boundary norm at most M, has norm at most M^(Re z) throughout the strip. If equality occurs at a real interior point theta with 0<theta<1, then the norm equals M at every right boundary point 1+iy. The equality argument applies the maximum modulus principle to exp(−z log M) times the function.

**Theorem 1.5 (Rotating phases determine their frequencies).**

Lean statement: `D5/S3/Zeros/CriticalPoints/RankOneTraceBound.rotating_phase_injective`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/CriticalPoints/RankOneTraceBound.rotating_phase_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For complex u,v with u nonzero and real a,b, if u exp(iya)=v exp(iyb) for every real y, then u=v and a=b. Evaluation at zero determines the phase, and equality of derivatives at zero determines the frequency.

## References

- Truth anchor: `D5/S3/Zeros/CriticalPoints/RankOneTraceBound.norm_trace_rank_one_sum_le`
- Truth anchor: `D5/S3/Zeros/CriticalPoints/RankOneTraceBound.phases_eq_of_norm_trace_rank_one_sum_eq`
- Truth anchor: `D5/S3/Zeros/CriticalPoints/RankOneTraceBound.rotating_phase_injective`
- Truth anchor: `D5/S3/Zeros/CriticalPoints/RankOneTraceBound.strip_moment_bound_and_equality`
- Truth anchor: `D5/S3/Zeros/CriticalPoints/RankOneTraceBound.trace_rank_one_sum`
