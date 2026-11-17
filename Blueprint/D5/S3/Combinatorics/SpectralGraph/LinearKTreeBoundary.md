# Boundary locality for straight linear k-trees

## Abstract

Finite propagation and endpoint moments of banded matrices.

**Definition 1.1 (Banded matrices).**

$$\forall n \in \operatorname{Nat},\; \forall b \in \operatorname{Nat},\; \forall A \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \operatorname{Real}\right),\; \operatorname{IsBanded}\left(b, A\right) = \left(\forall i \in \operatorname{Fin}\left(n\right),\; \forall j \in \operatorname{Fin}\left(n\right),\; (b < \operatorname{Nat}.\operatorname{dist}\left(\operatorname{val}\left(i\right), \operatorname{val}\left(j\right)\right)) \Rightarrow (A\left(i, j\right) = 0)\right)$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/LinearKTreeBoundary.IsBanded` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

An entry is zero when the distance between its indices exceeds b.

**Definition 1.2 (Reversal symmetry).**

$$\forall N \in \operatorname{Nat},\; \forall A \in \operatorname{Matrix}\left(\operatorname{Fin}\left(N\right), \operatorname{Fin}\left(N\right), \operatorname{Real}\right),\; \operatorname{IsReversalInvariant}\left(A\right) = \left(\forall i \in \operatorname{Fin}\left(N\right),\; \forall j \in \operatorname{Fin}\left(N\right),\; A\left(\operatorname{Fin}.\operatorname{rev}\left(i\right), \operatorname{Fin}.\operatorname{rev}\left(j\right)\right) = A\left(i, j\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/LinearKTreeBoundary.IsReversalInvariant` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Reversing both indices preserves each matrix entry.

**Theorem 1.3 (Eventual constancy of boundary moments).**

$$\forall A \in (N: \operatorname{Nat}) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(N\right), \operatorname{Fin}\left(N\right), \operatorname{Real}\right),\; \forall b \in \operatorname{Nat},\; \forall r \in \operatorname{Nat},\; \forall q \in \operatorname{Nat},\; \forall f \in \operatorname{Nat} \to \operatorname{Real},\; (\forall i \in \operatorname{Nat},\; (r \le i) \Rightarrow (f\left(i\right) = 0)) \Rightarrow ((\forall N \in \operatorname{Nat},\; \operatorname{IsBanded}\left(b, A\left(N\right)\right)) \Rightarrow ((\forall N \in \operatorname{Nat},\; \operatorname{IsReversalInvariant}\left(A\left(N\right)\right)) \Rightarrow ((\forall N \in \operatorname{Nat},\; \forall M \in \operatorname{Nat},\; \forall i \in \operatorname{Fin}\left(N\right),\; \forall j \in \operatorname{Fin}\left(N\right),\; \forall u \in \operatorname{Fin}\left(M\right),\; \forall v \in \operatorname{Fin}\left(M\right),\; (\operatorname{val}\left(i\right) = \operatorname{val}\left(u\right)) \Rightarrow ((\operatorname{val}\left(j\right) = \operatorname{val}\left(v\right)) \Rightarrow ((\operatorname{val}\left(i\right) + q \le N) \Rightarrow ((\operatorname{val}\left(u\right) + q \le M) \Rightarrow (A\left(N\right)\left(i, j\right) = A\left(M\right)\left(u, v\right)))))) \Rightarrow (\forall L \in \operatorname{Nat},\; \exists C \in \operatorname{Real},\; \operatorname{Filter}.\operatorname{Eventually}\left((\lambda N: \operatorname{Nat} \mapsto \operatorname{dotProduct}\left((\lambda i: \operatorname{Fin}\left(N\right) \mapsto f\left(\operatorname{val}\left(i\right)\right) + f\left(\operatorname{val}\left(\operatorname{Fin}.\operatorname{rev}\left(i\right)\right)\right)), \operatorname{Matrix}.\operatorname{mulVec}\left(A\left(N\right)^{L}, (\lambda i: \operatorname{Fin}\left(N\right) \mapsto f\left(\operatorname{val}\left(i\right)\right) + f\left(\operatorname{val}\left(\operatorname{Fin}.\operatorname{rev}\left(i\right)\right)\right))\right)\right) = C), \operatorname{Filter}.\operatorname{atTop}\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/LinearKTreeBoundary.boundary_moments_stabilize` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A fixed power reaches only a finite distance. Once both endpoints are farther apart than that distance, their cross terms vanish; the same-endpoint terms agree with one fixed finite section. Reversal symmetry makes the two endpoint contributions equal.

**Theorem 1.4 (Consecutive differences of an affine asymptotic).**

$$\forall R \in \operatorname{Nat} \to \operatorname{Real},\; \forall c \in \operatorname{Nat} \to \operatorname{Real},\; \forall d \in \operatorname{Real},\; \forall C \in \operatorname{Real},\; (\operatorname{Filter}.\operatorname{Tendsto}\left(c, \operatorname{Filter}.\operatorname{atTop}, \operatorname{nhds}\left(C\right)\right)) \Rightarrow ((\operatorname{Filter}.\operatorname{Eventually}\left((\lambda n: \operatorname{Nat} \mapsto R\left(n\right) = (n: \operatorname{Real}) \cdot d + c\left(n\right)), \operatorname{Filter}.\operatorname{atTop}\right)) \Rightarrow (\operatorname{Filter}.\operatorname{Tendsto}\left((\lambda n: \operatorname{Nat} \mapsto R\left(n + 1\right) - R\left(n\right)), \operatorname{Filter}.\operatorname{atTop}, \operatorname{nhds}\left(d\right)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/LinearKTreeBoundary.increment_limit_of_affine_correction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A convergent correction contributes zero to the limit of consecutive differences.

**Theorem 1.5 (Exact inverse defect expansion).**

$$\forall I \in \operatorname{Type},\; [\operatorname{Fintype}\left(I\right)] [\operatorname{DecidableEq}\left(I\right)] \forall Q \in \operatorname{Matrix}\left(I, I, \operatorname{Real}\right),\; (\operatorname{Matrix}.\operatorname{IsSymm}\left(Q\right)) \Rightarrow ((\operatorname{IsUnit}\left(Q\right)) \Rightarrow (\forall u \in I \to \operatorname{Real},\; \forall D \in \operatorname{Real},\; (D \ne 0) \Rightarrow (\operatorname{dotProduct}\left(u, \operatorname{Matrix}.\operatorname{mulVec}\left(Q^{-1}, u\right)\right) = \frac{\operatorname{dotProduct}\left(u, u\right)}{D} + \frac{\operatorname{dotProduct}\left(u, \operatorname{HSMul}.\operatorname{hSMul}\left(D, u\right) - \operatorname{Matrix}.\operatorname{mulVec}\left(Q, u\right)\right) + \operatorname{dotProduct}\left(\operatorname{HSMul}.\operatorname{hSMul}\left(D, u\right) - \operatorname{Matrix}.\operatorname{mulVec}\left(Q, u\right), \operatorname{Matrix}.\operatorname{mulVec}\left(Q^{-1}, \operatorname{HSMul}.\operatorname{hSMul}\left(D, u\right) - \operatorname{Matrix}.\operatorname{mulVec}\left(Q, u\right)\right)\right)}{D^{2}})))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/LinearKTreeBoundary.inverse_defect_expansion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For c = D u - Q u, the inverse quadratic form splits into a bulk term and a defect correction.

**Theorem 1.6 (Constant boundary sum).**

$$\forall r \in \operatorname{Nat},\; \forall N \in \operatorname{Nat},\; (r \le N) \Rightarrow (\forall f \in \operatorname{Nat} \to \operatorname{Real},\; (\forall i \in \operatorname{Nat},\; (r \le i) \Rightarrow (f\left(i\right) = 0)) \Rightarrow (\operatorname{Finset}.\operatorname{sum}\left(\operatorname{Finset}.\operatorname{univ}, (\lambda i: \operatorname{Fin}\left(N\right) \mapsto f\left(\operatorname{val}\left(i\right)\right) + f\left(\operatorname{val}\left(\operatorname{Fin}.\operatorname{rev}\left(i\right)\right)\right))\right) = 2 \cdot \operatorname{Finset}.\operatorname{sum}\left(\operatorname{Finset}.\operatorname{univ}, (\lambda i: \operatorname{Fin}\left(r\right) \mapsto f\left(\operatorname{val}\left(i\right)\right))\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/LinearKTreeBoundary.boundary_sum_constant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Reflection preserves the sum, and support in the first r positions reduces it to a fixed finite sum.

**Theorem 1.7 (Uniform boundary norm bound).**

$$\forall r \in \operatorname{Nat},\; \forall N \in \operatorname{Nat},\; (r \le N) \Rightarrow (\forall f \in \operatorname{Nat} \to \operatorname{Real},\; (\forall i \in \operatorname{Nat},\; (r \le i) \Rightarrow (f\left(i\right) = 0)) \Rightarrow (\left\lVert \operatorname{WithLp}.\operatorname{toLp}\left(2, (\lambda i: \operatorname{Fin}\left(N\right) \mapsto f\left(\operatorname{val}\left(i\right)\right) + f\left(\operatorname{val}\left(\operatorname{Fin}.\operatorname{rev}\left(i\right)\right)\right))\right) \right\rVert^{2} \le 4 \cdot \operatorname{Finset}.\operatorname{sum}\left(\operatorname{Finset}.\operatorname{univ}, (\lambda i: \operatorname{Fin}\left(r\right) \mapsto f\left(\operatorname{val}\left(i\right)\right)^{2})\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/LinearKTreeBoundary.boundary_norm_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The squared norm of the two endpoint vectors is at most four times the squared norm of one endpoint profile.

**Theorem 1.8 (Order bound from nonnegative row sums).**

$$\forall I \in \operatorname{Type},\; [\operatorname{Fintype}\left(I\right)] [\operatorname{DecidableEq}\left(I\right)] \forall A \in \operatorname{Matrix}\left(I, I, \operatorname{Real}\right),\; (\operatorname{Matrix}.\operatorname{IsHermitian}\left(A\right)) \Rightarrow ((\forall i \in I,\; \forall j \in I,\; 0 \le A\left(i, j\right)) \Rightarrow (\forall D \in \operatorname{Real},\; (\forall i \in I,\; \operatorname{Finset}.\operatorname{sum}\left(\operatorname{Finset}.\operatorname{univ}, (\lambda j: I \mapsto A\left(i, j\right))\right) \le D) \Rightarrow (A \le \operatorname{HSMul}.\operatorname{hSMul}\left(D, (1: \operatorname{Matrix}\left(I, I, \operatorname{Real}\right))\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/LinearKTreeBoundary.nonnegative_row_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Symmetry and 2xy ≤ x²+y² bound the quadratic form by the maximum row sum.

**Theorem 1.9 (Geometric contraction bound).**

$$\forall I \in \operatorname{Type},\; [\operatorname{Fintype}\left(I\right)] [\operatorname{DecidableEq}\left(I\right)] \forall Q \in \operatorname{Matrix}\left(I, I, \operatorname{Real}\right),\; \forall D \in \operatorname{Real},\; (1 \le D) \Rightarrow (((1: \operatorname{Matrix}\left(I, I, \operatorname{Real}\right)) \le Q) \Rightarrow ((Q \le \operatorname{HSMul}.\operatorname{hSMul}\left(D, (1: \operatorname{Matrix}\left(I, I, \operatorname{Real}\right))\right)) \Rightarrow (\left\lVert (1: \operatorname{Matrix}\left(I, I, \operatorname{Real}\right)) - \operatorname{HSMul}.\operatorname{hSMul}\left(D^{-1}, Q\right) \right\rVert \le 1 - D^{-1})))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/LinearKTreeBoundary.richardson_norm_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The order interval I ≤ Q ≤ D I places the spectrum of I - D⁻¹ Q in the interval from zero to 1 - D⁻¹.

## References

- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/LinearKTreeBoundary.IsBanded`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/LinearKTreeBoundary.IsReversalInvariant`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/LinearKTreeBoundary.boundary_moments_stabilize`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/LinearKTreeBoundary.boundary_norm_bound`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/LinearKTreeBoundary.boundary_sum_constant`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/LinearKTreeBoundary.increment_limit_of_affine_correction`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/LinearKTreeBoundary.inverse_defect_expansion`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/LinearKTreeBoundary.nonnegative_row_bound`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/LinearKTreeBoundary.richardson_norm_bound`
- Dependency: [D5/S3/Observer/Linear/SmallSignedEntryTranscriptCompensation](../../Observer/Linear/SmallSignedEntryTranscriptCompensation.md)
