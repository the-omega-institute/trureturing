# Crossing-Matrix Determinant Obstruction

## Abstract

Positive powers of two crossing matrices have a strict determinant obstruction.

**Theorem 1.1 (Both crossing-matrix power shifts are nonsingular).**

$$\begin{aligned}\forall k, n \in \mathbb{N}, 0 < k \land 0 < n \Rightarrow\\\left(\operatorname{det}(C_{k}^{n} - I) = 2 - \operatorname{tr}(C_{k}^{n})\right) \land\\\left(\operatorname{det}(C_{k}^{n} - I) < 0\right) \land\\\left(\operatorname{det}(C_{k}^{n} - I) \neq 0\right) \land\\\left(\operatorname{det}(D_{k}^{n} - I) \neq 0\right).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/CrossingMatrixDeterminant.crossing_det_pow_sub_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive natural numbers k and n, let C_k=!![4k+1,1;4k,1] and D_k=!![2k+1,2;2k(k+1),2k+1]. Both integer matrices have determinant one and trace 4k+2.

A real Vieta pair for an arbitrary two by two integer matrix with this determinant and trace, together with the frozen trace_pow_eq_add_pow theorem, expresses the trace of its nth power as a^n+b^n. The strict positivity of (a^n-1)^2 for k>0 and n>0 gives trace greater than two.

For a determinant-one matrix M of size two, expansion gives det(M-I)=2-tr(M). Applying the strict trace bound to C_k makes this determinant negative and therefore nonzero. The same argument applied to D_k makes det(D_k^n-I) nonzero.

This result does not establish the Smith-form cardinality #(Z^2/MZ^2)=|det(M)|, nor the cardinalities of the return groups R(C_k,n) and R(D_k,n).

## References

- Truth anchor: `D5/S1/Recurrence/CrossingMatrixDeterminant.crossing_det_pow_sub_one`
- Dependency: [D5/S0/Observation/MatrixTracePowerSum](../../S0/Observation/MatrixTracePowerSum.md)
