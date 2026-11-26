# The square root of QTD is not a metric

## Abstract

The square root of quantum triangular discrimination fails every uniform quasi-triangle inequality.

Yupan Liu, Complexity-theoretic perspectives on quantum state testing, PhD thesis, Nagoya University, Open Problem 8.16, printed p. 180, asks: “Is it possible to prove that the square root of quantum triangular discrimination, denoted as √QTD, is a distance metric? Specifically, for any quantum states ρ0, ρ1, and ρ2, can it be shown that the following inequality holds: √QTD(ρ0, ρ1) + √QTD(ρ1, ρ2) ≥ √QTD(ρ0, ρ2)?” The same proposed triangle inequality appears in §1.3 of Quantum state testing beyond the polarizing regime and quantum triangular discrimination, arXiv:2303.01952v5; Computational Complexity 34 (2025), article 11.

**Definition 1.1 (The proposed triangle inequality).**

$$claim \Leftrightarrow (\forall n: \mathbb{N}, \forall rho0: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right), \forall rho1: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right), \forall rho2: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right), (\operatorname{IsState}\left(rho0\right)) \Rightarrow ((\operatorname{IsState}\left(rho1\right)) \Rightarrow ((\operatorname{IsState}\left(rho2\right)) \Rightarrow (\sqrt{\operatorname{QTD}\left(rho0, rho2\right)} \le (\sqrt{\operatorname{QTD}\left(rho0, rho1\right)}) + (\sqrt{\operatorname{QTD}\left(rho1, rho2\right)})))))$$

*Formalization.* `D5/S3/Divergence/QuantumTriangularMetricRefutation.claim` (`✓ std3`).

*Citation.* Yupan Liu (2025). *Quantum state testing beyond the polarizing regime and quantum triangular discrimination*. DOI: [10.48550/arXiv.2303.01952](https://doi.org/10.48550/arXiv.2303.01952). URL: <https://arxiv.org/abs/2303.01952v5>.

*Commentary.*

Open Problem 8.16 asks whether the square root of Definition 3.1 satisfies the triangle inequality for every triple of quantum states in every finite dimension. IsState means positive semidefinite with trace one. QTD is the original matrix functional-calculus expression, with the inverse square root taken on the support. The quantifier over dimensions also includes zero.

**Theorem 1.2 (No uniform quasi-triangle constant).**

$$\forall K: \mathbb{R}, \exists rho0: \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right), \exists rho1: \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right), \exists rho2: \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right), (\operatorname{IsState}\left(rho0\right)) \land ((\operatorname{IsState}\left(rho1\right)) \land ((\operatorname{IsState}\left(rho2\right)) \land ((K) \cdot ((\sqrt{\operatorname{QTD}\left(rho0, rho1\right)}) + (\sqrt{\operatorname{QTD}\left(rho1, rho2\right)})) < \sqrt{\operatorname{QTD}\left(rho0, rho2\right)})))$$

*Proof.* Machine-checked in Lean as `D5/S3/Divergence/QuantumTriangularMetricRefutation.no_quasi_triangle` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Yupan Liu (2025). *Quantum state testing beyond the polarizing regime and quantum triangular discrimination*. DOI: [10.48550/arXiv.2303.01952](https://doi.org/10.48550/arXiv.2303.01952). URL: <https://arxiv.org/abs/2303.01952v5>.

*Commentary.*

For 0<t≤1/4, let ρ±=(1+t⁶)⁻¹[[1,±t³],[±t³,t⁶]] and τ=diag(1−t⁴,t⁴). The endpoint matrices are positive semidefinite of rank one and trace one, while τ is positive definite of trace one. Equivalently, the endpoint parameter is r=t³ and the diagonal parameter is b=t⁴. The sum ρ++ρ− is diagonal, and QTD(ρ+,ρ−)=2t³/(1+t⁶). To calculate a short edge, put a=t⁶/(1+t⁶), b=t⁴, d=√(b(2−b)+(1−2b)a), u=b²+(1−2b)a and v=b(1−b). A positive definite two-by-two matrix S of trace two has inverse square root ((2+d)I−S)/(d√(2+2d)), where d²=det S. The existing CommutingMidpoint identities sqrt_trace_square_two and sqrt_times_trace_two give sqrt(S)=(S+dI)/√(2+2d). The displayed inverse is checked by multiplication, then identified with the negative half power using half_inverse. The trace identity Tr(M²)=(Tr M)²−2det M, applied to M=(ρ+−τ)(ρ++τ)⁻¹ᐟ², gives QTD(ρ+,τ)=u/d+v²/(d²(1+d)). Changing the sign of the coherence gives QTD(τ,ρ−)=QTD(ρ+,τ). The scalar bounds d²≥3t⁴/2, d≥t², u≤17t⁶/16 and v²≤t⁸ imply QTD(ρ+,τ)≤83t⁴/48<7t⁴/4. For an arbitrary real K, choose m≥max(1,K) and t=1/(8m²). Then 4m²QTD(ρ+,τ)<QTD(ρ+,ρ−). Taking nonnegative square roots gives the strict comparison in the displayed statement. Thus a fixed multiplicative constant cannot restore the triangle inequality even on qubit states.

**Theorem 1.3 (The triangle inequality fails).**

$$\neg (\forall n: \mathbb{N}, \forall rho0: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right), \forall rho1: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right), \forall rho2: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right), (\operatorname{IsState}\left(rho0\right)) \Rightarrow ((\operatorname{IsState}\left(rho1\right)) \Rightarrow ((\operatorname{IsState}\left(rho2\right)) \Rightarrow (\sqrt{\operatorname{QTD}\left(rho0, rho2\right)} \le (\sqrt{\operatorname{QTD}\left(rho0, rho1\right)}) + (\sqrt{\operatorname{QTD}\left(rho1, rho2\right)})))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Divergence/QuantumTriangularMetricRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/liu-2025-qtd-triangle-inequality-refutation` (refuted) by `D5/S3/Divergence/QuantumTriangularMetricRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"liu-2025-qtd-triangle-inequality-refutation","declaration_gid":"D5/S3/Divergence/QuantumTriangularMetricRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Yupan Liu (2025). *Quantum state testing beyond the polarizing regime and quantum triangular discrimination*. DOI: [10.48550/arXiv.2303.01952](https://doi.org/10.48550/arXiv.2303.01952). URL: <https://arxiv.org/abs/2303.01952v5>.

*Commentary.*

Apply the preceding theorem at K=1. Its three qubit states satisfy the strict reverse of the proposed triangle inequality, contradicting its dimension-two instance. Hence the square root of QTD is not a distance metric. The contrast with classical triangular discrimination concerns this particular quantum extension and does not identify a different quantum divergence with QTD.

## References

- Truth anchor: `D5/S3/Divergence/QuantumTriangularMetricRefutation.claim`
- Truth anchor: `D5/S3/Divergence/QuantumTriangularMetricRefutation.no_quasi_triangle`
- Truth anchor: `D5/S3/Divergence/QuantumTriangularMetricRefutation.result`
- Dependency: [D5/S0/Observation/MatrixTracePowerSum](../../S0/Observation/MatrixTracePowerSum.md)
- Dependency: [D5/S3/Divergence/QuantumTriangularJensenShannonRefutation](QuantumTriangularJensenShannonRefutation.md)
- Dependency: [D5/S3/Quantum/CommutingMidpoint/Fidelity](../Quantum/CommutingMidpoint/Fidelity.md)
- Dependency: [D5/S3/Quantum/Dynamics/EntropyProductionCoherenceDeletionIdentity](../Quantum/Dynamics/EntropyProductionCoherenceDeletionIdentity.md)
- Dependency: [D5/S3/Quantum/Matrix/AlternativeMeanLinearization](../Quantum/Matrix/AlternativeMeanLinearization.md)
