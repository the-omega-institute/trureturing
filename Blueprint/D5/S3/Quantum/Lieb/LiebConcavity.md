# LiebConcavity

## Abstract

Attributed Lieb joint trace concavity for positive-definite inputs and interior exponents.

**Theorem 1.1 (Joint trace convexity on positive-definite pairs).**

$$\forall u: \operatorname{Level},\ H: \operatorname{Type}(u),\ [\operatorname{NormedAddCommGroup}(H)], [\operatorname{InnerProductSpace}(\mathbb{C}, H)], [\operatorname{CompleteSpace}(H)], [\operatorname{Nontrivial}(H)], [\operatorname{FiniteDimensional}(\mathbb{C}, H)], s: \mathbb{R}, K: \operatorname{L}(H),\ 1 \le s \land s \le 2 \implies \operatorname{JointlyConvexOn}(\operatorname{pdSet}(H), \operatorname{pdSet}(H), \operatorname{liebTraceMap}(H, s, K)).$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Lieb/LiebConcavity.liebTrace_jointlyConvexOn_pdSet` (`✓ std3`). ∎

*Citation.* Kei Tsukamoto, Kento Mori, Hayata Yamasaki (2026). *Lieb-Ando trace curvature and operator power convexity in Physlib*. URL: <https://github.com/leanprover-community/physlib/blob/b9043cc548ef6d63a28454cf3a57fb12a0c2e142/QuantumInfo/ForMathlib/HayataGroup/TraceInequality/LiebAndoTrace.lean>.

*Commentary.*

This is the exact Physlib endpoint from original line 1118, with unchanged proof text, arbitrary K and 1 <= s <= 2. TracePerspectiveConvexity consumes this interface. The carrier is a complete nontrivial finite complex Hilbert space, and both inputs have strictly positive spectra. Neither K invertibility nor A/B commutation is assumed. Its operator-power and perspective suppliers come from the same immutable pin.

**Theorem 1.2 (Joint trace concavity on positive-definite pairs).**

$$\forall u: \operatorname{Level},\ H: \operatorname{Type}(u),\ [\operatorname{NormedAddCommGroup}(H)], [\operatorname{InnerProductSpace}(\mathbb{C}, H)], [\operatorname{CompleteSpace}(H)], [\operatorname{Nontrivial}(H)], [\operatorname{FiniteDimensional}(\mathbb{C}, H)], s: \mathbb{R}, K: \operatorname{L}(H),\ 0 < s \land s < 1 \implies \operatorname{JointlyConcaveOn}(\operatorname{pdSet}(H), \operatorname{pdSet}(H), \operatorname{liebTraceMap}(H, s, K)).$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Lieb/LiebConcavity.liebTrace_jointlyConcaveOn_pdSet` (`✓ std3`). ∎

*Citation.* Kei Tsukamoto, Kento Mori, Hayata Yamasaki (2026). *Lieb-Ando trace curvature and operator power convexity in Physlib*. URL: <https://github.com/leanprover-community/physlib/blob/b9043cc548ef6d63a28454cf3a57fb12a0c2e142/QuantumInfo/ForMathlib/HayataGroup/TraceInequality/LiebAndoTrace.lean>.

*Commentary.*

The exponent s satisfies 0 < s < 1. The carrier is a nontrivial complete finite-dimensional complex Hilbert space. K is arbitrary; A and B are self-adjoint with strictly positive spectra. Original A and B need not commute. Both arguments use the same convex-mixture coefficient.

The unchanged attributed supplier proof evaluates a jointly concave Hilbert-Schmidt operator perspective against the adjoint of K. The left and right multiplication operators commute for arbitrary A and B. The real trace functional is defined in the consumed bridge module.

Use s = 1 - p, exchange the input arguments, and apply trace cyclicity to obtain the interior-exponent positive-definite form with the adjoint of K, A to exponent p, K and B to exponent 1 - p in that order. The retained endpoint has this strict-PD and interior-exponent scope.

A separate transient exact application was compiled for every finite decidable index type d, including the empty type. For arbitrary complex d-by-d K, positive-semidefinite A1, A2, B1, B2, and p and t in [0,1], put T_p(A,B) = Re Tr(K* A^p K B^(1-p)). Then (1-t) T_p(A1,B1) + t T_p(A2,B2) is at most T_p((1-t) A1 + t A2, (1-t) B1 + t B2). Original A and B need not commute. Here the powers are the spectral CFC powers, with A^0 = I for positive-semidefinite A.

The matrix-to-Euclidean-operator star algebra equivalence preserves powers and traces. For 0 < p < 1, applying the supplier to A + epsilon I and B + epsilon I and taking epsilon down to zero uses the pinned CFC continuity for positive powers on the full PSD cone. At p = 0 and p = 1 the functional is linear in B and A respectively. An empty index type has zero trace. The exact full application passed Lean compilation and a scoped compiled report with only propext, Classical.choice and Quot.sound; its source and evidence are retained in the persistent operator-perspective-lieb-continuation-20261011 research directory. Its temporary D5 source is removed after validation because the application is reuse rather than an independent new result.

This is reuse of the Apache-2.0 Physlib source at revision b9043cc548ef6d63a28454cf3a57fb12a0c2e142, credited to Kei Tsukamoto, Kento Mori and Hayata Yamasaki. Lieb's theorem is known; no mathematical originality is claimed. The selected transient trace-equivalence bridge credits Alex Meiburg and retains its MIT notice and license.

## References

- Truth anchor: `D5/S3/Quantum/Lieb/LiebConcavity.liebTrace_jointlyConcaveOn_pdSet`
- Truth anchor: `D5/S3/Quantum/Lieb/LiebConcavity.liebTrace_jointlyConvexOn_pdSet`
- Dependency: [D5/S3/Quantum/Lieb/LiebBridge](LiebBridge.md)
