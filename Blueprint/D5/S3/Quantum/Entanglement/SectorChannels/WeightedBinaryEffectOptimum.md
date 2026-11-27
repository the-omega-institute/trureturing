# Exact weighted binary-effect optimum

## Abstract

A weighted interval of positive two-by-two effects has an exact nonlinear clipped-overlap optimum.

**Theorem 1.1 (The sharp two-piece loss in a positive matrix interval).**

Lean statement: `D5/S3/Quantum/Entanglement/SectorChannels/WeightedBinaryEffectOptimum.result`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/SectorChannels/WeightedBinaryEffectOptimum.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Take D=diag(a,b), with 0<b<=a and a^2+b^2=1, and w between zero and one half. Vary H with H and D-H positive semidefinite. Clip tr(H^2) at w and tr((D-H)^2) at 1-w. Twice one minus the sum of the clipped values has the stated minimum, and the theorem constructs H attaining it.

At fixed L=tr(DH), the two positive determinants bound tr(H^2) from above by the smaller of two quadratics in U=tr(H). One increases up to U=(L+ab)/(a+b); the other decreases above it. Thus the middle frontier is attained by two complementary rank-one terms. The two exterior ranges are bounded sharply by the positive trace-square inequality and a one-direction diagonal filter.

Set q=b^2. Below q the two cap crossings compete and the larger of w/q and 1-w/q gives the smaller deficit. Above q, the larger target cap is saturated on the middle arc. This exact finite-matrix result is used by the native channel theorem.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/SectorChannels/WeightedBinaryEffectOptimum.result`
