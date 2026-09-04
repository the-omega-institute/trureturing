# A Nontrivial Zero in Every Fixed-Width Window

## Abstract

Every sufficiently high window of one fixed width contains a nontrivial zeta zero.

This is a quantitative zero-distribution statement. The frozen unconditional explicit formula along the cosine packet gives the logarithmic lower bound, while the frozen local zero-count upper bound controls the zero-side tail. Together they show that every window of fixed width 2R at height T at least T0 contains a nontrivial zero.

The constants R and T0 are existential absolute constants determined by the proof's constants; no numerical value is claimed. Nothing is asserted about the real parts of these zeros. This is not a proof of the Riemann hypothesis.

The resulting fixed-width statement is weaker than the classical Littlewood gap bound, but its proof is closed inside this repository.

**Theorem 1.1 (The explicit-formula right side has a logarithmic lower bound).**

$$\exists c \in \mathbb{R}, M \in \mathbb{R}, T1 \in \mathbb{R},\; 0 < c \land \left(\forall T \in \mathbb{R},\; T1 \le T \Rightarrow c \cdot \log(T + 3) - M \le \Re(\operatorname{literatureRHS}\left(\operatorname{cosineModulation}\left(packetSquare, T\right)\right))\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZeroInfinitude/WindowZero.literatureRHS_re_lower_log` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The Archimedean packet contribution supplies a positive multiple of log(T+3). The two pole evaluations vanish and the fixed-support prime contribution is uniformly bounded, so all remaining terms enter one constant M.

**Theorem 1.2 (A fixed gap radius makes the shifted zero tail small).**

$$\forall iota \in Type, gamma \in iota \to \mathbb{R}, m \in iota \to \mathbb{N}, A0 \in \mathbb{R}, epsilon \in \mathbb{R},\; \left(\operatorname{LocalCount}\left(gamma, m, A0\right) \land 0 < epsilon\right) \Rightarrow \left(\exists R \in \mathbb{R},\; 2 \le R \land \left(\forall T \in \mathbb{R},\; \left(\forall rho \in iota,\; R \le \left|gamma\left(rho\right) - T\right|\right) \Rightarrow \left(\operatorname{Summable}\left((rho: iota \mapsto \frac{m\left(rho\right)}{1 + (gamma\left(rho\right) - T)^{2}})\right) \land \sum_{rho \in iota} \frac{m\left(rho\right)}{1 + (gamma\left(rho\right) - T)^{2}} \le 4 \cdot A0 \cdot \left(epsilon \cdot \log(\left|T\right| + 3) + totalWeight\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZeroInfinitude/WindowZero.exists_radius_shifted_inv_sq_tsum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive epsilon, unit-window grouping and the local count bound select one radius R at least two. Under an R-gap, the full nonnegative multiplicity-weighted inverse-square series is summable and its logarithmic coefficient is at most 4 A0 epsilon.

**Theorem 1.3 (Every sufficiently high fixed-width window contains a zero).**

$$\exists R \in \mathbb{R}, T0 \in \mathbb{R},\; 0 < R \land \left(\forall T \in \mathbb{R},\; T0 \le T \Rightarrow \left(\exists rho \in \operatorname{carrier}\left(zetaZeroConfig\right),\; \left|\operatorname{Im}\left(rho\right) - T\right| \le R\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZeroInfinitude/WindowZero.exists_zero_near_every_large_height` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Choose epsilon from the positive logarithmic coefficient and the frozen decay and local-count constants. A zero-free window would then force the zero side below half the logarithmic growth of the explicit-formula right side, contradicting their unconditional equality.

## References

- Truth anchor: `D5/S3/Weil/ZeroInfinitude/WindowZero.exists_radius_shifted_inv_sq_tsum`
- Truth anchor: `D5/S3/Weil/ZeroInfinitude/WindowZero.exists_zero_near_every_large_height`
- Truth anchor: `D5/S3/Weil/ZeroInfinitude/WindowZero.literatureRHS_re_lower_log`
- Dependency: [D5/S3/Weil/ZeroInfinitude/ArchimedeanDivergence](ArchimedeanDivergence.md)
- Dependency: [D5/S3/Weil/ZeroInfinitude/CosinePacket](CosinePacket.md)
- Dependency: [D5/S3/Weil/ZeroInfinitude/ExplicitFormulaObstruction](ExplicitFormulaObstruction.md)
