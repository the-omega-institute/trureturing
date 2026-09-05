# Logarithmic Zero Count in Every Fixed-Width Window

## Abstract

Every sufficiently high fixed-width window contains at least a positive multiple of log T nontrivial zeta zeros, counted with multiplicity.

This is a logarithmic lower bound on the multiplicity-weighted zero count in every fixed-width window at large height. It is obtained from the same cosine-packet explicit-formula estimate as WindowZero by splitting the zero side into the window and its complement.

Together with the frozen local upper bound zetaZeroConfig_local_count, this pins the true order log T of the window count. The constants R, T0, and c-prime are existential absolute constants; no numerical value is claimed.

Nothing is asserted about real parts of the zeros. This is not a proof of the Riemann hypothesis.

**Theorem 1.1 (One fixed radius controls every shifted complement tail).**

$$\forall iota \in Type, gamma \in iota \to \mathbb{R}, m \in iota \to \mathbb{N}, A0 \in \mathbb{R}, epsilon \in \mathbb{R},\; \left(\operatorname{LocalCount}\left(gamma, m, A0\right) \land 0 < epsilon\right) \Rightarrow \left(\exists R \in \mathbb{R},\; 2 \le R \land \left(\forall T \in \mathbb{R}, s \in \operatorname{Finset}\left(iota\right),\; \left(\forall rho \in iota,\; \left(\neg rho \in s\right) \Rightarrow R \le \left|gamma\left(rho\right) - T\right|\right) \Rightarrow \left(\operatorname{Summable}\left((rho: \left\{\neg rho \in s \mid rho \in iota\right\} \mapsto \frac{m\left(rho\right)}{1 + (gamma\left(rho\right) - T)^{2}})\right) \land \sum_{rho \in \left\{\neg rho \in s \mid rho \in iota\right\}} \frac{m\left(rho\right)}{1 + (gamma\left(rho\right) - T)^{2}} \le 4 \cdot A0 \cdot \left(epsilon \cdot \log(\left|T\right| + 3) + totalWeight\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZeroInfinitude/WindowCount.exists_radius_shifted_inv_sq_tsum_compl` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The frozen finite-subfamily estimate is applied to every finite subset of the window complement. Nonnegativity then yields summability and the same logarithmic tail bound for the full complement series.

**Theorem 1.2 (The zero side splits into a window count and a logarithmic tail).**

$$\forall K \in \mathbb{R}, A0 \in \mathbb{R}, epsilon \in \mathbb{R},\; \left(0 \le K \land \left(\left(\forall z \in \mathbb{C},\; \left|\operatorname{Im}\left(z\right)\right| \le \frac{1}{2} \Rightarrow \left\lVert \operatorname{paperFT}\left(packetSquare, z\right) \right\rVert \le \frac{K}{1 + (\operatorname{Re}\left(z\right))^{2}}\right) \land \left(\operatorname{LocalCount}\left((rho: \operatorname{carrier}\left(zetaZeroConfig\right) \mapsto \operatorname{Im}\left(rho\right)), (rho: \operatorname{carrier}\left(zetaZeroConfig\right) \mapsto \operatorname{mult}\left(zetaZeroConfig, rho\right)), A0\right) \land 0 < epsilon\right)\right)\right) \Rightarrow \left(\exists R \in \mathbb{R},\; 2 \le R \land \left(\forall T \in \mathbb{R},\; 0 \le T \Rightarrow \left\lVert \sum_{rho \in \operatorname{carrier}\left(zetaZeroConfig\right)} \operatorname{mult}\left(zetaZeroConfig, rho\right) \cdot \operatorname{paperFT}\left(\operatorname{cosineModulation}\left(packetSquare, T\right), \operatorname{gammaOf}\left(rho\right)\right) \right\rVert \le K \cdot \operatorname{N}\left(zetaZeroConfig, T - R, T + R\right) + 4 \cdot K \cdot A0 \cdot \left(epsilon \cdot \log(T + 3) + totalWeight\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZeroInfinitude/WindowCount.zero_side_norm_le_window_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The central negative-frequency window and its conjugate image each have multiplicity sum N(T-R,T+R). The two complement series obey the fixed radius estimate, while closed-strip decay converts both pieces into the stated zero-side norm bound.

**Theorem 1.3 (Every large fixed-width window has logarithmically many zeros).**

$$\exists R, T_{0}, c' \in \mathbb{R},\ 0 < R \land 0 < c' \land \forall T \in \mathbb{R},\ T_{0} \leq T \Rightarrow c' \cdot \log(T + 3) \leq \operatorname{N}\left(zetaZeroConfig, T - R, T + R\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZeroInfinitude/WindowCount.window_count_lower_log` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Choose the complement-tail coefficient below the positive logarithmic coefficient in the frozen explicit-formula lower bound. For all large T, the remaining logarithmic mass must be carried by the central multiplicity-weighted window count.

## References

- Truth anchor: `D5/S3/Weil/ZeroInfinitude/WindowCount.exists_radius_shifted_inv_sq_tsum_compl`
- Truth anchor: `D5/S3/Weil/ZeroInfinitude/WindowCount.window_count_lower_log`
- Truth anchor: `D5/S3/Weil/ZeroInfinitude/WindowCount.zero_side_norm_le_window_count`
- Dependency: [D5/S3/Weil/ZeroInfinitude/WindowZero](WindowZero.md)
