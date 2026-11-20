# Concentration at a fixed multiplicative width

## Abstract

Concentration of normalized Laplace moments outside a critical window

**Theorem 1.1 (An explicit moment order controls both tails).**

$$\forall a \in \mathbb{R},\; 1 \le a \Rightarrow \left(\forall g \in \mathbb{R} \to \mathbb{R},\; \operatorname{Measurable}\left(g\right) \Rightarrow \left(\forall M \in \mathbb{R},\; \left(\forall u \in \mathbb{R},\; 0 \le u \Rightarrow \left|g\left(u\right)\right| \le M \cdot \operatorname{exp}\left(2 \cdot u\right)\right) \Rightarrow \begin{aligned}\operatorname{let} k := \left\lfloor640 \cdot a\right\rfloor,\\\operatorname{let} f := (u \mapsto \left|g\left(u\right)\right| \cdot \frac{u^{k} \cdot \operatorname{exp}\left(-\left(512 \cdot u\right)\right)}{k!}),\\\operatorname{let} S := (0,\infty) \setminus [a,\frac{3 \cdot a}{2}],\\a \le k \land \left(\operatorname{IntegrableOn}\left(f, S\right) \land \int_{S} f\left(u\right) du \le M \cdot \left(\frac{1}{542} + \frac{1}{478}\right) \cdot 512^{-k}\right)\end{aligned}\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Laplace/CriticalGammaWindow.critical_window_off_mass` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

After the growth bound, the remaining damping rate is 510. On the left tail use rate 542 with multiplier exp(32a). On the right use rate 478 with multiplier exp(−48a). Extending each positive majorant to the whole positive half-line gives r to the power −(k+1) by the Gamma integral.

The inequalities 640a−1 ≤ k ≤ 640a and the elementary logarithmic bounds absorb the two multipliers. The left and right contributions are at most M times 512 to the power −k divided by 542 and 478 respectively.

## References

- Truth anchor: `D5/S3/Analytic/Laplace/CriticalGammaWindow.critical_window_off_mass`
