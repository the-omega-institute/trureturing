# Normalized moments on a multiplicative window

## Abstract

Concentration of normalized Laplace moments outside a critical window

**Theorem 1.1 (An explicit moment order controls both tails).**

$$\forall a \in \mathbb{R},\; 1 \le a \Rightarrow \left(\forall g \in \mathbb{R} \to \mathbb{R},\; \operatorname{Measurable}\left(g\right) \Rightarrow \left(\forall M \in \mathbb{R},\; \left(\forall u \in \mathbb{R},\; 0 \le u \Rightarrow \left|g\left(u\right)\right| \le M \cdot \operatorname{exp}\left(2 \cdot u\right)\right) \Rightarrow \begin{aligned}\operatorname{let} k := \left\lfloor640 \cdot a\right\rfloor,\\\operatorname{let} f := (u \mapsto \left|g\left(u\right)\right| \cdot \frac{u^{k} \cdot \operatorname{exp}\left(-\left(512 \cdot u\right)\right)}{k!}),\\\operatorname{let} S := (0,\infty) \setminus [a,\frac{3 \cdot a}{2}],\\a \le k \land \left(\operatorname{IntegrableOn}\left(f, S\right) \land \int_{S} f\left(u\right) du \le M \cdot \left(\frac{1}{542} + \frac{1}{478}\right) \cdot 512^{-k}\right)\end{aligned}\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Laplace/CriticalGammaWindow.critical_window_off_mass` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

After the growth bound, the remaining damping rate is 510. On the left tail use rate 542 with multiplier exp(32a). On the right use rate 478 with multiplier exp(−48a). Extending each positive majorant to the whole positive half-line gives r to the power −(k+1) by the Gamma integral.

The inequalities 640a−1 ≤ k ≤ 640a and the elementary logarithmic bounds absorb the two multipliers. The left and right contributions are at most M times 512 to the power −k divided by 542 and 478 respectively.

**Theorem 1.2 (Both tails at an adjustable order and width).**

$$\forall h \in \mathbb{R},\; \forall b \in \mathbb{R},\; \left(1 < h \land h < b\right) \Rightarrow \left(\left(\forall T \in \mathbb{R},\; \exists C \in \mathbb{R},\; \forall s \in \mathbb{R},\; C \le s \Rightarrow \left(2 < s \cdot (1-\frac{h}{b}) \land \left(T < (s \cdot \left((h \cdot \operatorname{log}\left(h\right)-h) + 1\right)-2) \land T < (s \cdot ((b-h)-h \cdot \operatorname{log}\left(\frac{b}{h}\right))-2 \cdot b)\right)\right)\right) \land \left(\forall s \in \mathbb{R},\; 2 < s \cdot (1-\frac{h}{b}) \Rightarrow \left(\forall a \in \mathbb{R},\; 0 < a \Rightarrow \left(\forall g \in \mathbb{R} \to \mathbb{R},\; \operatorname{Measurable}\left(g\right) \Rightarrow \left(\forall M \in \mathbb{R},\; \left(\forall u \in \mathbb{R},\; 0 \le u \Rightarrow \left|g\left(u\right)\right| \le M \cdot \operatorname{exp}\left(2 \cdot u\right)\right) \Rightarrow \begin{aligned}\operatorname{let} k := \left\lfloor{s \cdot h \cdot a}\right\rfloor,\\\operatorname{let} S := (0,\infty) \setminus [a,b \cdot a],\\\operatorname{let} f := (u \mapsto \left|g\left(u\right)\right| \cdot \frac{u^{k} \cdot \operatorname{exp}\left(-\left(s \cdot u\right)\right)}{k!}),\\\operatorname{IntegrableOn}\left(f, S\right) \land \int_{S} f\left(u\right) du \le M \cdot s^{-k} \cdot \left(\frac{\operatorname{exp}\left(-\left((s \cdot \left((h \cdot \operatorname{log}\left(h\right)-h) + 1\right)-2) \cdot a\right)\right)}{s} + \frac{b}{h \cdot s} \cdot \operatorname{exp}\left(-\left((s \cdot ((b-h)-h \cdot \operatorname{log}\left(\frac{b}{h}\right))-2 \cdot b) \cdot a\right)\right)\right)\end{aligned}\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Laplace/CriticalGammaWindow.adjustable_window_off_mass` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix 1 < h < b. The left decay rate is σ(h log h − h + 1) − 2. The right decay rate is σ(b − h − h log(b/h)) − 2b. Strictness in the logarithmic inequality log x < x − 1 gives positive slopes for both rates. Every prescribed lower bound therefore holds for both at all sufficiently large σ. The choice of σ may depend on how close h is to b.

For a positive cutoff a choose k = floor(σha). On the left tail, tilt to hσ and use σha < k+1. On the right tail, tilt to hσ/b and use k ≤ σha. Extending the tilted densities to the positive axis gives the Gamma integral at each rate. After factoring out M times σ to the power −k, the two exponentials carry prefactors 1/σ and b/(hσ). The estimate applies even when k is zero.

## References

- Truth anchor: `D5/S3/Analytic/Laplace/CriticalGammaWindow.adjustable_window_off_mass`
- Truth anchor: `D5/S3/Analytic/Laplace/CriticalGammaWindow.critical_window_off_mass`
