# Sharp Bragg Zero-Free Disk

## Abstract

A positive Bragg peak and its Bernstein variation bound determine a sharp zero-free disk.

**Theorem 1.1 (The finite Bragg radius is zero-free and sharp).**

$$\forall P: \mathbb{C} \to \mathbb{C}, z_{0}\in\mathbb{C}, T, \varphi, c\in\mathbb{R},\\{}T>0, \varphi>0, c>0,\ \left|\operatorname{P}\left(z_{0}\right)\right| \geq T \cdot c,\\{}(\forall w\in\mathbb{C}, \left|\operatorname{P}\left(w\right) - \operatorname{P}\left(z_{0}\right)\right| \leq e \cdot T \cdot \left(\varphi \cdot T + 2\right) \cdot \left|w - z_{0}\right|)\\{}\Rightarrow ((\forall w\in\mathbb{C}, \left|w - z_{0}\right| < \frac{c}{e \cdot \left(\varphi \cdot T + 2\right)} \Rightarrow \operatorname{P}\left(w\right) \neq 0) \land z_{0}\in\operatorname{B}\left(z_{0}, \frac{c}{e \cdot \left(\varphi \cdot T + 2\right)}\right) \land \operatorname{P}\left(z_{0}\right) \neq 0) \land\\{}\exists Q: \mathbb{C} \to \mathbb{C}, \exists w_{*}\in\mathbb{C}, \left|\operatorname{Q}\left(0\right)\right| = T \cdot c \land (\forall w\in\mathbb{C}, \left|\operatorname{Q}\left(w\right) - \operatorname{Q}\left(0\right)\right| = e \cdot T \cdot \left(\varphi \cdot T + 2\right) \cdot \left|w\right|) \land\\{}\left|w_{*}\right| = \frac{c}{e \cdot \left(\varphi \cdot T + 2\right)} \land \operatorname{Q}\left(w_{*}\right) = 0.$$

*Proof.* Machine-checked in Lean as `D5/S0/Asymptotics/Interference/BraggZeroFreeDisk.bragg_zero_free_disk` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let c denote the positive magnitude of the relevant Fourier-Bohr coefficient. The peak lower bound is T c, while the Bernstein estimate supplies Lipschitz constant L = e T (phi T + 2). Their quotient is the exact finite radius r = c/(e(phi T + 2)).

Inside the open disk, the maximum possible variation from the center is strictly smaller than T c. The reverse triangle inequality therefore prevents the function from vanishing there.

The linear profile Q(w) = T c - L w has the same central height and exact Lipschitz constant, and it vanishes at distance r. This boundary witness shows that the strict disk cannot be enlarged uniformly from only the two quantitative hypotheses.

The source's c/(e phi T)(1+o(1)) is an asymptotic rewrite. This theorem retains the finite +2 term and explicitly assumes T, phi, and c positive, excluding totalized-division degeneracies.

## References

- Truth anchor: `D5/S0/Asymptotics/Interference/BraggZeroFreeDisk.bragg_zero_free_disk`
