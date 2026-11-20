# Inverse-diagonal lower bound for the reflecting heat grid

## Abstract

Inverse-diagonal lower bound for the reflecting heat grid

On n cells the physical generator takes the second difference with reflecting ghost cells and multiplies by n². Write Gₙ for this generator and Wₙ(T) for its observed Gramian. The cell mass is 1/n. The indices i range over Fin(n) and j,k over Fin(n−1). The symbol δⱼₖ is the Kronecker delta. The positive frequencies are j+1 for j in Fin(n−1). Their dimensionless rates qⱼ are 2−2 cos(π(j+1)/n), and their real cell-centered profiles are √2 cos(π(j+1)(i+1/2)/n).

**Theorem 1.1 (Physical eigenvalue with reflecting endpoints).**

$$G_{n}\left(\phi_{j}\right)\left(i\right)=-n^{2} q_{j} \phi_{j}\left(i\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Linear/ReflectingHeatStripBound.reflectingGenerator_cellMode` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At the endpoints the ghost cells repeat the adjacent cell values. Extending the cosine through the ghosts makes the same centered second-difference identity valid at every cell. The eigenvalue is −n²qⱼ.

**Theorem 1.2 (Zero cell mean).**

$$\sum_{i\in Fin\left(n\right)} \phi_{j}\left(i\right)=0$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Linear/ReflectingHeatStripBound.cellMode_sum_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The cosine sum from the geometric progression vanishes at each retained frequency.

**Theorem 1.3 (Mass orthonormality).**

$$\frac{\sum_{i\in Fin\left(n\right)} \phi_{j}\left(i\right)\phi_{k}\left(i\right)}{n}=\delta_{jk}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Linear/ReflectingHeatStripBound.cellMode_mass_inner` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The product-to-sum identity reduces the mass pairing to the sum and difference frequencies. The constant contribution gives one exactly on the diagonal.

**Theorem 1.4 (Heat evolution in mass coordinates).**

$$\begin{gathered}\frac{d}{dt} u\left(t, i\right)=G_{n}\left(u\left(t, \cdot\right)\right)\left(i\right)\\\sum_{i\in Fin\left(n\right)} u\left(t, i\right)=0\\\frac{\sum_{i\in Fin\left(n\right)} u\left(t, i\right)\phi_{j}\left(i\right)}{n}=c_{j} \exp\left(-n^{2} q_{j} t\right)\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Linear/ReflectingHeatStripBound.reflectingHeatFlow_spec` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each n and each real initial coefficient family c on Fin(n−1), let u be the sum of the modes with coefficients cⱼ exp(−n²qⱼt). At every real t and every cell i, its time derivative is the reflecting generator applied to u. The zero means and mass orthonormality of the modes give the other two identities.

**Theorem 1.5 (Finite strip lower bound on the physical inverse diagonal).**

$$\frac{n}{b_{j}} \frac{\prod_{k\in Fin\left(n-1\right)\setminus\{j\}} \frac{r_{j}+r_{k}}{\left|q_{j}-q_{k}\right|} \exp\left(\frac{-n a(r_{j}-q_{j})}{2}\right)}{\sqrt{n a}} \le \sqrt{(W_{n}\left(\frac{a}{n}\right)^{-1})_{jj}}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Linear/ReflectingHeatStripBound.inverse_diagonal_lower_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Observation at the first cell gives bⱼ = √(2−qⱼ/2), which is positive. The physical Gramian integrates products of bⱼ exp(−n²qⱼt) in Lebesgue time. Distinct rates and nonzero weights give invertibility on every positive window. Vanishing energy forces the synthesized exponential sum to vanish throughout the window. Sampling at successive equally spaced interior times then gives a Vandermonde system with distinct nodes.

For n ≥ 2, positive a and β, and any retained j, set T=a/n and rₖ = √(qₖ²+β²). Synthesize a signal using column j of the inverse Gramian. Multiplying that signal by bⱼ gives an exact Kronecker moment function whose L² norm is bⱼ times the square root of inverse entry (j,j). Apply the finite-window theorem at decay nodes n²q and strip parameter n²β. Homogeneity cancels n² in the node ratios, and the damping uses the scaled duration na. Dividing by the observed weight and writing the norm on this scale gives the factor n/bⱼ.

## References

- Truth anchor: `D5/S3/Observer/Linear/ReflectingHeatStripBound.cellMode_mass_inner`
- Truth anchor: `D5/S3/Observer/Linear/ReflectingHeatStripBound.cellMode_sum_zero`
- Truth anchor: `D5/S3/Observer/Linear/ReflectingHeatStripBound.inverse_diagonal_lower_bound`
- Truth anchor: `D5/S3/Observer/Linear/ReflectingHeatStripBound.reflectingGenerator_cellMode`
- Truth anchor: `D5/S3/Observer/Linear/ReflectingHeatStripBound.reflectingHeatFlow_spec`
- Dependency: [D5/S3/Analytic/Hardy/FiniteStripMomentBound](../../Analytic/Hardy/FiniteStripMomentBound.md)
