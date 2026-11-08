# Inverse-power line: PowerPacking

## Abstract

Inverse-power equilibrium rigidity on the real line.

**Theorem 1.1 (window gap mass).**

$$\forall\,\left(a\,:\,\mathbb{Z}\,\to\,\mathbb{R}\right)\,,\,\left(\operatorname{StrictMono}\,a\right)\,\to\,\forall\,\left(r\,R\,:\,\mathbb{R}\right)\,,\,\left(1\,\le\,r\right)\,\to\,\left(0\,\le\,R\right)\,\to\,\left(\forall\,j\,:\,\mathbb{Z}\,,\,a\,\left(j\,+\,1\right)\,-\,a\,j\,\le\,r\,\cdot\,\left(a\,j\,-\,a\,\left(j\,-\,1\right)\right)\right)\,\to\,\forall\,\left(m\,k\,:\,\mathbb{Z}\right)\,,\,\left(m\,<\,k\right)\,\to\,\left(|\,a\,m\,|\,\le\,2\,\cdot\,R\right)\,\to\,\left(|\,a\,k\,|\,\le\,2\,\cdot\,R\right)\,\to\,\forall\,\left(S\,:\,\operatorname{Finset}\,\mathbb{Z}\right)\,,\,\left(\forall\,j\,\in\,S\,,\,|\,a\,j\,|\,\le\,2\,\cdot\,R\right)\,\to\,\left(\sum_{j\,\in\,S}\,\left(a\,\left(j\,+\,1\right)\,-\,a\,j\right)\right)\,\le\,\left(4\,+\,4\,\cdot\,r\right)\,\cdot\,R$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/InversePowerLinePowerPacking.window_gap_mass` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Alper Ferudun (2026). *Equilibria of Inverse-Square Repulsion on the Line Are Arithmetic Progressions*. DOI: [10.48550/arXiv.2610.06944](https://doi.org/10.48550/arXiv.2610.06944). URL: <https://arxiv.org/abs/2610.06944v1>.

*Commentary.*

The total consecutive-gap length starting in a coordinate window is at most the displayed linear bound; the ratio controls the last gap extending beyond the window.

**Theorem 1.2 (full weighted distance).**

$$\forall\,\left(a\,:\,\mathbb{Z}\,\to\,\mathbb{R}\right)\,,\,\left(\operatorname{StrictMono}\,a\right)\,\to\,\forall\,\left(r\,s\,\delta\,:\,\mathbb{R}\right)\,,\,\left(1\,\le\,r\right)\,\to\,\left(2\,<\,s\right)\,\to\,\left(0\,<\,\delta\right)\,\to\,\left(\forall\,j\,:\,\mathbb{Z}\,,\,a\,\left(j\,+\,1\right)\,-\,a\,j\,\le\,r\,\cdot\,\left(a\,j\,-\,a\,\left(j\,-\,1\right)\right)\right)\,\to\,\left(\forall\,j\,:\,\mathbb{Z}\,,\,a\,j\,-\,a\,\left(j\,-\,1\right)\,\le\,r\,\cdot\,\left(a\,\left(j\,+\,1\right)\,-\,a\,j\right)\right)\,\to\,\forall\,\left(n\,:\,\mathbb{Z}\right)\,,\,\left(\delta\,\le\,a\,\left(n\,+\,1\right)\,-\,a\,n\right)\,\to\,\left(\delta\,\le\,a\,n\,-\,a\,\left(n\,-\,1\right)\right)\,\to\,\operatorname{Summable}\,\left(\operatorname{fun}\,j\,:\,\mathbb{Z}\,\mapsto\,\left(a\,\left(j\,+\,1\right)\,-\,a\,j\right)\,\cdot\,|\,a\,j\,-\,a\,n\,|\,^{1\,-\,s}\right)\,\land\,\left(\sum'_{j\,:\,\mathbb{Z}}\,\left(a\,\left(j\,+\,1\right)\,-\,a\,j\right)\,\cdot\,|\,a\,j\,-\,a\,n\,|\,^{1\,-\,s}\right)\,\le\,\left(1\,+\,r\right)\,\cdot\,\left(\left(1\,+\,r\right)\,^{s\,-\,1}\,\cdot\,\delta\,^{2\,-\,s}\,/\,\left(s\,-\,2\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/InversePowerLinePowerPacking.full_weighted_distance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Alper Ferudun (2026). *Equilibria of Inverse-Square Repulsion on the Line Are Arithmetic Progressions*. DOI: [10.48550/arXiv.2610.06944](https://doi.org/10.48550/arXiv.2610.06944). URL: <https://arxiv.org/abs/2610.06944v1>.

*Commentary.*

Interval packing on both sides bounds the weighted inverse-power distance sum using only the two gaps next to the chosen particle and the adjacent-gap ratios.

**Theorem 1.3 (inverse power second moment).**

$$\forall\,\left(V\,:\,\operatorname{Type}\,*\right)\,,\,\forall\,\left(C\,:\,V\,\to\,V\,\to\,\mathbb{R}\right)\,,\,\left(\forall\,x\,y\,,\,0\,\le\,C\,x\,y\right)\,\to\,\forall\,\left(a\,g\,:\,V\,\to\,\mathbb{R}\right)\,,\,\forall\,\left(K\,B\,:\,\mathbb{R}\right)\,,\,\left(0\,\le\,K\right)\,\to\,\left(\forall\,x\,,\,0\,\le\,g\,x\right)\,\to\,\left(\forall\,x\,y\,,\,x\,\neq\,y\,\to\,C\,x\,y\,\le\,K\,\cdot\,g\,x\,\cdot\,g\,y\,\cdot\,|\,a\,y\,-\,a\,x\,|\,^{-\,B\,-\,1}\right)\,\to\,\left(\operatorname{Function}\,.\,\operatorname{Injective}\,a\right)\,\to\,\forall\,\left(x\,:\,V\right)\,,\,\left(\operatorname{Summable}\,\left(\operatorname{fun}\,y\,\mapsto\,g\,y\,\cdot\,|\,a\,y\,-\,a\,x\,|\,^{1\,-\,B}\right)\right)\,\to\,\operatorname{Summable}\,\left(\operatorname{fun}\,y\,\mapsto\,C\,x\,y\,\cdot\,\left(a\,x\,-\,a\,y\right)\,^{2}\right)\,\land\,\left(\sum'_{y}\,C\,x\,y\,\cdot\,\left(a\,x\,-\,a\,y\right)\,^{2}\right)\,\le\,K\,\cdot\,g\,x\,\cdot\,\left(\sum'_{y}\,g\,y\,\cdot\,|\,a\,y\,-\,a\,x\,|\,^{1\,-\,B}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/InversePowerLinePowerPacking.inverse_power_second_moment` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Alper Ferudun (2026). *Equilibria of Inverse-Square Repulsion on the Line Are Arithmetic Progressions*. DOI: [10.48550/arXiv.2610.06944](https://doi.org/10.48550/arXiv.2610.06944). URL: <https://arxiv.org/abs/2610.06944v1>.

*Commentary.*

A pointwise inverse-power conductance bound and a summable weighted-distance family give the displayed summable second moment and its bound.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/InversePowerLinePowerPacking.full_weighted_distance`
- Truth anchor: `D5/S3/StatisticalMechanics/InversePowerLinePowerPacking.inverse_power_second_moment`
- Truth anchor: `D5/S3/StatisticalMechanics/InversePowerLinePowerPacking.window_gap_mass`
