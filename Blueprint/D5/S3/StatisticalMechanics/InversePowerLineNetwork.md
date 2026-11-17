# Inverse-power line: Network

## Abstract

Inverse-power equilibrium rigidity on the real line.

**Definition 1.1 (energy).**

$$\forall\,\left(V\,:\,\operatorname{Type}\,*\right)\,,\,\forall\,\left(C\,:\,V\,\to\,V\,\to\,\mathbb{R}\right)\,,\,\forall\,\left(f\,:\,V\,\to\,\mathbb{R}\right)\,,\,\left(\operatorname{energy}\,C\,f\,=\,\left(1\,/\,2\right)\,\cdot\,\sum'_{p\,:\,V\,\times\,V}\,C\,p\,.\,1\,p\,.\,2\,\cdot\,\left(f\,p\,.\,1\,-\,f\,p\,.\,2\right)\,^{2}\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/InversePowerLineNetwork.energy` (`✓ std3`).

*Citation.* Alper Ferudun (2026). *Equilibria of Inverse-Square Repulsion on the Line Are Arithmetic Progressions*. DOI: [10.48550/arXiv.2610.06944](https://doi.org/10.48550/arXiv.2610.06944). URL: <https://arxiv.org/abs/2610.06944v1>.

*Commentary.*

Section 3 (p. 4): “The energy of f : V → ℝ is ℰc(f) = ½ ∑x,y c(x,y)(f(x) − f(y))² ∈ [0,∞].” Here energy is the real-valued tsum expression. The estimates prove summability for every finitely supported function to which the expression is applied. Both endpoints belong to the displayed vertex type; restricting that type to a sublevel omits boundary edges. No equality with extended infinite energy is asserted when the series is not summable.

**Theorem 1.2 (summable finite rows).**

$$\forall\,\left(V\,W\,:\,\operatorname{Type}\,*\right)\,,\,\forall\,\left(S\,:\,\operatorname{Finset}\,V\right)\,,\,\forall\,\left(F\,:\,V\,\times\,W\,\to\,\mathbb{R}\right)\,,\,\left(\forall\,x\,,\,\operatorname{Summable}\,\left(\operatorname{fun}\,y\,\mapsto\,F\,\left(x\,,\,y\right)\right)\right)\,\to\,\left(\forall\,x\,,\,x\,\neg\in\,S\,\to\,\forall\,y\,,\,F\,\left(x\,,\,y\right)\,=\,0\right)\,\to\,\operatorname{Summable}\,F$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/InversePowerLineNetwork.summable_finite_rows` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Alper Ferudun (2026). *Equilibria of Inverse-Square Repulsion on the Line Are Arithmetic Progressions*. DOI: [10.48550/arXiv.2610.06944](https://doi.org/10.48550/arXiv.2610.06944). URL: <https://arxiv.org/abs/2610.06944v1>.

*Commentary.*

A family on a product is summable when every row is summable and only finitely many rows can be nonzero.

**Theorem 1.3 (energy summable).**

$$\forall\,\left(V\,:\,\operatorname{Type}\,*\right)\,,\,\forall\,\left(C\,:\,V\,\to\,V\,\to\,\mathbb{R}\right)\,,\,\left(\forall\,x\,y\,,\,C\,x\,y\,=\,C\,y\,x\right)\,\to\,\left(\forall\,x\,y\,,\,0\,\le\,C\,x\,y\right)\,\to\,\left(\forall\,x\,,\,\operatorname{Summable}\,\left(C\,x\right)\right)\,\to\,\forall\,\left(f\,:\,V\,\to\,\mathbb{R}\right)\,,\,\forall\,\left(S\,:\,\operatorname{Finset}\,V\right)\,,\,\left(\forall\,x\,,\,x\,\neg\in\,S\,\to\,f\,x\,=\,0\right)\,\to\,\operatorname{Summable}\,\left(\operatorname{fun}\,p\,:\,V\,\times\,V\,\mapsto\,C\,p\,.\,1\,p\,.\,2\,\cdot\,\left(f\,p\,.\,1\,-\,f\,p\,.\,2\right)\,^{2}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/InversePowerLineNetwork.energy_summable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Alper Ferudun (2026). *Equilibria of Inverse-Square Repulsion on the Line Are Arithmetic Progressions*. DOI: [10.48550/arXiv.2610.06944](https://doi.org/10.48550/arXiv.2610.06944). URL: <https://arxiv.org/abs/2610.06944v1>.

*Commentary.*

A symmetric nonnegative conductance with summable rows gives summable energy terms for every finitely supported real function.

**Theorem 1.4 (harmonic constant of sublevel capacity zero).**

$$\forall\,\left(V\,:\,\operatorname{Type}\,*\right)\,,\,\forall\,\left(C\,:\,V\,\to\,V\,\to\,\mathbb{R}\right)\,,\,\left(\forall\,x\,y\,,\,C\,x\,y\,=\,C\,y\,x\right)\,\to\,\left(\forall\,x\,y\,,\,0\,\le\,C\,x\,y\right)\,\to\,\left(\forall\,x\,y\,,\,x\,\neq\,y\,\to\,0\,<\,C\,x\,y\right)\,\to\,\left(\forall\,x\,,\,\operatorname{Summable}\,\left(C\,x\right)\right)\,\to\,\forall\,\left(h\,:\,V\,\to\,\mathbb{R}\right)\,,\,\left(\forall\,x\,,\,0\,<\,h\,x\right)\,\to\,\left(\forall\,x\,,\,\operatorname{Summable}\,\left(\operatorname{fun}\,y\,\mapsto\,C\,x\,y\,\cdot\,h\,y\right)\right)\,\to\,\left(\forall\,x\,,\,\left(\sum'_{y}\,C\,x\,y\,\cdot\,h\,y\right)\,=\,\left(\sum'_{y}\,C\,x\,y\right)\,\cdot\,h\,x\right)\,\to\,\left(\forall\,M\,:\,\mathbb{R}\,,\,0\,<\,M\,\to\,\left(\exists\,y\,:\,V\,,\,M\,<\,h\,y\right)\,\to\,\forall\,\operatorname{x0}\,:\,\{x\,:\,V\,//\,h\,x\,\le\,M\}\,,\,\forall\,\varepsilon\,:\,\mathbb{R}\,,\,0\,<\,\varepsilon\,\to\,\exists\,\left(S\,:\,\operatorname{Finset}\,\{x\,:\,V\,//\,h\,x\,\le\,M\}\right)\,\left(f\,:\,\{x\,:\,V\,//\,h\,x\,\le\,M\}\,\to\,\mathbb{R}\right)\,,\,\left(\forall\,x\,,\,x\,\neg\in\,S\,\to\,f\,x\,=\,0\right)\,\land\,f\,\operatorname{x0}\,=\,1\,\land\,\operatorname{energy}\,\left(\operatorname{fun}\,x\,y\,\mapsto\,C\,x\,.\,\operatorname{val}\,y\,.\,\operatorname{val}\right)\,f\,<\,\varepsilon\right)\,\to\,\forall\,x\,y\,,\,h\,x\,=\,h\,y$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/InversePowerLineNetwork.harmonic_constant_of_sublevel_capacity_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Alper Ferudun (2026). *Equilibria of Inverse-Square Repulsion on the Line Are Arithmetic Progressions*. DOI: [10.48550/arXiv.2610.06944](https://doi.org/10.48550/arXiv.2610.06944). URL: <https://arxiv.org/abs/2610.06944v1>.

*Commentary.*

A positive harmonic function is constant when conductances between distinct vertices are positive, the indicated rows converge, and every proper positive sublevel has zero induced capacity.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/InversePowerLineNetwork.energy`
- Truth anchor: `D5/S3/StatisticalMechanics/InversePowerLineNetwork.energy_summable`
- Truth anchor: `D5/S3/StatisticalMechanics/InversePowerLineNetwork.harmonic_constant_of_sublevel_capacity_zero`
- Truth anchor: `D5/S3/StatisticalMechanics/InversePowerLineNetwork.summable_finite_rows`
