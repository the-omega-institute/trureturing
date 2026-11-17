# Inverse-power line: Conductance

## Abstract

Inverse-power equilibrium rigidity on the real line.

**Theorem 1.1 (equilibrium gap ratio).**

$$\forall\,\left(s\,:\,\mathbb{R}\right)\,,\,\left(2\,<\,s\right)\,\to\,\forall\,\left(a\,:\,\mathbb{Z}\,\to\,\mathbb{R}\right)\,,\,\left(\operatorname{StrictMono}\,a\right)\,\to\,\left(\forall\,n\,,\,\operatorname{HasSum}\,\left(\operatorname{indexedForce}\,s\,a\,n\right)\,0\right)\,\to\,\forall\,n\,:\,\mathbb{Z}\,,\,a\,\left(n\,+\,1\right)\,-\,a\,n\,\le\,2\,\cdot\,\left(a\,n\,-\,a\,\left(n\,-\,1\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/InversePowerLineConductance.equilibrium_gap_ratio` (`✓ std3`). ∎

*Citation.* Alper Ferudun (2026). *Equilibria of Inverse-Square Repulsion on the Line Are Arithmetic Progressions*. DOI: [10.48550/arXiv.2610.06944](https://doi.org/10.48550/arXiv.2610.06944). URL: <https://arxiv.org/abs/2610.06944v1>.

*Commentary.*

Zero signed forces bound each forward gap by twice the previous gap for real exponents greater than two.

**Theorem 1.2 (equilibrium gap reverse).**

$$\forall\,\left(s\,:\,\mathbb{R}\right)\,,\,\left(2\,<\,s\right)\,\to\,\forall\,\left(a\,:\,\mathbb{Z}\,\to\,\mathbb{R}\right)\,,\,\left(\operatorname{StrictMono}\,a\right)\,\to\,\left(\forall\,n\,,\,\operatorname{HasSum}\,\left(\operatorname{indexedForce}\,s\,a\,n\right)\,0\right)\,\to\,\forall\,n\,:\,\mathbb{Z}\,,\,a\,n\,-\,a\,\left(n\,-\,1\right)\,\le\,2\,\cdot\,\left(a\,\left(n\,+\,1\right)\,-\,a\,n\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/InversePowerLineConductance.equilibrium_gap_reverse` (`✓ std3`). ∎

*Citation.* Alper Ferudun (2026). *Equilibria of Inverse-Square Repulsion on the Line Are Arithmetic Progressions*. DOI: [10.48550/arXiv.2610.06944](https://doi.org/10.48550/arXiv.2610.06944). URL: <https://arxiv.org/abs/2610.06944v1>.

*Commentary.*

Reflection of the increasing sequence gives the reverse adjacent-gap bound.

**Theorem 1.3 (reciprocal transform).**

$$\forall\,\left(V\,:\,\operatorname{Type}\,*\right)\,,\,\forall\,\left(c\,:\,V\,\to\,V\,\to\,\mathbb{R}\right)\,,\,\forall\,\left(g\,:\,V\,\to\,\mathbb{R}\right)\,,\,\left(\forall\,x\,,\,0\,<\,g\,x\right)\,\to\,\left(\forall\,x\,,\,\operatorname{Summable}\,\left(c\,x\right)\right)\,\to\,\left(\forall\,x\,,\,\operatorname{Summable}\,\left(\operatorname{fun}\,y\,\mapsto\,c\,x\,y\,\cdot\,g\,y\right)\right)\,\to\,\left(\forall\,x\,,\,\left(\sum'_{y}\,c\,x\,y\,\cdot\,g\,y\right)\,=\,\left(\sum'_{y}\,c\,x\,y\right)\,\cdot\,g\,x\right)\,\to\,\left(\forall\,x\,,\,\operatorname{Summable}\,\left(\operatorname{fun}\,y\,\mapsto\,c\,x\,y\,\cdot\,g\,x\,\cdot\,g\,y\right)\right)\,\land\,\left(\forall\,x\,,\,\operatorname{Summable}\,\left(\operatorname{fun}\,y\,\mapsto\,\left(c\,x\,y\,\cdot\,g\,x\,\cdot\,g\,y\right)\,\cdot\,\left(g\,y\right)\,^{-1}\right)\right)\,\land\,\left(\forall\,x\,,\,\left(\sum'_{y}\,\left(c\,x\,y\,\cdot\,g\,x\,\cdot\,g\,y\right)\,\cdot\,\left(g\,y\right)\,^{-1}\right)\,=\,\left(\sum'_{y}\,c\,x\,y\,\cdot\,g\,x\,\cdot\,g\,y\right)\,\cdot\,\left(g\,x\right)\,^{-1}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/InversePowerLineConductance.reciprocal_transform` (`✓ std3`). ∎

*Citation.* Alper Ferudun (2026). *Equilibria of Inverse-Square Repulsion on the Line Are Arithmetic Progressions*. DOI: [10.48550/arXiv.2610.06944](https://doi.org/10.48550/arXiv.2610.06944). URL: <https://arxiv.org/abs/2610.06944v1>.

*Commentary.*

Multiplying a summable conductance by the product of a positive harmonic function at its endpoints makes its reciprocal harmonic, with the displayed row summability.

**Definition 1.4 (conductance).**

$$\forall\,\left(s\,:\,\mathbb{R}\right)\,,\,\forall\,\left(a\,:\,\mathbb{Z}\,\to\,\mathbb{R}\right)\,,\,\forall\,\left(n\,j\,:\,\mathbb{Z}\right)\,,\,\left(\operatorname{conductance}\,s\,a\,n\,j\,=\,\operatorname{if}\,n\,=\,j\,\operatorname{then}\,0\,\operatorname{else}\,\operatorname{if}\,|\,a\,j\,-\,a\,n\,|\,=\,|\,a\,\left(j\,+\,1\right)\,-\,a\,\left(n\,+\,1\right)\,|\,\operatorname{then}\,s\,\cdot\,|\,a\,j\,-\,a\,n\,|\,^{-\,s\,-\,1}\,\operatorname{else}\,\left(|\,a\,j\,-\,a\,n\,|\,^{-\,s}\,-\,|\,a\,\left(j\,+\,1\right)\,-\,a\,\left(n\,+\,1\right)\,|\,^{-\,s}\right)\,/\,\left(|\,a\,\left(j\,+\,1\right)\,-\,a\,\left(n\,+\,1\right)\,|\,-\,|\,a\,j\,-\,a\,n\,|\right)\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/InversePowerLineConductance.conductance` (`✓ std3`).

*Citation.* Alper Ferudun (2026). *Equilibria of Inverse-Square Repulsion on the Line Are Arithmetic Progressions*. DOI: [10.48550/arXiv.2610.06944](https://doi.org/10.48550/arXiv.2610.06944). URL: <https://arxiv.org/abs/2610.06944v1>.

*Commentary.*

Lemma 2.3 (p. 3): “For integers n ≠ j put D = |aⱼ − aₙ| and D′ = |aⱼ₊₁ − aₙ₊₁|, and let” c(n,j) = (D⁻ˢ − D′⁻ˢ)/(D′ − D) if D ≠ D′, and c(n,j) = sD⁻ˢ⁻¹ if D = D′. The formula expands D and D′ and sets the unused diagonal to zero.

**Theorem 1.5 (conductance symmetric).**

$$\forall\,\left(s\,:\,\mathbb{R}\right)\,,\,\forall\,\left(a\,:\,\mathbb{Z}\,\to\,\mathbb{R}\right)\,,\,\forall\,\left(n\,j\,:\,\mathbb{Z}\right)\,,\,\operatorname{conductance}\,s\,a\,n\,j\,=\,\operatorname{conductance}\,s\,a\,j\,n$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/InversePowerLineConductance.conductance_symmetric` (`✓ std3`). ∎

*Citation.* Alper Ferudun (2026). *Equilibria of Inverse-Square Repulsion on the Line Are Arithmetic Progressions*. DOI: [10.48550/arXiv.2610.06944](https://doi.org/10.48550/arXiv.2610.06944). URL: <https://arxiv.org/abs/2610.06944v1>.

*Commentary.*

The inverse-power conductance is unchanged when the two integer indices are exchanged.

**Theorem 1.6 (conductance positive).**

$$\forall\,\left(s\,:\,\mathbb{R}\right)\,,\,\left(0\,<\,s\right)\,\to\,\forall\,\left(a\,:\,\mathbb{Z}\,\to\,\mathbb{R}\right)\,,\,\left(\operatorname{StrictMono}\,a\right)\,\to\,\forall\,\left(n\,j\,:\,\mathbb{Z}\right)\,,\,\left(n\,\neq\,j\right)\,\to\,0\,<\,\operatorname{conductance}\,s\,a\,n\,j$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/InversePowerLineConductance.conductance_positive` (`✓ std3`). ∎

*Citation.* Alper Ferudun (2026). *Equilibria of Inverse-Square Repulsion on the Line Are Arithmetic Progressions*. DOI: [10.48550/arXiv.2610.06944](https://doi.org/10.48550/arXiv.2610.06944). URL: <https://arxiv.org/abs/2610.06944v1>.

*Commentary.*

At distinct indices of a strictly increasing sequence, the conductance is strictly positive when the exponent is positive.

**Theorem 1.7 (conductance distance bound).**

$$\forall\,\left(s\,:\,\mathbb{R}\right)\,,\,\left(0\,<\,s\right)\,\to\,\forall\,\left(a\,:\,\mathbb{Z}\,\to\,\mathbb{R}\right)\,,\,\left(\operatorname{StrictMono}\,a\right)\,\to\,\left(\forall\,n\,,\,\operatorname{fwdDiff}\,1\,a\,n\,\le\,2\,\cdot\,\operatorname{fwdDiff}\,1\,a\,\left(n\,+\,1\right)\right)\,\to\,\forall\,\left(n\,j\,:\,\mathbb{Z}\right)\,,\,\left(n\,\neq\,j\right)\,\to\,\operatorname{conductance}\,s\,a\,n\,j\,\le\,\left(s\,/\,\left(3\,:\,\mathbb{R}\right)\,^{-\,s\,-\,1}\right)\,\cdot\,|\,a\,j\,-\,a\,n\,|\,^{-\,s\,-\,1}$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/InversePowerLineConductance.conductance_distance_bound` (`✓ std3`). ∎

*Citation.* Alper Ferudun (2026). *Equilibria of Inverse-Square Repulsion on the Line Are Arithmetic Progressions*. DOI: [10.48550/arXiv.2610.06944](https://doi.org/10.48550/arXiv.2610.06944). URL: <https://arxiv.org/abs/2610.06944v1>.

*Commentary.*

The adjacent-gap comparison bounds the conductance by the displayed inverse power of the particle distance.

**Theorem 1.8 (conductance rows).**

$$\forall\,\left(s\,:\,\mathbb{R}\right)\,,\,\left(0\,<\,s\right)\,\to\,\forall\,\left(a\,:\,\mathbb{Z}\,\to\,\mathbb{R}\right)\,,\,\left(\operatorname{StrictMono}\,a\right)\,\to\,\left(\forall\,n\,,\,\operatorname{fwdDiff}\,1\,a\,n\,\le\,2\,\cdot\,\operatorname{fwdDiff}\,1\,a\,\left(n\,+\,1\right)\right)\,\to\,\left(\forall\,n\,,\,\operatorname{Summable}\,\left(\operatorname{fun}\,j\,:\,\mathbb{Z}\,\mapsto\,|\,a\,j\,-\,a\,n\,|\,^{-\,s}\right)\right)\,\to\,\forall\,n\,,\,\operatorname{Summable}\,\left(\operatorname{conductance}\,s\,a\,n\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/InversePowerLineConductance.conductance_rows` (`✓ std3`). ∎

*Citation.* Alper Ferudun (2026). *Equilibria of Inverse-Square Repulsion on the Line Are Arithmetic Progressions*. DOI: [10.48550/arXiv.2610.06944](https://doi.org/10.48550/arXiv.2610.06944). URL: <https://arxiv.org/abs/2610.06944v1>.

*Commentary.*

The distance bound and absolute force summability imply summable conductance rows.

**Theorem 1.9 (gaps harmonic).**

$$\forall\,\left(s\,:\,\mathbb{R}\right)\,,\,\forall\,\left(a\,:\,\mathbb{Z}\,\to\,\mathbb{R}\right)\,,\,\left(\operatorname{StrictMono}\,a\right)\,\to\,\left(\forall\,n\,,\,\operatorname{HasSum}\,\left(\operatorname{indexedForce}\,s\,a\,n\right)\,0\right)\,\to\,\left(\forall\,n\,,\,\operatorname{Summable}\,\left(\operatorname{conductance}\,s\,a\,n\right)\right)\,\to\,\left(\forall\,n\,,\,\operatorname{Summable}\,\left(\operatorname{fun}\,j\,\mapsto\,\operatorname{conductance}\,s\,a\,n\,j\,\cdot\,\operatorname{fwdDiff}\,1\,a\,j\right)\right)\,\land\,\left(\forall\,n\,,\,\left(\sum'_{j}\,\operatorname{conductance}\,s\,a\,n\,j\,\cdot\,\operatorname{fwdDiff}\,1\,a\,j\right)\,=\,\left(\sum'_{j}\,\operatorname{conductance}\,s\,a\,n\,j\right)\,\cdot\,\operatorname{fwdDiff}\,1\,a\,n\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/InversePowerLineConductance.gaps_harmonic` (`✓ std3`). ∎

*Citation.* Alper Ferudun (2026). *Equilibria of Inverse-Square Repulsion on the Line Are Arithmetic Progressions*. DOI: [10.48550/arXiv.2610.06944](https://doi.org/10.48550/arXiv.2610.06944). URL: <https://arxiv.org/abs/2610.06944v1>.

*Commentary.*

Subtracting consecutive zero-force identities makes consecutive gaps harmonic for the conductance, with summable weighted rows.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/InversePowerLineConductance.conductance`
- Truth anchor: `D5/S3/StatisticalMechanics/InversePowerLineConductance.conductance_distance_bound`
- Truth anchor: `D5/S3/StatisticalMechanics/InversePowerLineConductance.conductance_positive`
- Truth anchor: `D5/S3/StatisticalMechanics/InversePowerLineConductance.conductance_rows`
- Truth anchor: `D5/S3/StatisticalMechanics/InversePowerLineConductance.conductance_symmetric`
- Truth anchor: `D5/S3/StatisticalMechanics/InversePowerLineConductance.equilibrium_gap_ratio`
- Truth anchor: `D5/S3/StatisticalMechanics/InversePowerLineConductance.equilibrium_gap_reverse`
- Truth anchor: `D5/S3/StatisticalMechanics/InversePowerLineConductance.gaps_harmonic`
- Truth anchor: `D5/S3/StatisticalMechanics/InversePowerLineConductance.reciprocal_transform`
- Dependency: [D5/S3/StatisticalMechanics/InversePowerLineBasics](InversePowerLineBasics.md)
