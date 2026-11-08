# Inverse-power line: Basics

## Abstract

Inverse-power equilibrium rigidity on the real line.

**Definition 1.1 (IsSEquilibrium).**

$$\forall\,\left(s\,:\,\mathbb{R}\right)\,,\,\forall\,\left(X\,:\,\operatorname{Set}\,\mathbb{R}\right)\,,\,\left(\operatorname{IsSEquilibrium}\,s\,X\,\iff\,1\,<\,s\,\land\,X\,.\,\operatorname{Nontrivial}\,\land\,\left(\forall\,u\,v\,:\,\mathbb{R}\,,\,\left(\operatorname{Set}\,.\,\operatorname{inter}\,X\,\left(\operatorname{Set}\,.\,\operatorname{Icc}\,u\,v\right)\right)\,.\,\operatorname{Finite}\right)\,\land\,\left(\forall\,x\,:\,\mathbb{R}\,,\,x\,\in\,X\,\to\,\operatorname{Summable}\,\left(\operatorname{fun}\,y\,:\,\{y\,:\,\mathbb{R}\,//\,y\,\in\,X\,\land\,y\,\neq\,x\}\,\mapsto\,\operatorname{Real}\,.\,\operatorname{rpow}\,|\,\left(y\,:\,\mathbb{R}\right)\,-\,x\,|\,\left(-\,s\right)\right)\,\land\,\operatorname{HasSum}\,\left(\operatorname{fun}\,y\,:\,\{y\,:\,\mathbb{R}\,//\,y\,\in\,X\,\land\,y\,\neq\,x\}\,\mapsto\,\operatorname{Real}\,.\,\operatorname{sign}\,\left(\left(y\,:\,\mathbb{R}\right)\,-\,x\right)\,\cdot\,\operatorname{Real}\,.\,\operatorname{rpow}\,|\,\left(y\,:\,\mathbb{R}\right)\,-\,x\,|\,\left(-\,s\right)\right)\,0\right)\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/InversePowerLineBasics.IsSEquilibrium` (`✓ std3`).

*Citation.* Alper Ferudun (2026). *Equilibria of Inverse-Square Repulsion on the Line Are Arithmetic Progressions*. DOI: [10.48550/arXiv.2610.06944](https://doi.org/10.48550/arXiv.2610.06944). URL: <https://arxiv.org/abs/2610.06944v1>.

*Commentary.*

Definition 1.1 (p. 2): “Let s > 1. An s-equilibrium is a set X ⊂ ℝ with at least two points that is locally finite (every bounded interval contains only finitely many points of X) and satisfies, for every x ∈ X,” the finite-magnitude sum (1) and the zero signed sum (2). The formula states both sums explicitly, indexed by the subtype of points of X distinct from x. Summable and HasSum express unordered convergence.

**Definition 1.2 (arithmeticProgression).**

$$\forall\,\left(\alpha\,\beta\,:\,\mathbb{R}\right)\,,\,\left(\operatorname{arithmeticProgression}\,\alpha\,\beta\,=\,\operatorname{Set}\,.\,\operatorname{range}\,\left(\operatorname{fun}\,n\,:\,\mathbb{Z}\,\mapsto\,\alpha\,\cdot\,\left(n\,:\,\mathbb{R}\right)\,+\,\beta\right)\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/InversePowerLineBasics.arithmeticProgression` (`✓ std3`).

*Citation.* Alper Ferudun (2026). *Equilibria of Inverse-Square Repulsion on the Line Are Arithmetic Progressions*. DOI: [10.48550/arXiv.2610.06944](https://doi.org/10.48550/arXiv.2610.06944). URL: <https://arxiv.org/abs/2610.06944v1>.

*Commentary.*

Theorem 1.2 (p. 2): “Then X = {αn + β : n ∈ ℤ} for some α > 0 and β ∈ ℝ.” The set is the range over all integers; positivity is imposed by the theorems that use it.

**Theorem 1.3 (equilibrium enumeration).**

$$\forall\,\left(s\,:\,\mathbb{R}\right)\,,\,\forall\,\left(X\,:\,\operatorname{Set}\,\mathbb{R}\right)\,,\,\left(\operatorname{IsSEquilibrium}\,s\,X\right)\,\to\,\exists\,a\,:\,\mathbb{Z}\,\to\,\mathbb{R}\,,\,\operatorname{StrictMono}\,a\,\land\,\operatorname{Set}\,.\,\operatorname{range}\,a\,=\,X$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/InversePowerLineBasics.equilibrium_enumeration` (`✓ std3`). ∎

*Citation.* Alper Ferudun (2026). *Equilibria of Inverse-Square Repulsion on the Line Are Arithmetic Progressions*. DOI: [10.48550/arXiv.2610.06944](https://doi.org/10.48550/arXiv.2610.06944). URL: <https://arxiv.org/abs/2610.06944v1>.

*Commentary.*

Every equilibrium admits a strictly increasing enumeration indexed by all integers. Local finiteness and the exclusion of extremal particles give the two-sided discrete order.

**Definition 1.4 (indexedForce).**

$$\forall\,\left(s\,:\,\mathbb{R}\right)\,,\,\forall\,\left(a\,:\,\mathbb{Z}\,\to\,\mathbb{R}\right)\,,\,\forall\,\left(n\,j\,:\,\mathbb{Z}\right)\,,\,\left(\operatorname{indexedForce}\,s\,a\,n\,j\,=\,\operatorname{Real}\,.\,\operatorname{sign}\,\left(a\,j\,-\,a\,n\right)\,\cdot\,|\,a\,j\,-\,a\,n\,|\,^{-\,s}\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/InversePowerLineBasics.indexedForce` (`✓ std3`).

*Citation.* Alper Ferudun (2026). *Equilibria of Inverse-Square Repulsion on the Line Are Arithmetic Progressions*. DOI: [10.48550/arXiv.2610.06944](https://doi.org/10.48550/arXiv.2610.06944). URL: <https://arxiv.org/abs/2610.06944v1>.

*Commentary.*

The signed force at integer index n due to index j. Strictly increasing enumerations identify this expression with the force terms of Definition 1.1. The diagonal value is zero.

**Theorem 1.5 (equilibrium indexed force).**

$$\forall\,\left(s\,:\,\mathbb{R}\right)\,,\,\forall\,\left(X\,:\,\operatorname{Set}\,\mathbb{R}\right)\,,\,\left(\operatorname{IsSEquilibrium}\,s\,X\right)\,\to\,\forall\,\left(a\,:\,\mathbb{Z}\,\to\,\mathbb{R}\right)\,,\,\left(\operatorname{StrictMono}\,a\right)\,\to\,\left(\operatorname{Set}\,.\,\operatorname{range}\,a\,=\,X\right)\,\to\,\forall\,n\,:\,\mathbb{Z}\,,\,\operatorname{HasSum}\,\left(\operatorname{indexedForce}\,s\,a\,n\right)\,0$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/InversePowerLineBasics.equilibrium_indexed_force` (`✓ std3`). ∎

*Citation.* Alper Ferudun (2026). *Equilibria of Inverse-Square Repulsion on the Line Are Arithmetic Progressions*. DOI: [10.48550/arXiv.2610.06944](https://doi.org/10.48550/arXiv.2610.06944). URL: <https://arxiv.org/abs/2610.06944v1>.

*Commentary.*

Transport along the increasing enumeration preserves the zero signed force sum, with the diagonal term equal to zero.

**Theorem 1.6 (equilibrium indexed total).**

$$\forall\,\left(s\,:\,\mathbb{R}\right)\,,\,\forall\,\left(X\,:\,\operatorname{Set}\,\mathbb{R}\right)\,,\,\left(\operatorname{IsSEquilibrium}\,s\,X\right)\,\to\,\forall\,\left(a\,:\,\mathbb{Z}\,\to\,\mathbb{R}\right)\,,\,\left(\operatorname{StrictMono}\,a\right)\,\to\,\left(\operatorname{Set}\,.\,\operatorname{range}\,a\,=\,X\right)\,\to\,\forall\,n\,:\,\mathbb{Z}\,,\,\operatorname{Summable}\,\left(\operatorname{fun}\,j\,:\,\mathbb{Z}\,\mapsto\,|\,a\,j\,-\,a\,n\,|\,^{-\,s}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/InversePowerLineBasics.equilibrium_indexed_total` (`✓ std3`). ∎

*Citation.* Alper Ferudun (2026). *Equilibria of Inverse-Square Repulsion on the Line Are Arithmetic Progressions*. DOI: [10.48550/arXiv.2610.06944](https://doi.org/10.48550/arXiv.2610.06944). URL: <https://arxiv.org/abs/2610.06944v1>.

*Commentary.*

Transport along the increasing enumeration preserves absolute summability of the inverse-power forces, with the diagonal term equal to zero.

**Theorem 1.7 (constant gap affine).**

$$\forall\,\left(a\,:\,\mathbb{Z}\,\to\,\mathbb{R}\right)\,,\,\forall\,\left(\alpha\,:\,\mathbb{R}\right)\,,\,\left(\forall\,n\,:\,\mathbb{Z}\,,\,a\,\left(n\,+\,1\right)\,-\,a\,n\,=\,\alpha\right)\,\to\,\forall\,n\,:\,\mathbb{Z}\,,\,a\,n\,=\,\alpha\,\cdot\,\left(n\,:\,\mathbb{R}\right)\,+\,a\,0$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/InversePowerLineBasics.constant_gap_affine` (`✓ std3`). ∎

*Citation.* Alper Ferudun (2026). *Equilibria of Inverse-Square Repulsion on the Line Are Arithmetic Progressions*. DOI: [10.48550/arXiv.2610.06944](https://doi.org/10.48550/arXiv.2610.06944). URL: <https://arxiv.org/abs/2610.06944v1>.

*Commentary.*

A sequence with constant consecutive difference is affine on all integers.

**Theorem 1.8 (progression equilibrium).**

$$\forall\,\left(s\,\alpha\,\beta\,:\,\mathbb{R}\right)\,,\,\left(1\,<\,s\right)\,\to\,\left(0\,<\,\alpha\right)\,\to\,\operatorname{IsSEquilibrium}\,s\,\left(\operatorname{arithmeticProgression}\,\alpha\,\beta\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/InversePowerLineBasics.progression_equilibrium` (`✓ std3`). ∎

*Citation.* Alper Ferudun (2026). *Equilibria of Inverse-Square Repulsion on the Line Are Arithmetic Progressions*. DOI: [10.48550/arXiv.2610.06944](https://doi.org/10.48550/arXiv.2610.06944). URL: <https://arxiv.org/abs/2610.06944v1>.

*Commentary.*

Every affine integer progression with positive scale is an equilibrium for every real exponent greater than one.

**Theorem 1.9 (equilibrium exists).**

$$\forall\,\left(s\,:\,\mathbb{R}\right)\,,\,\left(1\,<\,s\right)\,\to\,\exists\,X\,:\,\operatorname{Set}\,\mathbb{R}\,,\,\operatorname{IsSEquilibrium}\,s\,X$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/InversePowerLineBasics.equilibrium_exists` (`✓ std3`). ∎

*Citation.* Alper Ferudun (2026). *Equilibria of Inverse-Square Repulsion on the Line Are Arithmetic Progressions*. DOI: [10.48550/arXiv.2610.06944](https://doi.org/10.48550/arXiv.2610.06944). URL: <https://arxiv.org/abs/2610.06944v1>.

*Commentary.*

For every real exponent greater than one, the integer lattice supplies an equilibrium.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/InversePowerLineBasics.IsSEquilibrium`
- Truth anchor: `D5/S3/StatisticalMechanics/InversePowerLineBasics.arithmeticProgression`
- Truth anchor: `D5/S3/StatisticalMechanics/InversePowerLineBasics.constant_gap_affine`
- Truth anchor: `D5/S3/StatisticalMechanics/InversePowerLineBasics.equilibrium_enumeration`
- Truth anchor: `D5/S3/StatisticalMechanics/InversePowerLineBasics.equilibrium_exists`
- Truth anchor: `D5/S3/StatisticalMechanics/InversePowerLineBasics.equilibrium_indexed_force`
- Truth anchor: `D5/S3/StatisticalMechanics/InversePowerLineBasics.equilibrium_indexed_total`
- Truth anchor: `D5/S3/StatisticalMechanics/InversePowerLineBasics.indexedForce`
- Truth anchor: `D5/S3/StatisticalMechanics/InversePowerLineBasics.progression_equilibrium`
