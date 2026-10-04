# PhysicalProductTotality

## Abstract

Actual physical product Hermite functions on Euclidean Lebesgue volume.

**Definition 1.1 (The actual physical product function).**

$$\forall d \in \mathbb{N}, hbar \in \mathbb{R}, mass \in \operatorname{Fin}\left(d\right) \to \mathbb{R}, frequency \in \operatorname{Fin}\left(d\right) \to \mathbb{R},\; \forall alpha \in \operatorname{Fin}\left(d\right) \to \mathbb{N}, x \in \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(d\right)\right),\; \operatorname{physicalHermite}\left(d, hbar, mass, frequency, alpha\right)\left(x\right) = \prod_{j: \operatorname{Fin}\left(d\right)}{\operatorname{ofReal}\left(\frac{\operatorname{aeval}\left(\operatorname{sqrt}\left(2\right) \cdot \frac{x\left(j\right)}{\operatorname{sqrt}\left(\frac{hbar}{mass\left(j\right) \cdot frequency\left(j\right)}\right)}, \operatorname{hermite}\left(alpha\left(j\right)\right)\right) \cdot \operatorname{exp}\left(-\frac{\frac{x\left(j\right)}{\operatorname{sqrt}\left(\frac{hbar}{mass\left(j\right) \cdot frequency\left(j\right)}\right)}^{2}}{2}\right)}{\operatorname{sqrt}\left(\operatorname{sqrt}\left(\frac{hbar}{mass\left(j\right) \cdot frequency\left(j\right)}\right)\right) \cdot \operatorname{sqrt}\left(\operatorname{factorial}\left(alpha\left(j\right)\right) \cdot \operatorname{sqrt}\left(\mathrm{pi}\right)\right)}\right)}$$

*Formalization.* `D5/S3/Quantum/Analysis/Hermite/PhysicalProductTotality.physicalHermite` (`✓ std3`).

*Citation.* The Tau Ceti contributors; Rémy Degenne (2026). *Gaussian-polynomial totality through exponential-moment determinacy*. URL: <https://github.com/TauCetiProject/TauCeti/tree/f749c1bb6b118c898f8d152e8ff9ad3d2b339dfd>.

*Commentary.*

The equation gives the actual function for arbitrary real parameters. Positivity is required by the totality theorem below.

**Theorem 1.2 (Every positive-parameter physical test family is total).**

$$\forall d \in \mathbb{N}, hbar \in \mathbb{R}, mass \in \operatorname{Fin}\left(d\right) \to \mathbb{R}, frequency \in \operatorname{Fin}\left(d\right) \to \mathbb{R},\; \left(0 < hbar \land \left(\left(\forall j \in \operatorname{Fin}\left(d\right),\; 0 < mass\left(j\right)\right) \land \left(\forall j \in \operatorname{Fin}\left(d\right),\; 0 < frequency\left(j\right)\right)\right)\right) \Rightarrow \left(\left(\forall alpha \in \operatorname{Fin}\left(d\right) \to \mathbb{N},\; \operatorname{MemLp}\left(\operatorname{physicalHermite}\left(d, hbar, mass, frequency, alpha\right), 2, \mathrm{ambientLebesgue}\right)\right) \land \left(\forall g \in \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(d\right)\right) \to \mathbb{C},\; \operatorname{MemLp}\left(g, 2, \mathrm{ambientLebesgue}\right) \Rightarrow \left(\left(\forall alpha \in \operatorname{Fin}\left(d\right) \to \mathbb{N},\; \int_{x: \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(d\right)\right)} \operatorname{physicalHermite}\left(d, hbar, mass, frequency, alpha\right)\left(x\right) \cdot g\left(x\right) d\mathrm{ambientLebesgue} = 0\right) \Rightarrow g =_{\operatorname{ae}, \mathrm{ambientLebesgue}} 0\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/Hermite/PhysicalProductTotality.physical_product_totality` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors; Rémy Degenne (2026). *Gaussian-polynomial totality through exponential-moment determinacy*. URL: <https://github.com/TauCetiProject/TauCeti/tree/f749c1bb6b118c898f8d152e8ff9ad3d2b339dfd>.

*Commentary.*

For every natural dimension d, E is EuclideanSpace Real (Fin d). ambientLebesgue is exactly the canonical volume measure on E; every MemLp and integral uses that same measure. hbar is positive and mass(j), frequency(j) are positive at every coordinate. The empty dimension is included.

physicalHermite is the displayed finite product. hermite is the probabilists Hermite polynomial, aeval evaluates it in Real, ofReal embeds each real factor into Complex, and pi is Real.pi. The coordinate length is sqrt(hbar/(mass(j)*frequency(j))). All square roots are nonnegative real roots. Thus every physical mode is real-valued inside Complex; its conjugate equals itself.

Finite-coordinate slot continuity extends actual physical test pairings from dense coordinate spans. Rectangle indicators, local pi-lambda induction and a common sigma-finite exhaustion then separate every actual Lebesgue L2 representative. The coordinate Gaussian-polynomial theorem is the canonical prerequisite.

The analytic constructions are attributed necessary-content adaptations from the fixed Tau Ceti revision listed in the Library note. They carry no research originality claim. No retained coordinate map, abstract basis, isometry, surjectivity, normalization or zero-dimension companion theorem is introduced.

This unit does not establish differential oscillator eigenaction, all-Schwartz restriction, maximal weak or coefficient graph, a finite Hermite operator core, tensor/operator domains, adapted symplectic or metaplectic transport, Gibbs positive trace/factorization, or normal-state second-moment covariance and uncertainty.

## References

- Truth anchor: `D5/S3/Quantum/Analysis/Hermite/PhysicalProductTotality.physicalHermite`
- Truth anchor: `D5/S3/Quantum/Analysis/Hermite/PhysicalProductTotality.physical_product_totality`
- Dependency: [D5/S3/Quantum/Analysis/Hermite/GaussianPolynomialTotality](GaussianPolynomialTotality.md)
