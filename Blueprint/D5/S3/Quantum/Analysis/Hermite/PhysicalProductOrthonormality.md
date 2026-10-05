# PhysicalProductOrthonormality

## Abstract

Actual physical product Hermite functions on Euclidean Lebesgue volume.

**Theorem 1.1 (All-index physical orthonormal pairing).**

$$\forall d \in \mathbb{N}, hbar \in \mathbb{R}, mass \in \operatorname{Fin}\left(d\right) \to \mathbb{R}, frequency \in \operatorname{Fin}\left(d\right) \to \mathbb{R},\; \left(0 < hbar \land \left(\left(\forall j \in \operatorname{Fin}\left(d\right),\; 0 < mass\left(j\right)\right) \land \left(\forall j \in \operatorname{Fin}\left(d\right),\; 0 < frequency\left(j\right)\right)\right)\right) \Rightarrow \left(\forall alpha \in \operatorname{Fin}\left(d\right) \to \mathbb{N}, beta \in \operatorname{Fin}\left(d\right) \to \mathbb{N},\; \int_{x: \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(d\right)\right)} \operatorname{physicalHermite}\left(d, hbar, mass, frequency, alpha\right)\left(x\right) \cdot \operatorname{physicalHermite}\left(d, hbar, mass, frequency, beta\right)\left(x\right) d\mathrm{ambientLebesgue} = \operatorname{if} alpha = beta \operatorname{then} 1 \operatorname{else} 0\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/Hermite/PhysicalProductOrthonormality.physical_product_orthonormal_integral` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors (2026). *Physical product Hermite orthonormal integrals*. URL: <https://github.com/TauCetiProject/TauCeti/tree/f749c1bb6b118c898f8d152e8ff9ad3d2b339dfd>.

*Commentary.*

For every natural dimension d, E is EuclideanSpace Real (Fin d). ambientLebesgue is exactly the canonical volume measure on E; every MemLp and integral uses that same measure. hbar is positive and mass(j), frequency(j) are positive at every coordinate. The empty dimension is included.

physicalHermite is the displayed finite product. hermite is the probabilists Hermite polynomial, aeval evaluates it in Real, ofReal embeds each real factor into Complex, and pi is Real.pi. The coordinate length is sqrt(hbar/(mass(j)*frequency(j))). All square roots are nonnegative real roots. Thus every physical mode is real-valued inside Complex; its conjugate equals itself.

Weighted integration by parts and the all-index lowering recursion prove the factorial Gaussian pairing. The sqrt(2) and positive-length Jacobians, normalization and finite-product integral transport give the actual Kronecker pairing. The displayed multiplication is equal to the usual conjugate-first-slot integral because the modes are real-valued.

The value is one when alpha equals beta and zero otherwise. For d=0 there is one empty multi-index, its mode is one and volume is the Dirac probability measure. PhysicalFormula gives the very same function as PhysicalProductTotality.physicalHermite, rather than a separately assumed orthonormal family.

$\forall d \in \mathbb{N}, hbar \in \mathbb{R}, mass \in \operatorname{Fin}\left(d\right) \to \mathbb{R}, frequency \in \operatorname{Fin}\left(d\right) \to \mathbb{R},\; \forall alpha \in \operatorname{Fin}\left(d\right) \to \mathbb{N}, x \in \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(d\right)\right),\; \operatorname{physicalHermite}\left(d, hbar, mass, frequency, alpha\right)\left(x\right): \mathbb{C} = \prod_{j: \operatorname{Fin}\left(d\right)}{\operatorname{ofReal}\left(\frac{\operatorname{aeval}\left(\operatorname{sqrt}\left(2\right) \cdot \frac{x\left(j\right)}{\operatorname{sqrt}\left(\frac{hbar}{mass\left(j\right) \cdot frequency\left(j\right)}\right)}, \operatorname{hermite}\left(alpha\left(j\right)\right)\right) \cdot \operatorname{exp}\left(-\frac{\frac{x\left(j\right)}{\operatorname{sqrt}\left(\frac{hbar}{mass\left(j\right) \cdot frequency\left(j\right)}\right)}^{2}}{2}\right)}{\operatorname{sqrt}\left(\operatorname{sqrt}\left(\frac{hbar}{mass\left(j\right) \cdot frequency\left(j\right)}\right)\right) \cdot \operatorname{sqrt}\left(\operatorname{factorial}\left(alpha\left(j\right)\right) \cdot \operatorname{sqrt}\left(\mathrm{pi}\right)\right)}\right)}$

The analytic construction follows the fixed Tau Ceti revision cited in the Library note. The physical normalization and Euclidean product-volume transport give the displayed integral for these functions.

The integral pairing alone does not establish differential oscillator eigenaction, all-Schwartz restriction, maximal weak or coefficient graph, a finite Hermite operator core, tensor/operator domains, adapted symplectic or metaplectic transport, Gibbs positive trace/factorization, or normal-state second-moment covariance and uncertainty.

## References

- Truth anchor: `D5/S3/Quantum/Analysis/Hermite/PhysicalProductOrthonormality.physical_product_orthonormal_integral`
- Dependency: [D5/S3/Quantum/Analysis/Hermite/PhysicalProductTotality](PhysicalProductTotality.md)
