# Physical Hermite Differential Tests

## Abstract

Physical tensor Hermite functions are Schwartz eigenfunctions with compact graph approximants.

**Theorem 1.1 (Actual differential eigenaction and compact test limits).**

$$\forall d \in Nat, hbar \in \mathbb{R}, m \in \operatorname{Fin}\left(d\right) \to \mathbb{R}, omega \in \operatorname{Fin}\left(d\right) \to \mathbb{R}, alpha \in \operatorname{Fin}\left(d\right) \to Nat,\; \left(hbar > 0 \land \left(\left(\forall j \in \operatorname{Fin}\left(d\right),\; m\left(j\right) > 0\right) \land \left(\forall j \in \operatorname{Fin}\left(d\right),\; omega\left(j\right) > 0\right)\right)\right) \Rightarrow \left(\exists phi \in \operatorname{Schwartz}\left(\operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(d\right)\right), \mathbb{C}\right),\; \left(\forall x \in \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(d\right)\right),\; phi\left(x\right) = \operatorname{Phi}\left(d, hbar, m, omega, alpha, x\right)\right) \land \left(\operatorname{H0}\left(d, hbar, m, omega, phi\right) = \operatorname{E}\left(d, hbar, omega, alpha\right) \cdot phi \land \left(\exists psi \in Nat \to \operatorname{Schwartz}\left(\operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(d\right)\right), \mathbb{C}\right),\; \left(\forall N \in Nat,\; \operatorname{HasCompactSupport}\left(psi\left(N\right)\right)\right) \land \left(\operatorname{TendstoL2}\left(\left(\operatorname{J}\left(psi\left(N\right)\right)\right)_{N \in Nat}, \operatorname{J}\left(phi\right)\right) \land \operatorname{TendstoL2}\left(\left(\operatorname{J}\left(\operatorname{H0}\left(d, hbar, m, omega, psi\left(N\right)\right)\right)\right)_{N \in Nat}, \operatorname{E}\left(d, hbar, omega, alpha\right) \cdot \operatorname{J}\left(phi\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/PhysicalHermiteTests.physical_hermite_tests` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural dimension d, positive hbar, positive coordinate masses m and frequencies omega, and every multi-index alpha, the normalized physical tensor Hermite function Phi has a complex Schwartz realization phi on real Euclidean space. Set ell of j equal to the square root of hbar divided by m of j times omega of j. Phi is the product of the probabilists Hermite polynomial of alpha of j at square root of two times x of j divided by ell of j, times exp of minus x of j squared divided by twice ell of j squared, divided by the square root of square root of pi times ell of j times the factorial of alpha of j.

H0 is the actual sum of minus hbar squared divided by twice the mass times the second coordinate derivative, plus half the mass times frequency squared times the coordinate squared. H0 phi equals E times phi as Schwartz functions, where E is the sum of hbar times omega of j times alpha of j plus one half.

Compact smooth cutoffs psi of N converge to phi in actual complex Lebesgue L2. Their full H0 images simultaneously converge to E times phi. The coordinate Gaussian dilation and polynomial multiplier give the Schwartz function. Two actual coordinate derivatives and the Hermite differential equation give the eigenaction. The cutoff commutator and squared dominated convergence give the two L2 limits.

Dimension zero is included: the products are one and the energy and differential sums are zero. Orthonormality and totality are not hypotheses or conclusions here. The one-dimensional differentiation proof is adapted from Leonardo Pedro's Timepiece; its source and full license are identified in the Lean source.

## References

- Truth anchor: `D5/S3/Quantum/Analysis/PhysicalHermiteTests.physical_hermite_tests`
- Dependency: [D5/S3/Quantum/Analysis/GaussianSchwartz](GaussianSchwartz.md)
- Dependency: [D5/S3/Quantum/Analysis/SchwartzCutoffGraph](SchwartzCutoffGraph.md)
