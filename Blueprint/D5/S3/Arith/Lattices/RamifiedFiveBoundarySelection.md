# Ramified-Five Boundary Selection

## Abstract

The golden discriminant selects five as the unique ramified prime and lattice boundary modulus.

**Theorem 1.1 (The unique ramified prime is the canonical boundary modulus).**

$$\begin{aligned}(-1)^{2} - 4\times1\times(-1) = 5 \land\\{}\operatorname{cast}(5, GoldenInt) = (-1 + 2\varphi)^{2} \land\\{}(\forall p \in \mathbb{N}, \operatorname{Prime}(p) \Rightarrow (\operatorname{legendreSym}(5, p) = 0 \Leftrightarrow p = 5)) \land\\{}\forall x: \operatorname{Fin}(6) \to \mathbb{Z}, \operatorname{boundaryQuadratic}(\operatorname{boundaryProjection}(x)) = 2\cdot \operatorname{latticeEnergyModFive}(x), \operatorname{in} \operatorname{ZMod}(5).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/RamifiedFiveBoundarySelection.ramified_five_boundary_selection` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The first row computes the discriminant of the canonical golden polynomial from its integer coefficients. The second row exhibits five as the square of the ramifying golden integer in the canonical GoldenInt carrier.

For every rational prime, the quadratic character modulo five vanishes exactly at five. This gives the unique finite ramified location without restricting the prime carrier to a finite list or to odd primes.

The last row uses the source's canonical six-coordinate lattice, explicit three-dimensional boundary projection, boundary quadratic form, and integral Gram energy. It states the exact mod-five selection law on every integral lattice vector.

Repository search found the frozen golden discriminant, ramified-square, and energy-boundary laws, but no theorem combining them with uniqueness of the ramified prime. Pinned Mathlib supplies the Legendre zero criterion and modular divisibility bridge used for that uniqueness step.

## References

- Truth anchor: `D5/S3/Arith/Lattices/RamifiedFiveBoundarySelection.ramified_five_boundary_selection`
- Dependency: [D5/S0/Carrier/GoldenDiscriminant](../../../S0/Carrier/GoldenDiscriminant.md)
- Dependency: [D5/S3/Arith/Lattices/EnergyBoundarySelectionLaw](EnergyBoundarySelectionLaw.md)
- Dependency: [D5/S3/PrimeForms/GoldenPrimeClassification](../../PrimeForms/GoldenPrimeClassification.md)
